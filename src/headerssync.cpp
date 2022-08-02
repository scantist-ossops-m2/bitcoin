#include <headerssync.h>
#include <logging.h>
#include <pow.h>
#include <timedata.h>
#include <util/check.h>

// The two constants below are computed using the simulation script on
// https://gist.github.com/sipa/016ae445c132cdf65a2791534dfb7ae1

//! Store a commitment to a header every HEADER_COMMITMENT_FREQUENCY blocks.
constexpr size_t HEADER_COMMITMENT_FREQUENCY{575};

//! Only feed headers to validation once this many headers on top have been
//! received and validated against commitments.
constexpr size_t REDOWNLOAD_BUFFER_SIZE{14216};

// Our memory analysis assumes 48 bytes for a CompressedHeader (so we should
// re-calculate parameters if we compress further)
static_assert(sizeof(CompressedHeader) == 48);

HeadersSyncState::HeadersSyncState(NodeId id, const Consensus::Params& consensus_params) :
    m_id(id), m_consensus_params(consensus_params)
{ }

/** Free any memory in use, and mark this object as no longer usable. This is
 * required to guarantee that we won't reuse this object with the same
 * SaltedTxidHasher for another sync. */
void HeadersSyncState::Finalize()
{
    Assume(m_download_state != State::FINAL);
    m_header_commitments.clear();
    m_last_header_received.SetNull();
    std::deque<CompressedHeader>().swap(m_redownloaded_headers);
    m_redownload_buffer_last_hash.SetNull();
    m_redownload_buffer_first_prev_hash.SetNull();
    m_process_all_remaining_headers = false;
    m_current_height = 0;
    std::vector<uint256>().swap(m_chain_start_locator.vHave);

    m_download_state = State::FINAL;
}

/** Initialize the parameters for this headers download, validate this first
 * batch, and request more headers. */
std::optional<CBlockLocator> HeadersSyncState::StartInitialDownload(const CBlockIndex* chain_start,
        const std::vector<CBlockHeader>& initial_headers, const arith_uint256&
        minimum_required_work)
{
    // A new instance of this object should be instantiated for every headers
    // sync, so that we don't reuse our salted hasher between syncs.
    assert(m_download_state == State::UNSTARTED);
    m_download_state = State::INITIAL_DOWNLOAD;

    m_chain_start = chain_start;
    m_minimum_required_work = minimum_required_work;
    m_current_chain_work = chain_start->nChainWork;
    m_current_height = chain_start->nHeight;
    m_chain_start_locator = chain_start->GetLocator();

    m_last_header_received = m_chain_start->GetBlockHeader();

    // Estimate the number of blocks that could possibly exist on the peer's
    // chain *right now* using 6 blocks/second (fastest blockrate given the MTP
    // rule) times the number of seconds from the last allowed block until
    // today. This serves as a memory bound on how many commitments we might
    // store from this peer, and we can safely give up syncing if the peer
    // exceeds this bound, because it's not possible for a consensus-valid
    // chain to be longer than this (at the current time -- in the future we
    // could try again, if necessary, to sync a longer chain).
    m_max_commitments = 6*(GetAdjustedTime() - chain_start->GetMedianTimePast() + MAX_FUTURE_BLOCK_TIME) / HEADER_COMMITMENT_FREQUENCY;

    if (!ValidateAndStoreHeadersCommitments(initial_headers)) {
        return std::nullopt;
    }
    return MakeNextHeadersRequest();
}

/** Process the next batch of headers received from our peer.
 *  Validate and store commitments, and compare total chainwork to our target to
 *  see if we can switch to REDOWNLOAD mode.  */
HeadersSyncState::ProcessingResult HeadersSyncState::ProcessNextHeaders(const
        std::vector<CBlockHeader>& headers, const bool full_headers_message)
{
    ProcessingResult ret;

    Assume(!headers.empty());
    if (headers.empty()) return ret;

    Assume(m_download_state != State::FINAL);
    if (m_download_state == State::FINAL) return ret;

    if (m_download_state == State::INITIAL_DOWNLOAD) {
        // During INITIAL_DOWNLOAD, we minimally validate block headers and
        // occasionally add commitments to them, until we reach our work
        // threshold.
        if (!ValidateAndStoreHeadersCommitments(headers)) {
            // The headers didn't pass validation; give up on the sync.
            return ret;
        }
        ret.success = true;
        if (full_headers_message || m_download_state == State::REDOWNLOAD) {
            // A full headers message means the peer may have more to give us;
            // also if we just switched to REDOWNLOAD then we need to re-request
            // headers from the beginning.
            ret.locator = MakeNextHeadersRequest();
            return ret;
        } else {
            // If we're in INITIAL_DOWNLOAD and we get a non-full headers
            // message, then the peer's chain has ended and definitely doesn't
            // have enough work, so we can stop our sync.
            LogPrint(BCLog::NET, "Ignoring low-work chain (height=%u) from peer=%d\n", m_current_height, m_id);
            Finalize();
            return ret;
        }
    } else if (m_download_state == State::REDOWNLOAD) {
        // During REDOWNLOAD, we compare our stored commitments to what we
        // receive, and add headers to our redownload buffer. When the buffer
        // gets big enough (meaning that we've checked enough commitments),
        // we'll return a batch of headers to the caller for processing.
        for (const auto& hdr : headers) {
            if (!ValidateAndStoreRedownloadedHeader(hdr)) {
                // Something went wrong -- the peer gave us an unexpected chain.
                // We could consider looking at the reason for failure and
                // punishing the peer, but for now just give up on sync.
                Finalize();
                return ret;
            }
        }

        ret.success = true;
        // Return any headers that are ready for acceptance.
        ret.headers_to_process = RemoveHeadersReadyForAcceptance();

        // If we hit our target blockhash, then all remaining headers will be
        // returned and we can clear any leftover internal state.
        if (m_redownloaded_headers.empty() && m_process_all_remaining_headers) {
            Finalize();
            return ret;
        }

        // If the headers message is full, we need to request more.
        if (full_headers_message) {
            ret.locator = MakeNextHeadersRequest();
            return ret;
        } else {
            // For some reason our peer gave us a high-work chain, but is now
            // declining to serve us that full chain again. Give up.
            // Note that there's no more processing to be done with these
            // headers, so we can still return success.
            Finalize();
            return ret;
        }
    }
    return ret;
}

bool HeadersSyncState::ValidateAndStoreHeadersCommitments(const std::vector<CBlockHeader>& headers)
{
    // The caller should not give us an empty set of headers.
    Assume(headers.size() > 0);
    if (headers.size() == 0) return true;

    Assume(m_download_state != State::FINAL);
    if (m_download_state == State::FINAL) return false;

    if (headers[0].hashPrevBlock != m_last_header_received.GetHash()) {
        // Somehow our peer gave us a header that doesn't connect.
        // This might be benign -- perhaps we issued an extra getheaders
        // message, such as after a block INV was received.
        // Or it could be that our peer is broken or malicious. If broken,
        // sending a new getheaders immediately could trigger an infinite
        // loop. Just give up for now; if our peer ever gives us an block
        // INV later we will fetch headers then, and likely retrigger this
        // logic.
        Finalize();
        return false;
    }

    // If it does connect, (minimally) validate and store a commitment to each one.
    for (const auto& hdr : headers) {
        if (!ValidateAndProcessSingleHeader(m_last_header_received, hdr, m_current_height+1)) {
            Finalize();
            return false;
        }
    }

    if (m_current_chain_work >= m_minimum_required_work) {
        m_redownloaded_headers.clear();
        m_redownload_buffer_last_height = m_chain_start->nHeight;
        m_redownload_buffer_first_prev_hash = m_chain_start->GetBlockHash();
        m_redownload_buffer_last_hash = m_chain_start->GetBlockHash();
        m_redownload_chain_work = m_chain_start->nChainWork;
        m_download_state = State::REDOWNLOAD;
    }
    return true;
}

bool HeadersSyncState::ValidateAndProcessSingleHeader(const CBlockHeader& previous, const CBlockHeader& current, int64_t current_height)
{
    Assume(m_download_state != State::FINAL);
    if (m_download_state == State::FINAL) return false;

    // Verify that the difficulty isn't growing too fast; an adversary with
    // limited hashing capability has a greater chance of producing a high
    // work chain if they compress the work into as few blocks as possible,
    // so don't let anyone give a chain that would violate the difficulty
    // adjustment maximum.
    if (!PermittedDifficultyTransition(m_consensus_params, current_height,
                previous.nBits, current.nBits)) {
        return false;
    }

    if (!CheckProofOfWork(current.GetHash(), current.nBits, m_consensus_params)) return false;

    if ((current_height - m_chain_start->nHeight) % HEADER_COMMITMENT_FREQUENCY == 0) {
        // Add a commitment.
        m_header_commitments.push_back(m_hasher(current.GetHash()) & 1);
        if (m_header_commitments.size() > m_max_commitments) {
            // The peer's chain is too long; give up.
            // It's possible the chain grew since we started the sync; so
            // potentially we could succeed in syncing the peer's chain if we
            // try again later.
            LogPrint(BCLog::NET, "headers chain is too long; giving up sync peer=%d\n", m_id);
            return false;
        }
    }

    m_current_chain_work += GetBlockProof(CBlockIndex(current));
    m_last_header_received = current;
    ++m_current_height;

    return true;
}

bool HeadersSyncState::ValidateAndStoreRedownloadedHeader(const CBlockHeader& header)
{
    Assume(m_download_state != State::FINAL);
    if (m_download_state == State::FINAL) return false;

    // Ensure that we're working on a header that connects to the chain we're
    // downloading.
    if (header.hashPrevBlock != m_redownload_buffer_last_hash) {
        return false;
    }

    int64_t next_height = m_redownload_buffer_last_height + 1;

    // Check that the difficulty adjustments are within our tolerance:
    uint32_t previous_nBits{0};
    if (!m_redownloaded_headers.empty()) {
        previous_nBits = m_redownloaded_headers.back().nBits;
    } else {
        previous_nBits = m_chain_start->nBits;
    }

    if (!PermittedDifficultyTransition(m_consensus_params, next_height,
                previous_nBits, header.nBits)) {
        return false;
    }

    // Track work on the redownloaded chain
    m_redownload_chain_work += GetBlockProof(CBlockIndex(header));

    if (m_redownload_chain_work >= m_minimum_required_work) {
        m_process_all_remaining_headers = true;
    }

    // If we're at a header for which we previously stored a commitment, verify
    // it is correct. Failure will result in aborting download.
    // Also, don't check commitments once we've gotten to our target blockhash;
    // it's possible our peer has extended its chain between our first sync and
    // our second, and we don't want to return failure after we've seen our
    // target blockhash just because we ran out of commitments.
    if (!m_process_all_remaining_headers && (next_height - m_chain_start->nHeight) % HEADER_COMMITMENT_FREQUENCY == 0) {
         bool commitment = m_hasher(header.GetHash()) & 1;
         if (m_header_commitments.size() == 0) {
            // Somehow our peer managed to feed us a different chain and
            // we've run out of commitments.
            return false;
        }
        bool expected_commitment = m_header_commitments.front();
        m_header_commitments.pop_front();
        if (commitment != expected_commitment) {
            return false;
        }
    }

    // Store this header for later processing.
    m_redownloaded_headers.push_back(header);
    m_redownload_buffer_last_height = next_height;
    m_redownload_buffer_last_hash = header.GetHash();

    return true;
}

std::vector<CBlockHeader> HeadersSyncState::RemoveHeadersReadyForAcceptance()
{
    std::vector<CBlockHeader> ret;

    Assume(m_download_state != State::FINAL);
    if (m_download_state == State::FINAL) return ret;

    while (m_redownloaded_headers.size() > REDOWNLOAD_BUFFER_SIZE ||
            (m_redownloaded_headers.size() > 0 && m_process_all_remaining_headers)) {
        ret.emplace_back(m_redownloaded_headers.front().GetFullHeader(m_redownload_buffer_first_prev_hash));
        m_redownloaded_headers.pop_front();
        m_redownload_buffer_first_prev_hash = ret.back().GetHash();
    }
    return ret;
}

std::optional<CBlockLocator> HeadersSyncState::MakeNextHeadersRequest()
{
    Assume(m_download_state != State::FINAL);
    if (m_download_state == State::FINAL) return std::nullopt;

    std::vector<uint256> locator;

    if (m_download_state == State::INITIAL_DOWNLOAD && !m_last_header_received.IsNull()) {
        // During initial download, we continue from the last header received.
        locator.push_back(m_last_header_received.GetHash());
    }

    if (m_download_state == State::REDOWNLOAD && !m_redownloaded_headers.empty()) {
        // During redownload, we will either download from the last received
        // header that we stored during the second download phase, or from the
        // fork point (m_chain_start).
        locator.push_back(m_redownload_buffer_last_hash);
    }

    locator.insert(locator.end(), m_chain_start_locator.vHave.begin(),
            m_chain_start_locator.vHave.end());
    return CBlockLocator(std::move(locator));
}
