// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <node/coinstats.h>

#include <coins.h>
#include <crypto/muhash.h>
#include <hash.h>
#include <serialize.h>
#include <uint256.h>
#include <util/system.h>
#include <validation.h>

#include <map>

static void ApplyStats(CCoinsStats &stats, MuHash3072& muhash, const uint256& hash, const std::map<uint32_t, Coin>& outputs)
{
    assert(!outputs.empty());
    stats.nTransactions++;
    for (const auto& output : outputs) {
        COutPoint outpoint = COutPoint(hash, output.first);
        Coin coin = output.second;

        TruncatedSHA512Writer ss(SER_DISK, 0);
        ss << outpoint;
        ss << (uint32_t)(coin.nHeight * 2 + coin.fCoinBase);
        ss << coin.out;
        muhash *= MuHash3072(ss.GetHash().begin());

        stats.nTransactionOutputs++;
        stats.nTotalAmount += output.second.out.nValue;
        stats.nBogoSize += 32 /* txid */ + 4 /* vout index */ + 4 /* height + coinbase */ + 8 /* amount */ +
                           2 /* scriptPubKey len */ + output.second.out.scriptPubKey.size() /* scriptPubKey */;
    }
}

//! Calculate statistics about the unspent transaction output set
bool GetUTXOStats(CCoinsView *view, CCoinsStats &stats)
{
    stats = CCoinsStats();
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    assert(pcursor);

    MuHash3072 muhash;
    stats.hashBlock = pcursor->GetBestBlock();
    {
        LOCK(cs_main);
        stats.nHeight = LookupBlockIndex(stats.hashBlock)->nHeight;
    }
    uint256 prevkey;
    std::map<uint32_t, Coin> outputs;
    while (pcursor->Valid()) {
        COutPoint key;
        Coin coin;
        if (pcursor->GetKey(key) && pcursor->GetValue(coin)) {
            if (!outputs.empty() && key.hash != prevkey) {
                ApplyStats(stats, muhash, prevkey, outputs);
                outputs.clear();
            }
            prevkey = key.hash;
            outputs[key.n] = std::move(coin);
            stats.coins_count++;
        } else {
            return error("%s: unable to read value", __func__);
        }
        pcursor->Next();
    }
    if (!outputs.empty()) {
        ApplyStats(stats, muhash, prevkey, outputs);
    }

    unsigned char out[384];
    muhash.Finalize(out);
    stats.hashSerialized = (TruncatedSHA512Writer(SER_DISK, 0) << out).GetHash();

    stats.nDiskSize = view->EstimateSize();
    return true;
}
