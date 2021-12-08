// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <core_io.h>
#include <hash.h>
#include <key.h>
#include <script/miniscript.h>
#include <script/script.h>
#include <span.h>
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/util.h>
#include <util/strencodings.h>

#include <optional>


struct Satisfier: BaseSignatureChecker {
    typedef CPubKey Key;

    // Precomputed public keys, and a dummy signature for each of them.
    std::vector<Key> dummy_keys;
    std::map<CKeyID, Key> dummy_keys_map;
    std::map<Key, std::vector<unsigned char>> dummy_sigs;

    // Precomputed hashes of each kind.
    std::vector<std::vector<unsigned char>> sha256;
    std::vector<std::vector<unsigned char>> ripemd160;
    std::vector<std::vector<unsigned char>> hash256;
    std::vector<std::vector<unsigned char>> hash160;
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> sha256_preimages;
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> ripemd160_preimages;
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> hash256_preimages;
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> hash160_preimages;

    //! Set the precomputed data.
    void Init() {
        unsigned char keydata[32] = {1};
        for (unsigned char i = 1; i <= 50; i++) {
            keydata[31] = i;
            CKey privkey;
            privkey.Set(keydata, keydata + 32, true);
            const Key pubkey = privkey.GetPubKey();

            dummy_keys.push_back(pubkey);
            dummy_keys_map.insert({pubkey.GetID(), pubkey});
            std::vector<unsigned char> sig;
            privkey.Sign(uint256S(""), sig);
            sig.push_back(1); // SIGHASH_ALL
            dummy_sigs.insert({pubkey, sig});

            std::vector<unsigned char> hash;
            hash.resize(32);
            CSHA256().Write(keydata, 32).Finalize(hash.data());
            sha256.push_back(hash);
            sha256_preimages[hash] = std::vector<unsigned char>(keydata, keydata + 32);
            CHash256().Write(keydata).Finalize(hash);
            hash256.push_back(hash);
            hash256_preimages[hash] = std::vector<unsigned char>(keydata, keydata + 32);
            hash.resize(20);
            CRIPEMD160().Write(keydata, 32).Finalize(hash.data());
            ripemd160.push_back(hash);
            ripemd160_preimages[hash] = std::vector<unsigned char>(keydata, keydata + 32);
            CHash160().Write(keydata).Finalize(hash);
            hash160.push_back(hash);
            hash160_preimages[hash] = std::vector<unsigned char>(keydata, keydata + 32);
        }
    }

    // Conversion routines
    bool ToString(const Key& key, std::string& ret) const { ret = HexStr(key); return true; }
    const std::vector<unsigned char> ToPKBytes(const Key& key) const { return {key.begin(), key.end()}; }
    const std::vector<unsigned char> ToPKHBytes(const Key& key) const {
        const auto h = Hash160(key);
        return {h.begin(), h.end()};
    }
    template<typename I>
    bool FromString(I first, I last, Key& key) const {
        const auto bytes = ParseHex(std::string(first, last));
        key.Set(bytes.begin(), bytes.end());
        return key.IsValid();
    }
    template<typename I>
    bool FromPKBytes(I first, I last, CPubKey& key) const {
        key.Set(first, last);
        return key.IsValid();
    }
    template<typename I>
    bool FromPKHBytes(I first, I last, CPubKey& key) const {
        assert(last - first == 20);
        CKeyID keyid;
        std::copy(first, last, keyid.begin());
        const auto it = dummy_keys_map.find(keyid);
        if (it == dummy_keys_map.end()) return false;
        key = it->second;
        return true;
    }

    // Timelock challenges satisfaction. Make the value (deterministically) vary to explore different
    // paths.
    bool CheckAfter(uint32_t value) const { return value % 2; }
    bool CheckOlder(uint32_t value) const { return value % 2; }

    // Signature challenges fulfilled with a dummy signate, if it was one of our dummy keys.
    miniscript::Availability Sign(const CPubKey& key, std::vector<unsigned char>& sig) const {
        const auto it = dummy_sigs.find(key);
        if (it == dummy_sigs.end()) return miniscript::Availability::NO;
        sig = it->second;
        return miniscript::Availability::YES;
    }

    //! Lookup generalization for all the hash satisfactions below
    miniscript::Availability LookupHash(const std::vector<unsigned char>& hash, std::vector<unsigned char>& preimage,
                                        const std::map<std::vector<unsigned char>, std::vector<unsigned char>>& map) const
    {
        const auto it = map.find(hash);
        if (it == map.end()) return miniscript::Availability::NO;
        preimage = it->second;
        return miniscript::Availability::YES;
    }
    miniscript::Availability SatSHA256(const std::vector<unsigned char>& hash, std::vector<unsigned char>& preimage) const {
        return LookupHash(hash, preimage, sha256_preimages);
    }
    miniscript::Availability SatRIPEMD160(const std::vector<unsigned char>& hash, std::vector<unsigned char>& preimage) const {
        return LookupHash(hash, preimage, ripemd160_preimages);
    }
    miniscript::Availability SatHASH256(const std::vector<unsigned char>& hash, std::vector<unsigned char>& preimage) const {
        return LookupHash(hash, preimage, hash256_preimages);
    }
    miniscript::Availability SatHASH160(const std::vector<unsigned char>& hash, std::vector<unsigned char>& preimage) const {
        return LookupHash(hash, preimage, hash160_preimages);
    }

    // Signature checker methods. Checks the right dummy signature is used. Always assumes timelocks are
    // correct.
    bool CheckECDSASignature(const std::vector<unsigned char>& sig, const std::vector<unsigned char>& vchPubKey,
                             const CScript& scriptCode, SigVersion sigversion) const override
    {
        const CPubKey key{vchPubKey};
        const auto it = dummy_sigs.find(key);
        if (it == dummy_sigs.end()) return false;
        return it->second == sig;
    }
    bool CheckLockTime(const CScriptNum& nLockTime) const override { return true; }
    bool CheckSequence(const CScriptNum& nSequence) const override { return true; }

};

Satisfier SATISFIER;
// A dummy scriptsig to pass to VerifyScript (we always use Segwit v0).
const CScript DUMMY_SCRIPTSIG;

void initialize_miniscript_decode() {
    ECC_Start();
    SATISFIER.Init();
}

FUZZ_TARGET_INIT(miniscript_decode, initialize_miniscript_decode)
{
    FuzzedDataProvider fuzzed_data_provider(buffer.data(), buffer.size());
    const std::optional<CScript> script = ConsumeDeserializable<CScript>(fuzzed_data_provider);
    if (!script) return;

    const auto ms = miniscript::FromScript(*script, SATISFIER);
    if (!ms) return;

    // We can roundtrip it to its string representation.
    std::string ms_str;
    assert(ms->ToString(SATISFIER, ms_str));
    assert(*miniscript::FromScript(*script, SATISFIER) == *ms);
    // The Script representation must roundtrip since we parsed it this way the first time.
    const CScript ms_script = ms->ToScript(SATISFIER);
    assert(ms_script == *script);

    // Check both malleable and non-malleable satisfaction. Note that we only assert the produced witness
    // is valid if the Miniscript was sane, as otherwise it could overflow the limits.
    CScriptWitness witness;
    const CScript script_pubkey = CScript() << OP_0 << WitnessV0ScriptHash(*script);
    const bool mal_success = ms->Satisfy(SATISFIER, witness.stack, false) == miniscript::Availability::YES;
    if (mal_success && ms->IsSaneTopLevel()) {
        witness.stack.push_back(std::vector<unsigned char>(script->begin(), script->end()));
        assert(VerifyScript(DUMMY_SCRIPTSIG, script_pubkey, &witness, STANDARD_SCRIPT_VERIFY_FLAGS, SATISFIER));
    }
    witness.stack.clear();
    const bool nonmal_success = ms->Satisfy(SATISFIER, witness.stack, true) == miniscript::Availability::YES;
    if (nonmal_success && ms->IsSaneTopLevel()) {
        witness.stack.push_back(std::vector<unsigned char>(script->begin(), script->end()));
        assert(VerifyScript(DUMMY_SCRIPTSIG, script_pubkey, &witness, STANDARD_SCRIPT_VERIFY_FLAGS, SATISFIER));
    }
    // If a nonmalleable solution exists, a solution whatsoever must also exist.
    assert(mal_success >= nonmal_success);
    // If a miniscript is nonmalleable and needs a signature, and a solution exists, a non-malleable solution must also exist.
    if (ms->IsNonMalleable() && ms->NeedsSignature()) assert(nonmal_success == mal_success);

}
