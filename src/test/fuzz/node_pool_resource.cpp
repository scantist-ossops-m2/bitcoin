// Copyright (c) 2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <crypto/common.h>
#include <support/allocators/node_pool_resource.h>
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/util.h>

#include <cstdint>
#include <tuple>
#include <vector>

namespace {

template<typename TestResource>
class ResourceFuzzer
{
    TestResource m_test_resource;
    uint64_t m_sequence{0};
    size_t m_total_allocated;

    struct Entry
    {
        std::byte* ptr;
        size_t size;
        size_t alignment;
        uint64_t seed;

        Entry(std::byte* p, size_t s, size_t a, uint64_t se) : ptr(p), size(s), alignment(a), seed(se) {}
    };

    std::vector<Entry> m_entries;

public:
    template<typename... Args>
    ResourceFuzzer(Args&&... args) : m_test_resource(std::forward<Args>(args)...) {}

    void Create(size_t size, size_t alignment)
    {
        assert(size > 0); // Must allocate at least 1 byte.
        assert(alignment > 0); // Alignment must be at least 1.
        assert((alignment & (alignment - 1)) == 0); // Alignment must be power of 2.
        assert((size & (alignment - 1)) == 0); // Size must be a multiple of alignment.
        std::byte* ptr = static_cast<std::byte*>(m_test_resource.allocate(size, alignment));
        m_total_allocated += size;
        auto ptr_val = reinterpret_cast<std::uintptr_t>(ptr);
        assert((ptr_val & (alignment - 1)) == 0);
        uint64_t seed = m_sequence++;
        m_entries.emplace_back(ptr, size, alignment, seed);
        Xoroshiro128pp rng(seed);
        while (size >= 8) {
            WriteLE64((unsigned char*)ptr, rng());
            size -= 8;
            ptr += 8;
        }
        if (size > 0) {
            std::byte buf[8];
            WriteLE64((unsigned char*)buf, rng() >> (8 * (8 - size)));
            std::copy(buf, buf + size, ptr);
        }
    }

    void Create(FuzzedDataProvider& provider)
    {
        if (m_total_allocated > 0x1000000) return;
        size_t alignment_bits = provider.ConsumeIntegralInRange<size_t>(0, 7);
        size_t alignment = 1 << alignment_bits;
        size_t size_bits = provider.ConsumeIntegralInRange<size_t>(0, 16 - alignment_bits);
        size_t size = provider.ConsumeIntegralInRange<size_t>(1U << size_bits, (1U << (size_bits + 1)) - 1U) << alignment_bits;
        Create(size, alignment);
    }

    void DestroyLast()
    {
        if (m_entries.empty()) return;
        auto [ptr, size, alignment, seed] = m_entries.back();
        auto ptr_val = reinterpret_cast<std::uintptr_t>(ptr);
        assert((ptr_val & (alignment - 1)) == 0);
        auto old_ptr = ptr;
        auto old_size = size;
        m_entries.pop_back();
        Xoroshiro128pp rng(seed);
        while (size >= 8) {
            assert(ReadLE64((const unsigned char*)ptr) == rng());
            size -= 8;
            ptr += 8;
        }
        if (size > 0) {
            std::byte buf[8] = {};
            std::copy(ptr, ptr + size, buf);
            assert(ReadLE64((const unsigned char*)buf) == rng() >> (8 * (8 - size)));
        }
        m_total_allocated -= old_size;
        m_test_resource.deallocate(old_ptr, old_size, alignment);
    }

    void Destroy(FuzzedDataProvider& provider)
    {
        if (m_entries.empty()) return;
        size_t idx = m_entries.size() - 1 - provider.ConsumeIntegralInRange<size_t>(0, m_entries.size() - 1);
        if (idx != m_entries.size() - 1) {
            std::swap(m_entries[idx], m_entries.back());
        }
        DestroyLast();
    }

    void Clear()
    {
        while (!m_entries.empty()) DestroyLast();
    }

    void Fuzz(FuzzedDataProvider& provider)
    {
        LIMITED_WHILE(provider.ConsumeBool(), 10000) {
            CallOneOf(
                provider,
                [&] { Create(provider); },
                [&] { Destroy(provider); }
            );
        }
        Clear();
    }
}; // class ResourceFuzzer

} // namespace

FUZZ_TARGET(node_pool_resource_ptr)
{
    FuzzedDataProvider provider(buffer.data(), buffer.size());
    ResourceFuzzer<NodePoolResource<256, 262144, alignof(void*)>> fuzzer;
    fuzzer.Fuzz(provider);
}

FUZZ_TARGET(node_pool_resource_max)
{
    FuzzedDataProvider provider(buffer.data(), buffer.size());
    ResourceFuzzer<NodePoolResource<256, 262144, alignof(max_align_t)>> fuzzer;
    fuzzer.Fuzz(provider);
}

FUZZ_TARGET(node_pool_resource_huge)
{
    FuzzedDataProvider provider(buffer.data(), buffer.size());
    ResourceFuzzer<NodePoolResource<256, 262144, 64>> fuzzer;
    fuzzer.Fuzz(provider);
}
