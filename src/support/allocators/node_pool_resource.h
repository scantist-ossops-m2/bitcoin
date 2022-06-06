#include <cstdint>
#include <cstddef>
#include <memory>
#include <memory_resource>
#include <utility>
#include <array>
#include <list>

template <std::size_t MAX_BLOCK_SIZE_BYTES, std::size_t CHUNK_SIZE_BYTES, std::size_t ALIGN_BYTES>
class NodePoolResource final : public std::pmr::memory_resource
{
    static_assert(ALIGN_BYTES > 0, "ALIGN_BYTES must be nonzero");
    static_assert((ALIGN_BYTES & (ALIGN_BYTES - 1)) == 0, "ALIGN_BYTES must be a power of two");

    /**
     * In-place linked list of the allocations, used for the free list.
     */
    struct FreeList {
        FreeList* next = nullptr;
    };

    /**
     * Internal alignment value. The larger of the requested ALIGN_BYTES and alignof(FreeList).
     */
    static constexpr std::size_t ELEM_SIZE_ALIGN = std::max(alignof(FreeList), ALIGN_BYTES);

    // Verify that units of size ELEM_SIZE_ALIGN can store a FreeList.
    static_assert(sizeof(FreeList) <= ELEM_SIZE_ALIGN, "FreeList must fit in alignment");

    // Verify the MAX_BLOCK_SIZE_BYTES is a multiple of the alignment.
    static_assert((MAX_BLOCK_SIZE_BYTES & (ELEM_SIZE_ALIGN - 1)) == 0);

    /**
     * Round up bytes to be at least a multiple of ELEM_SIZE_ALIGN.
     */
    constexpr std::size_t round_size(std::size_t bytes) noexcept
    {
        return (bytes + ELEM_SIZE_ALIGN - 1) & ~size_t{ELEM_SIZE_ALIGN - 1};
    }

    /**
     * Contains all allocated pools of memory, used to free the data in the destructor.
     */
    std::list<std::byte*> m_allocated_chunks{};

    /**
     * Single linked lists of all data that came from deallocating.
     */
    std::array<FreeList*, MAX_BLOCK_SIZE_BYTES / ELEM_SIZE_ALIGN> m_pools{};

    /**
     * Points to the beginning of available memory for carving out allocations.
     */
    std::byte* m_available_memory_it;

    /**
     * Points to the end of available memory for carving out allocations.
     *
     * That member variable is redundant, and is always equal to `m_allocated_chunks.back().get() + CHUNK_SIZE_BYTES`
     * whenever it is accessed, but `m_available_memory_end` caches this for clarity and efficiency.
     */
    std::byte* m_available_memory_end;

    /**
     * Fallback allocator when pool is not used.
     */
    std::pmr::memory_resource* const m_upstream_resource = std::pmr::get_default_resource();

    void allocate_chunk()
    {
        void* storage = m_upstream_resource->allocate(CHUNK_SIZE_BYTES, ELEM_SIZE_ALIGN);
        m_allocated_chunks.emplace_back(new (storage) std::byte[CHUNK_SIZE_BYTES]);
        m_available_memory_it = m_allocated_chunks.back();
        m_available_memory_end = m_available_memory_it + CHUNK_SIZE_BYTES;
    }


    void* do_allocate(std::size_t bytes, std::size_t alignment) override
    {
        if (alignment <= ELEM_SIZE_ALIGN) {
            const std::size_t round_bytes = round_size(bytes);
            if (round_bytes <= MAX_BLOCK_SIZE_BYTES) {
                std::size_t idx = (round_bytes / ELEM_SIZE_ALIGN) - 1;
                if (nullptr != m_pools[idx]) {
                    return std::exchange(m_pools[idx], m_pools[idx]->next);
                }
                if (std::size_t(m_available_memory_end - m_available_memory_it) < round_bytes) {
                    allocate_chunk();
                }
                return std::exchange(m_available_memory_it, m_available_memory_it + round_bytes);
            }
        }
        return m_upstream_resource->allocate(bytes, alignment);
    }

    void do_deallocate(void* p, std::size_t bytes, std::size_t alignment) noexcept override
    {
        if (alignment <= ELEM_SIZE_ALIGN) {
            const std::size_t round_bytes = round_size(bytes);
            if (round_bytes <= MAX_BLOCK_SIZE_BYTES) {
                std::size_t idx = (round_bytes / ELEM_SIZE_ALIGN) - 1;
                auto* a = new (p) FreeList{};
                a->next = std::exchange(m_pools[idx], a);
                return;
            }
        }
        m_upstream_resource->deallocate(p, bytes, alignment);
    }

    bool do_is_equal(const std::pmr::memory_resource& other) const noexcept override
    {
        return this == &other;
    }

public:
    NodePoolResource()
    {
        allocate_chunk();
    }

    ~NodePoolResource()
    {
        for (std::byte* ptr : m_allocated_chunks) {
            std::destroy(ptr, ptr + CHUNK_SIZE_BYTES);
            m_upstream_resource->deallocate(ptr, CHUNK_SIZE_BYTES, ELEM_SIZE_ALIGN);
        }
    }
};
