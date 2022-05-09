// Copyright (c) 2017-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// Based on the public domain implementation 'merged' by D. J. Bernstein
// See https://cr.yp.to/chacha.html.

#include <crypto/common.h>
#include <crypto/chacha20.h>

#include <cassert>
#include <immintrin.h>
#include <string.h>

constexpr static inline uint32_t rotl32(uint32_t v, int c) { return (v << c) | (v >> (32 - c)); }

#define QUARTERROUND(a,b,c,d) \
  a += b; d = rotl32(d ^ a, 16); \
  c += d; b = rotl32(b ^ c, 12); \
  a += b; d = rotl32(d ^ a, 8); \
  c += d; b = rotl32(b ^ c, 7);

#define REPEAT10(a) do { {a}; {a}; {a}; {a}; {a}; {a}; {a}; {a}; {a}; {a}; } while(0)

static const unsigned char sigma[] = "expand 32-byte k";

void ChaCha20::SetKey(const unsigned char* k, size_t keylen)
{
    assert(keylen == 32);
    m_key[0] = ReadLE32(k + 0);
    m_key[1] = ReadLE32(k + 4);
    m_key[2] = ReadLE32(k + 8);
    m_key[3] = ReadLE32(k + 12);
    m_key[4] = ReadLE32(k + 16);
    m_key[5] = ReadLE32(k + 20);
    m_key[6] = ReadLE32(k + 24);
    m_key[7] = ReadLE32(k + 28);
    m_nonce = 0;
    m_block_counter = 0;
}

ChaCha20::ChaCha20() : m_key{0, 0, 0, 0}, m_nonce{0}, m_block_counter{0} {}

ChaCha20::ChaCha20(const unsigned char* k, size_t keylen)
{
    SetKey(k, keylen);
}

void ChaCha20::SetIV(uint64_t iv)
{
    m_nonce = iv;
}

void ChaCha20::Seek(uint64_t pos)
{
    m_block_counter = pos;
}

static const uint32_t SIGMA alignas(16) [] = {0x61707865, 0x3320646e, 0x79622d32, 0x6b206574};
static const uint8_t ROT16 alignas(16) [] = {2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13};
static const uint8_t ROT24 alignas(16) [] = {3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12, 13, 14};

void __attribute__((target("ssse3"))) ChaCha20::Keystream(unsigned char* c, size_t bytes)
{
    __m128i x0, x1, x2, x3;
    __m128i j1, j2, j3;
    __m128i t;
    __m128i rot16 = _mm_load_si128((__m128i*)ROT16);
    __m128i rot24 = _mm_load_si128((__m128i*)ROT24);

    unsigned char *ctarget = nullptr;
    unsigned char tmp[64];
    unsigned int i;

    if (!bytes) return;

    j1 = _mm_load_si128((const __m128i*)m_key);
    j2 = _mm_load_si128((const __m128i*)(m_key + 4));
    j3 = _mm_set_epi64x(m_nonce, m_block_counter);

    for (;;) {
        if (bytes < 64) {
            ctarget = c;
            c = tmp;
        }
        x0 = _mm_load_si128((const __m128i*)SIGMA);
        x1 = j1;
        x2 = j2;
        x3 = j3;

        for (int i = 0; i < 10; ++i) {
            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot16);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 20);
            t = _mm_slli_epi32(t, 12);
            x1 = _mm_or_si128(x1, t);

            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot24);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 25);
            t = _mm_slli_epi32(t, 7);
            x1 = _mm_or_si128(x1, t);

            x2 = _mm_shuffle_epi32(x2, 78);
            x1 = _mm_shuffle_epi32(x1, 57);
            x3 = _mm_shuffle_epi32(x3, 147);

            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot16);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 20);
            t = _mm_slli_epi32(t, 12);
            x1 = _mm_or_si128(x1, t);

            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot24);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 25);
            t = _mm_slli_epi32(t, 7);
            x1 = _mm_or_si128(x1, t);

            x2 = _mm_shuffle_epi32(x2, 78);
            x1 = _mm_shuffle_epi32(x1, 147);
            x3 = _mm_shuffle_epi32(x3, 57);
        }

        x0 = _mm_add_epi32(x0, _mm_load_si128((const __m128i*)SIGMA));
        x1 = _mm_add_epi32(x1, j1);
        x2 = _mm_add_epi32(x2, j2);
        x3 = _mm_add_epi32(x3, j3);

        ++m_block_counter;
        j3 = _mm_set_epi64x(m_nonce, m_block_counter);

        _mm_storeu_si128((__m128i*)c, x0);
        _mm_storeu_si128((__m128i*)(c + 16), x1);
        _mm_storeu_si128((__m128i*)(c + 32), x2);
        _mm_storeu_si128((__m128i*)(c + 48), x3);

        if (bytes <= 64) {
            if (bytes < 64) {
                for (i = 0;i < bytes;++i) ctarget[i] = c[i];
            }
            return;
        }
        bytes -= 64;
        c += 64;
    }
}

void __attribute__((target("ssse3"))) ChaCha20::Crypt(const unsigned char* m, unsigned char* c, size_t bytes)
{
    __m128i x0, x1, x2, x3;
    __m128i t;
    __m128i rot16 = _mm_load_si128((__m128i*)ROT16);
    __m128i rot24 = _mm_load_si128((__m128i*)ROT24);

    unsigned char *ctarget = nullptr;
    unsigned char tmp[64];
    unsigned int i;

    if (!bytes) return;

    j1 = _mm_load_si128((const __m128i*)m_key);
    j2 = _mm_load_si128((const __m128i*)(m_key + 4));
    j3 = _mm_set_epi64x(m_nonce, m_block_counter);

    for (;;) {
        if (bytes < 64) {
            // if m has fewer than 64 bytes available, copy m to tmp and
            // read from tmp instead
            for (i = 0;i < bytes;++i) tmp[i] = m[i];
            m = tmp;
            ctarget = c;
            c = tmp;
        }

        x0 = _mm_load_si128((const __m128i*)SIGMA);
        x1 = j1;
        x2 = j2;
        x3 = j3;

        for (int i = 0; i < 10; ++i) {
            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot16);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 20);
            t = _mm_slli_epi32(t, 12);
            x1 = _mm_or_si128(x1, t);

            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot24);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 25);
            t = _mm_slli_epi32(t, 7);
            x1 = _mm_or_si128(x1, t);

            x2 = _mm_shuffle_epi32(x2, 78);
            x1 = _mm_shuffle_epi32(x1, 57);
            x3 = _mm_shuffle_epi32(x3, 147);

            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot16);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 20);
            t = _mm_slli_epi32(t, 12);
            x1 = _mm_or_si128(x1, t);

            x0 = _mm_add_epi32(x0, x1);
            x3 = _mm_xor_si128(x3, x0);
            x3 = _mm_shuffle_epi8(x3, rot24);

            x2 = _mm_add_epi32(x2, x3);
            x1 = _mm_xor_si128(x1, x2);
            t = x1;
            x1 = _mm_srli_epi32(x1, 25);
            t = _mm_slli_epi32(t, 7);
            x1 = _mm_or_si128(x1, t);

            x2 = _mm_shuffle_epi32(x2, 78);
            x1 = _mm_shuffle_epi32(x1, 147);
            x3 = _mm_shuffle_epi32(x3, 57);
        }

        x0 = _mm_add_epi32(x0, _mm_load_si128((const __m128i*)SIGMA));
        x1 = _mm_add_epi32(x1, j1);
        x2 = _mm_add_epi32(x2, j2);
        x3 = _mm_add_epi32(x3, j3);

        ++m_block_counter;
        j3 = _mm_set_epi64x(m_nonce, m_block_counter);

        _mm_storeu_si128((__m128i*)c, _mm_xor_si128(_mm_loadu_si128((const __m128i*)m), x0));
        _mm_storeu_si128((__m128i*)(c + 16), _mm_xor_si128(_mm_loadu_si128((const __m128i*)(m + 16)), x1));
        _mm_storeu_si128((__m128i*)(c + 32), _mm_xor_si128(_mm_loadu_si128((const __m128i*)(m + 32)), x2));
        _mm_storeu_si128((__m128i*)(c + 48), _mm_xor_si128(_mm_loadu_si128((const __m128i*)(m + 48)), x3));

        if (bytes <= 64) {
            if (bytes < 64) {
                for (i = 0;i < bytes;++i) ctarget[i] = c[i];
            }
            return;
        }
        bytes -= 64;
        c += 64;
        m += 64;
    }
}
