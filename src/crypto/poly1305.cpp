// Copyright (c) 2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <crypto/common.h>
#include <crypto/poly1305.h>

#include <string.h>

namespace poly1305_donna {

// Based on the public domain implementation by Andrew Moon
// poly1305-donna-32.h from https://github.com/floodyberry/poly1305-donna

void poly1305_init(poly1305_context *st, const unsigned char key[32]) noexcept {
    /* h = 0 */
    st->h[0] = 0;
    st->h[1] = 0;
    st->h[2] = 0;

    /* r &= 0xffffffc0ffffffc0ffffffc0fffffff */
    st->r[0] = ReadLE64(&key[0]) & 0x0ffffffc0fffffff;
    st->r[1] = ReadLE64(&key[8]) & 0x0ffffffc0ffffffc;

    /* h = 0 */
    st->h[0] = 0;
    st->h[1] = 0;
    st->h[2] = 0;

    /* save pad for later */
    st->pad[0] = ReadLE64(&key[16]);
    st->pad[1] = ReadLE64(&key[24]);

    st->leftover = 0;
    st->final = 0;
}

# define CONSTANT_TIME_CARRY(a,b) ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))

static void poly1305_blocks(poly1305_context *st, const unsigned char *m, size_t bytes) noexcept {
    const uint32_t padbit = st->final ? 0 : 1;

    uint64_t r0, r1;
    uint64_t s1;
    uint64_t h0, h1, h2, c;
    unsigned __int128 d0, d1;

    r0 = st->r[0];
    r1 = st->r[1];

    s1 = r1 + (r1 >> 2);

    h0 = st->h[0];
    h1 = st->h[1];
    h2 = st->h[2];

    while (bytes >= POLY1305_BLOCK_SIZE) {
        /* h += m[i] */
        h0 = (uint64_t)(d0 = (unsigned __int128)h0 + ReadLE64(m + 0));
        h1 = (uint64_t)(d1 = (unsigned __int128)h1 + (d0 >> 64) + ReadLE64(m + 8));
        /*
         * padbit can be zero only when original len was
         * POLY1306_BLOCK_SIZE, but we don't check
         */
        h2 += (uint64_t)(d1 >> 64) + padbit;

        /* h *= r "%" p, where "%" stands for "partial remainder" */
        d0 = ((unsigned __int128)h0 * r0) +
             ((unsigned __int128)h1 * s1);
        d1 = ((unsigned __int128)h0 * r1) +
             ((unsigned __int128)h1 * r0) +
             (h2 * s1);
        h2 = (h2 * r0);

        /* last reduction step: */
        /* a) h2:h0 = h2<<128 + d1<<64 + d0 */
        h0 = (uint64_t)d0;
        h1 = (uint64_t)(d1 += d0 >> 64);
        h2 += (uint64_t)(d1 >> 64);
        /* b) (h2:h0 += (h2:h0>>130) * 5) %= 2^130 */
        c = (h2 >> 2) + (h2 & ~3UL);
        h2 &= 3;
        h0 += c;
        h1 += (c = CONSTANT_TIME_CARRY(h0,c));
        h2 += CONSTANT_TIME_CARRY(h1,c);
        /*
         * Occasional overflows to 3rd bit of h2 are taken care of
         * "naturally". If after this point we end up at the top of
         * this loop, then the overflow bit will be accounted for
         * in next iteration. If we end up in poly1305_emit, then
         * comparison to modulus below will still count as "carry
         * into 131st bit", so that properly reduced value will be
         * picked in conditional move.
         */

        m += POLY1305_BLOCK_SIZE;
        bytes -= POLY1305_BLOCK_SIZE;
    }

    st->h[0] = h0;
    st->h[1] = h1;
    st->h[2] = h2;
}

void poly1305_finish(poly1305_context *st, unsigned char mac[16]) noexcept {
    uint64_t h0, h1, h2;
    uint64_t g0, g1, g2;
    unsigned __int128 t;
    uint64_t mask;

    /* process the remaining block */
    if (st->leftover) {
        size_t i = st->leftover;
        st->buffer[i++] = 1;
        for (; i < POLY1305_BLOCK_SIZE; i++) {
            st->buffer[i] = 0;
        }
        st->final = 1;
        poly1305_blocks(st, st->buffer, POLY1305_BLOCK_SIZE);
    }

    h0 = st->h[0];
    h1 = st->h[1];
    h2 = st->h[2];

    /* compare to modulus by computing h + -p */
    g0 = (uint64_t)(t = (unsigned __int128)h0 + 5);
    g1 = (uint64_t)(t = (unsigned __int128)h1 + (t >> 64));
    g2 = h2 + (uint64_t)(t >> 64);

    /* if there was carry into 131st bit, h1:h0 = g1:g0 */
    mask = 0 - (g2 >> 2);
    g0 &= mask;
    g1 &= mask;
    mask = ~mask;
    h0 = (h0 & mask) | g0;
    h1 = (h1 & mask) | g1;

    /* mac = (h + nonce) % (2^128) */
    h0 = (uint64_t)(t = (unsigned __int128)h0 + st->pad[0]);
    h1 = (uint64_t)(t = (unsigned __int128)h1 + st->pad[1] + (t >> 64));

    WriteLE64(mac + 0, h0);
    WriteLE64(mac + 8, h1);

    /* zero out the state */
    st->h[0] = 0;
    st->h[1] = 0;
    st->h[2] = 0;
    st->r[0] = 0;
    st->r[1] = 0;
    st->pad[0] = 0;
    st->pad[1] = 0;
}

void poly1305_update(poly1305_context *st, const unsigned char *m, size_t bytes) noexcept {
    size_t i;

    /* handle leftover */
    if (st->leftover) {
        size_t want = (POLY1305_BLOCK_SIZE - st->leftover);
        if (want > bytes) {
            want = bytes;
        }
        for (i = 0; i < want; i++) {
            st->buffer[st->leftover + i] = m[i];
        }
        bytes -= want;
        m += want;
        st->leftover += want;
        if (st->leftover < POLY1305_BLOCK_SIZE) return;
        poly1305_blocks(st, st->buffer, POLY1305_BLOCK_SIZE);
        st->leftover = 0;
    }

    /* process full blocks */
    if (bytes >= POLY1305_BLOCK_SIZE) {
        size_t want = (bytes & ~(POLY1305_BLOCK_SIZE - 1));
        poly1305_blocks(st, m, want);
        m += want;
        bytes -= want;
    }

    /* store leftover */
    if (bytes) {
        for (i = 0; i < bytes; i++) {
            st->buffer[st->leftover + i] = m[i];
        }
        st->leftover += bytes;
    }
}

}  // namespace poly1305_donna
