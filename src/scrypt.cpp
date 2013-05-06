/*
 * Copyright 2009 Colin Percival, 2011 ArtForz
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file was originally written by Colin Percival as part of the Tarsnap
 * online backup system.
 */

#include "scrypt.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <emmintrin.h>
#include <openssl/sha.h>

#define SCRYPT_MEM_CONST    128
#define SCRYPT_MAX_R        262143


static inline uint32_t be32dec(const void *pp)
{
	const uint8_t *p = (uint8_t const *)pp;
	return ((uint32_t)(p[3]) + ((uint32_t)(p[2]) << 8) +
	    ((uint32_t)(p[1]) << 16) + ((uint32_t)(p[0]) << 24));
}

static inline void be32enc(void *pp, uint32_t x)
{
	uint8_t *p = (uint8_t *)pp;
	p[3] = x & 0xff;
	p[2] = (x >> 8) & 0xff;
	p[1] = (x >> 16) & 0xff;
	p[0] = (x >> 24) & 0xff;
}

static inline uint32_t le32dec(const void *pp)
{
	const uint8_t *p = (uint8_t const *)pp;
	return ((uint32_t)(p[0]) + ((uint32_t)(p[1]) << 8) +
	    ((uint32_t)(p[2]) << 16) + ((uint32_t)(p[3]) << 24));
}

static inline void le32enc(void *pp, uint32_t x)
{
	uint8_t *p = (uint8_t *)pp;
	p[0] = x & 0xff;
	p[1] = (x >> 8) & 0xff;
	p[2] = (x >> 16) & 0xff;
	p[3] = (x >> 24) & 0xff;
}


typedef struct HMAC_SHA256Context {
	SHA256_CTX ictx;
	SHA256_CTX octx;
} HMAC_SHA256_CTX;

/* Initialize an HMAC-SHA256 operation with the given key. */
static void
HMAC_SHA256_Init(HMAC_SHA256_CTX *ctx, const void *_K, size_t Klen)
{
	unsigned char pad[64];
	unsigned char khash[32];
	const unsigned char *K = (const unsigned char*)_K;
	size_t i;

	/* If Klen > 64, the key is really SHA256(K). */
	if (Klen > 64) {
		SHA256_Init(&ctx->ictx);
		SHA256_Update(&ctx->ictx, K, Klen);
		SHA256_Final(khash, &ctx->ictx);
		K = khash;
		Klen = 32;
	}

	/* Inner SHA256 operation is SHA256(K xor [block of 0x36] || data). */
	SHA256_Init(&ctx->ictx);
	memset(pad, 0x36, 64);
	for (i = 0; i < Klen; i++)
		pad[i] ^= K[i];
	SHA256_Update(&ctx->ictx, pad, 64);

	/* Outer SHA256 operation is SHA256(K xor [block of 0x5c] || hash). */
	SHA256_Init(&ctx->octx);
	memset(pad, 0x5c, 64);
	for (i = 0; i < Klen; i++)
		pad[i] ^= K[i];
	SHA256_Update(&ctx->octx, pad, 64);

	/* Clean the stack. */
	memset(khash, 0, 32);
}

/* Add bytes to the HMAC-SHA256 operation. */
static void
HMAC_SHA256_Update(HMAC_SHA256_CTX *ctx, const void *in, size_t len)
{
	/* Feed data to the inner SHA256 operation. */
	SHA256_Update(&ctx->ictx, in, len);
}

/* Finish an HMAC-SHA256 operation. */
static void
HMAC_SHA256_Final(unsigned char digest[32], HMAC_SHA256_CTX *ctx)
{
	unsigned char ihash[32];

	/* Finish the inner SHA256 operation. */
	SHA256_Final(ihash, &ctx->ictx);

	/* Feed the inner hash to the outer SHA256 operation. */
	SHA256_Update(&ctx->octx, ihash, 32);

	/* Finish the outer SHA256 operation. */
	SHA256_Final(digest, &ctx->octx);

	/* Clean the stack. */
	memset(ihash, 0, 32);
}

static void PBKDF2_SHA256_80_1(const uint8_t *passwd, const uint8_t *salt, size_t saltlen, uint8_t *buf, size_t dkLen)
{
	HMAC_SHA256_CTX PShctx, hctx;
	size_t i;
	uint8_t ivec[4];
	uint8_t U[32];
	uint8_t T[32];
	uint64_t j;
	int k;
	size_t clen;

	/* Compute HMAC state after processing P and S. */
	HMAC_SHA256_Init(&PShctx, passwd, 80);
	HMAC_SHA256_Update(&PShctx, salt, saltlen);

	/* Iterate through the blocks. */
	for (i = 0; i * 32 < dkLen; i++) {
		/* Generate INT(i + 1). */
		be32enc(ivec, (uint32_t)(i + 1));

		/* Compute U_1 = PRF(P, S || INT(i)). */
		memcpy(&hctx, &PShctx, sizeof(HMAC_SHA256_CTX));
		HMAC_SHA256_Update(&hctx, ivec, 4);
		HMAC_SHA256_Final(U, &hctx);

		/* T_i = U_1 ... */
		memcpy(T, U, 32);

		/* Copy as many bytes as necessary into buf. */
		clen = dkLen - i * 32;
		if (clen > 32)
			clen = 32;
		memcpy(&buf[i * 32], T, clen);
	}

	/* Clean PShctx, since we never called _Final on it. */
	memset(&PShctx, 0, sizeof(HMAC_SHA256_CTX));
}


#define ROTL(a, b) (((a) << (b)) | ((a) >> (32 - (b))))

static inline void xor_salsa8(uint32_t B[16], const uint32_t Bx[16])
{
	uint32_t x00,x01,x02,x03,x04,x05,x06,x07,x08,x09,x10,x11,x12,x13,x14,x15;
	int i;

	x00 = (B[ 0] ^= Bx[ 0]);
	x01 = (B[ 1] ^= Bx[ 1]);
	x02 = (B[ 2] ^= Bx[ 2]);
	x03 = (B[ 3] ^= Bx[ 3]);
	x04 = (B[ 4] ^= Bx[ 4]);
	x05 = (B[ 5] ^= Bx[ 5]);
	x06 = (B[ 6] ^= Bx[ 6]);
	x07 = (B[ 7] ^= Bx[ 7]);
	x08 = (B[ 8] ^= Bx[ 8]);
	x09 = (B[ 9] ^= Bx[ 9]);
	x10 = (B[10] ^= Bx[10]);
	x11 = (B[11] ^= Bx[11]);
	x12 = (B[12] ^= Bx[12]);
	x13 = (B[13] ^= Bx[13]);
	x14 = (B[14] ^= Bx[14]);
	x15 = (B[15] ^= Bx[15]);
	for (i = 0; i < 8; i += 2) {
		/* Operate on columns. */
		x04 ^= ROTL(x00 + x12,  7);  x09 ^= ROTL(x05 + x01,  7);
		x14 ^= ROTL(x10 + x06,  7);  x03 ^= ROTL(x15 + x11,  7);

		x08 ^= ROTL(x04 + x00,  9);  x13 ^= ROTL(x09 + x05,  9);
		x02 ^= ROTL(x14 + x10,  9);  x07 ^= ROTL(x03 + x15,  9);

		x12 ^= ROTL(x08 + x04, 13);  x01 ^= ROTL(x13 + x09, 13);
		x06 ^= ROTL(x02 + x14, 13);  x11 ^= ROTL(x07 + x03, 13);

		x00 ^= ROTL(x12 + x08, 18);  x05 ^= ROTL(x01 + x13, 18);
		x10 ^= ROTL(x06 + x02, 18);  x15 ^= ROTL(x11 + x07, 18);

		/* Operate on rows. */
		x01 ^= ROTL(x00 + x03,  7);  x06 ^= ROTL(x05 + x04,  7);
		x11 ^= ROTL(x10 + x09,  7);  x12 ^= ROTL(x15 + x14,  7);

		x02 ^= ROTL(x01 + x00,  9);  x07 ^= ROTL(x06 + x05,  9);
		x08 ^= ROTL(x11 + x10,  9);  x13 ^= ROTL(x12 + x15,  9);

		x03 ^= ROTL(x02 + x01, 13);  x04 ^= ROTL(x07 + x06, 13);
		x09 ^= ROTL(x08 + x11, 13);  x14 ^= ROTL(x13 + x12, 13);

		x00 ^= ROTL(x03 + x02, 18);  x05 ^= ROTL(x04 + x07, 18);
		x10 ^= ROTL(x09 + x08, 18);  x15 ^= ROTL(x14 + x13, 18);
	}
	B[ 0] += x00;
	B[ 1] += x01;
	B[ 2] += x02;
	B[ 3] += x03;
	B[ 4] += x04;
	B[ 5] += x05;
	B[ 6] += x06;
	B[ 7] += x07;
	B[ 8] += x08;
	B[ 9] += x09;
	B[10] += x10;
	B[11] += x11;
	B[12] += x12;
	B[13] += x13;
	B[14] += x14;
	B[15] += x15;
}

void scrypt_1024_1_1_256(const char *input, char *output, char *scratchpad)
{
	uint8_t B[128];
	uint32_t X[32];
	uint32_t *V;
	uint32_t i, j, k;

	V = (uint32_t *)(((uintptr_t)(scratchpad) + 63) & ~ (uintptr_t)(63));

	PBKDF2_SHA256_80_1((const uint8_t *)input, (const uint8_t *)input, 80, B, 128);

	for (k = 0; k < 32; k++)
		X[k] = le32dec(&B[4 * k]);

	for (i = 0; i < 1024; i++) {
		memcpy(&V[i * 32], X, 128);
		xor_salsa8(&X[0], &X[16]);
		xor_salsa8(&X[16], &X[0]);
	}
	for (i = 0; i < 1024; i++) {
		j = 32 * (X[16] & 1023);
		for (k = 0; k < 32; k++)
			X[k] ^= V[j + k];
		xor_salsa8(&X[0], &X[16]);
		xor_salsa8(&X[16], &X[0]);
	}

	for (k = 0; k < 32; k++)
		le32enc(&B[4 * k], X[k]);

	PBKDF2_SHA256_80_1((const uint8_t *)input, B, 128, (uint8_t *)output, 32);
}






#define SCRYPT_USE_SSE 0


#if SCRYPT_USE_SSE

static void blkcpy(void * dest, void * src, size_t len)
{
	__m128i * D = (__m128i*)dest;
	__m128i * S = (__m128i*)src;
	size_t L = len / 16;
	size_t i;

	for (i = 0; i < L; i++)
		D[i] = S[i];
}

static void blkxor(void * dest, void * src, size_t len)
{
	__m128i * D = (__m128i*)dest;
	__m128i * S = (__m128i*)src;
	size_t L = len / 16;
	size_t i;

	for (i = 0; i < L; i++)
		D[i] = _mm_xor_si128(D[i], S[i]);
}

static void salsa20_8(__m128i B[4])
{
	__m128i X0, X1, X2, X3;
	__m128i T;
	size_t i;

	X0 = B[0];
	X1 = B[1];
	X2 = B[2];
	X3 = B[3];

	for (i = 0; i < 8; i += 2) {
		/* Operate on "columns". */
		T = _mm_add_epi32(X0, X3);
		X1 = _mm_xor_si128(X1, _mm_slli_epi32(T, 7));
		X1 = _mm_xor_si128(X1, _mm_srli_epi32(T, 25));
		T = _mm_add_epi32(X1, X0);
		X2 = _mm_xor_si128(X2, _mm_slli_epi32(T, 9));
		X2 = _mm_xor_si128(X2, _mm_srli_epi32(T, 23));
		T = _mm_add_epi32(X2, X1);
		X3 = _mm_xor_si128(X3, _mm_slli_epi32(T, 13));
		X3 = _mm_xor_si128(X3, _mm_srli_epi32(T, 19));
		T = _mm_add_epi32(X3, X2);
		X0 = _mm_xor_si128(X0, _mm_slli_epi32(T, 18));
		X0 = _mm_xor_si128(X0, _mm_srli_epi32(T, 14));

		/* Rearrange data. */
		X1 = _mm_shuffle_epi32(X1, 0x93);
		X2 = _mm_shuffle_epi32(X2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x39);

		/* Operate on "rows". */
		T = _mm_add_epi32(X0, X1);
		X3 = _mm_xor_si128(X3, _mm_slli_epi32(T, 7));
		X3 = _mm_xor_si128(X3, _mm_srli_epi32(T, 25));
		T = _mm_add_epi32(X3, X0);
		X2 = _mm_xor_si128(X2, _mm_slli_epi32(T, 9));
		X2 = _mm_xor_si128(X2, _mm_srli_epi32(T, 23));
		T = _mm_add_epi32(X2, X3);
		X1 = _mm_xor_si128(X1, _mm_slli_epi32(T, 13));
		X1 = _mm_xor_si128(X1, _mm_srli_epi32(T, 19));
		T = _mm_add_epi32(X1, X2);
		X0 = _mm_xor_si128(X0, _mm_slli_epi32(T, 18));
		X0 = _mm_xor_si128(X0, _mm_srli_epi32(T, 14));

		/* Rearrange data. */
		X1 = _mm_shuffle_epi32(X1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x93);
	}

	B[0] = _mm_add_epi32(B[0], X0);
	B[1] = _mm_add_epi32(B[1], X1);
	B[2] = _mm_add_epi32(B[2], X2);
	B[3] = _mm_add_epi32(B[3], X3);
}

static void blockmix_salsa8(__m128i * Bin, __m128i * Bout, __m128i * X, size_t r)
{
	size_t i;

	/* 1: X <-- B_{2r - 1} */
	blkcpy(X, &Bin[8 * r - 4], 64);

	/* 2: for i = 0 to 2r - 1 do */
	for (i = 0; i < r; i++) {
		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 8], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 4], X, 64);

		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 8 + 4], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[(r + i) * 4], X, 64);
	}
}

static uint64_t integerify(void * B, size_t r)
{
	uint32_t * X = (uint32_t *)((uintptr_t)(B) + (2 * r - 1) * 64);

	return (((uint64_t)(X[13]) << 32) + X[0]);
}

static void smix(uint8_t * B, size_t r, uint64_t N, void * V, void * XY)
{
	__m128i * X = (__m128i*)XY;
	__m128i * Y = (__m128i *)((uintptr_t)(XY) + 128 * r);
	__m128i * Z = (__m128i *)((uintptr_t)(XY) + 256 * r);
	uint32_t * X32 = (uint32_t *)X;
	uint64_t i, j;
	size_t k;

	/* 1: X <-- B */
	for (k = 0; k < 2 * r; k++) {
		for (i = 0; i < 16; i++) {
			X32[k * 16 + i] =
			    le32dec(&B[(k * 16 + (i * 5 % 16)) * 4]);
		}
	}

	/* 2: for i = 0 to N - 1 do */
	for (i = 0; i < N; i += 2) {
		/* 3: V_i <-- X */
		blkcpy((void *)((uintptr_t)(V) + i * 128 * r), X, 128 * r);

		/* 4: X <-- H(X) */
		blockmix_salsa8(X, Y, Z, r);

		/* 3: V_i <-- X */
		blkcpy((void *)((uintptr_t)(V) + (i + 1) * 128 * r),
		    Y, 128 * r);

		/* 4: X <-- H(X) */
		blockmix_salsa8(Y, X, Z, r);
	}

	/* 6: for i = 0 to N - 1 do */
	for (i = 0; i < N; i += 2) {
		/* 7: j <-- Integerify(X) mod N */
		j = integerify(X, r) & (N - 1);

		/* 8: X <-- H(X \xor V_j) */
		blkxor(X, (void *)((uintptr_t)(V) + j * 128 * r), 128 * r);
		blockmix_salsa8(X, Y, Z, r);

		/* 7: j <-- Integerify(X) mod N */
		j = integerify(Y, r) & (N - 1);

		/* 8: X <-- H(X \xor V_j) */
		blkxor(Y, (void *)((uintptr_t)(V) + j * 128 * r), 128 * r);
		blockmix_salsa8(Y, X, Z, r);
	}

	/* 10: B' <-- X */
	for (k = 0; k < 2 * r; k++) {
		for (i = 0; i < 16; i++) {
			le32enc(&B[(k * 16 + (i * 5 % 16)) * 4],
			    X32[k * 16 + i]);
		}
	}
}

#else
static void blkcpy(void * dest, void * src, size_t len)
{
	size_t * D = (size_t*)dest;
	size_t * S = (size_t*)src;
	size_t L = len / sizeof(size_t);
	size_t i;

	for (i = 0; i < L; i++)
		D[i] = S[i];
}

static void blkxor(void * dest, void * src, size_t len)
{
	size_t * D = (size_t*)dest;
	size_t * S = (size_t*)src;
	size_t L = len / sizeof(size_t);
	size_t i;

	for (i = 0; i < L; i++)
		D[i] ^= S[i];
}

static void salsa20_8(uint32_t B[16])
{
	uint32_t x[16];
	size_t i;

	blkcpy(x, B, 64);
	for (i = 0; i < 8; i += 2) {
#define R(a,b) (((a) << (b)) | ((a) >> (32 - (b))))
		/* Operate on columns. */
		x[ 4] ^= R(x[ 0]+x[12], 7);  x[ 8] ^= R(x[ 4]+x[ 0], 9);
		x[12] ^= R(x[ 8]+x[ 4],13);  x[ 0] ^= R(x[12]+x[ 8],18);

		x[ 9] ^= R(x[ 5]+x[ 1], 7);  x[13] ^= R(x[ 9]+x[ 5], 9);
		x[ 1] ^= R(x[13]+x[ 9],13);  x[ 5] ^= R(x[ 1]+x[13],18);

		x[14] ^= R(x[10]+x[ 6], 7);  x[ 2] ^= R(x[14]+x[10], 9);
		x[ 6] ^= R(x[ 2]+x[14],13);  x[10] ^= R(x[ 6]+x[ 2],18);

		x[ 3] ^= R(x[15]+x[11], 7);  x[ 7] ^= R(x[ 3]+x[15], 9);
		x[11] ^= R(x[ 7]+x[ 3],13);  x[15] ^= R(x[11]+x[ 7],18);

		/* Operate on rows. */
		x[ 1] ^= R(x[ 0]+x[ 3], 7);  x[ 2] ^= R(x[ 1]+x[ 0], 9);
		x[ 3] ^= R(x[ 2]+x[ 1],13);  x[ 0] ^= R(x[ 3]+x[ 2],18);

		x[ 6] ^= R(x[ 5]+x[ 4], 7);  x[ 7] ^= R(x[ 6]+x[ 5], 9);
		x[ 4] ^= R(x[ 7]+x[ 6],13);  x[ 5] ^= R(x[ 4]+x[ 7],18);

		x[11] ^= R(x[10]+x[ 9], 7);  x[ 8] ^= R(x[11]+x[10], 9);
		x[ 9] ^= R(x[ 8]+x[11],13);  x[10] ^= R(x[ 9]+x[ 8],18);

		x[12] ^= R(x[15]+x[14], 7);  x[13] ^= R(x[12]+x[15], 9);
		x[14] ^= R(x[13]+x[12],13);  x[15] ^= R(x[14]+x[13],18);
#undef R
	}
	for (i = 0; i < 16; i++)
		B[i] += x[i];
}

static void blockmix_salsa8(uint32_t * Bin, uint32_t * Bout, uint32_t * X, size_t r)
{
	size_t i;

	/* 1: X <-- B_{2r - 1} */
	blkcpy(X, &Bin[(2 * r - 1) * 16], 64);

	/* 2: for i = 0 to 2r - 1 do */
	for (i = 0; i < 2 * r; i += 2) {
		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 16], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 8], X, 64);

		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 16 + 16], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 8 + r * 16], X, 64);
	}
}

static uint64_t integerify(void * B, size_t r)
{
	uint32_t * X = (uint32_t *)((uintptr_t)(B) + (2 * r - 1) * 64);

	return (((uint64_t)(X[1]) << 32) + X[0]);
}

static void smix(uint8_t * B, size_t r, uint32_t * V, uint32_t * XY)
{
	uint32_t * X = XY;
	uint32_t * Y = &XY[32 * r];
	uint32_t * Z = &XY[64 * r];
	uint64_t i;
	uint64_t j;
	size_t k;

	/* 1: X <-- B */
	for (k = 0; k < 32 * r; k++)
		X[k] = le32dec(&B[4 * k]);

	/* 2: for i = 0 to N - 1 do */
	for (i = 0; i < SCRYPT_MEM_CONST; i += 2)
    {
		/* 3: V_i <-- X */
		blkcpy(&V[i * (32 * r)], X, 128 * r);

		/* 4: X <-- H(X) */
		blockmix_salsa8(X, Y, Z, r);

		/* 3: V_i <-- X */
		blkcpy(&V[(i + 1) * (32 * r)], Y, 128 * r);

		/* 4: X <-- H(X) */
		blockmix_salsa8(Y, X, Z, r);
	}

	/* 6: for i = 0 to N - 1 do */
	for (i = 0; i < SCRYPT_MEM_CONST; i += 2)
    {
		/* 7: j <-- Integerify(X) mod N */
		j = integerify(X, r) & (SCRYPT_MEM_CONST - 1);

		/* 8: X <-- H(X \xor V_j) */
		blkxor(X, &V[j * (32 * r)], 128 * r);
		blockmix_salsa8(X, Y, Z, r);

		/* 7: j <-- Integerify(X) mod N */
		j = integerify(Y, r) & (SCRYPT_MEM_CONST - 1);

		/* 8: X <-- H(X \xor V_j) */
		blkxor(Y, &V[j * (32 * r)], 128 * r);
		blockmix_salsa8(Y, X, Z, r);
	}

	/* 10: B' <-- X */
	for (k = 0; k < 32 * r; k++)
		le32enc(&B[4 * k], X[k]);
}
#endif


unsigned int isqrt(unsigned int num)
{
    unsigned int res = 0;
    unsigned int bit = 1;
    bit <<= 120;

    while (bit > num)
        bit >>= 2;

    while (bit != 0)
    {
        if (num >= res + bit)
        {
            num -= res + bit;
            res = (res >> 1) + bit;
        }
        else
            res >>= 1;
        bit >>= 2;
    }
    return res;
}

Scrypt::Scrypt(unsigned int nBits)
{
    m_B0 = NULL;
    m_V0 = NULL;
    m_XY0 = NULL;
    Reset(nBits);
}

Scrypt::~Scrypt()
{
    CleanUp();
}

void Scrypt::CleanUp()
{
    if(m_B0!=NULL)
        free(m_B0);
    if(m_XY0!=NULL)
        free(m_XY0);
    if(m_V0!=NULL)
        free(m_V0);
    m_B0 = NULL;
    m_V0 = NULL;
    m_XY0 = NULL;
}

void Scrypt::Reset(unsigned int nBits)
{
    int nShift = (nBits >> 24) & 0xff;
    double dDiff = (double)0x0000ffff / (double)(nBits & 0x00ffffff);
    double dReturn = 1.0;
    while (nShift < 29)
    {
        dDiff *= 256.0;
        nShift++;
    }
    while (nShift > 29)
    {
        dDiff /= 256.0;
        nShift--;
    }

    dReturn = floor(dDiff);
    dReturn = 9.0+(sqrt(dReturn)); // just above gpu litecoin miners
    if(dReturn >= SCRYPT_MAX_R)
        dReturn = SCRYPT_MAX_R;
    m_TargetR = (unsigned int)(dReturn);
    printf("target R: %u  %u  %u\n", (unsigned int)(dDiff), m_TargetR, (128 * m_TargetR * SCRYPT_MEM_CONST + 64)/1024);

    CleanUp();
    m_V0  = malloc(256 * m_TargetR * SCRYPT_MEM_CONST + 64);
    m_B0  = malloc(256 * m_TargetR + 64);
    m_XY0 = malloc(512 * m_TargetR + 64 + 64);
}

void Scrypt::Target_2_1(const char *input, char *output)
{
	uint32_t* V = (uint32_t *)(((uintptr_t)(m_V0) + 63) & ~ (uintptr_t)(63));
	uint8_t* B = (uint8_t *)(((uintptr_t)(m_B0) + 256) & ~ (uintptr_t)(63));
	uint32_t* XY = (uint32_t *)(((uintptr_t)(m_XY0) + 256) & ~ (uintptr_t)(63));

	// 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen)
	PBKDF2_SHA256_80_1((const uint8_t *)input, (const uint8_t *)input, 80, B, 128 * m_TargetR);

	// 2: B_i <-- MF(B_i, N)
	smix(B, m_TargetR, (uint32_t*)V, (uint32_t*)XY);

	// 3: DK <-- PBKDF2(P, B, 1, dkLen)
	PBKDF2_SHA256_80_1((const uint8_t *)input, B, 128 * m_TargetR, (uint8_t *)output, 32);
}

