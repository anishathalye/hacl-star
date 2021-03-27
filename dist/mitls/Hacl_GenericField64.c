/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_GenericField64.h"

/*******************************************************************************

A verified field arithmetic library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].
All the arithmetic operations are performed in the Montgomery domain.

*******************************************************************************/


/*
Allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument nBits is an exact number of significant bits of n.

  This function is *UNSAFE* and requires C clients to observe bn_mont_ctx_pre
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:

  • 0 < nBits /\ (nBits - 1) / bits t < len
  • pow2 (nBits - 1) < n /\ n < pow2 nBits

  • n % 2 = 1
  • 1 < n

  • n is a prime // needed for the modular multiplicative inverse

*/
Hacl_Bignum_GenericField_bn_mont_ctx_u64
Hacl_GenericField64_field_init(uint32_t len, uint32_t nBits, uint64_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *r2 = KRML_HOST_CALLOC(len, sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *n1 = KRML_HOST_CALLOC(len, sizeof (uint64_t));
  uint64_t *r21 = r2;
  uint64_t *n11 = n1;
  memcpy(n11, n, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits - (uint32_t)1U, n, r21);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  return
    (
      (Hacl_Bignum_GenericField_bn_mont_ctx_u64){
        .nBits = nBits,
        .len = len,
        .n = n11,
        .mu = mu,
        .r2 = r21
      }
    );
}

/*
Return a size of the modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
uint32_t Hacl_GenericField64_field_get_len(Hacl_Bignum_GenericField_bn_mont_ctx_u64 k)
{
  return k.len;
}

/*
Convert a bignum to its Montgomery representation.

  Write `a * R mod n` in `aM`.

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_to_field
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • a < n

*/
void
Hacl_GenericField64_to_field(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *a,
  uint64_t *aM
)
{
  Hacl_Bignum_Montgomery_bn_to_mont_u64(k.len, k.n, k.mu, k.r2, a, aM);
}

/*
Convert the result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField64_from_field(k, Hacl_GenericField64_to_field(k, a)) == a

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_from_field
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n

*/
void
Hacl_GenericField64_from_field(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *a
)
{
  Hacl_Bignum_Montgomery_bn_from_mont_u64(k.len, k.n, k.mu, aM, a);
}

/*
Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_add
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n 
*/
void
Hacl_GenericField64_add(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
)
{
  Hacl_Bignum_bn_add_mod_n_u64(k.len, k.n, aM, bM, cM);
}

/*
Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_sub
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n 
*/
void
Hacl_GenericField64_sub(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < k.len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = aM[(uint32_t)4U * i];
    uint64_t t20 = bM[(uint32_t)4U * i];
    uint64_t *res_i0 = cM + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = aM[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = bM[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = cM + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = aM[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = bM[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = cM + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = aM[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = bM[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = cM + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = k.len / (uint32_t)4U * (uint32_t)4U; i < k.len; i++)
  {
    uint64_t t1 = aM[i];
    uint64_t t2 = bM[i];
    uint64_t *res_i = cM + i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), k.len);
  uint64_t *tmp = alloca(k.len * sizeof (uint64_t));
  memset(tmp, 0U, k.len * sizeof (uint64_t));
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < k.len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = cM[(uint32_t)4U * i];
    uint64_t t20 = k.n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = cM[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = k.n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = cM[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = k.n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = cM[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = k.n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = k.len / (uint32_t)4U * (uint32_t)4U; i < k.len; i++)
  {
    uint64_t t1 = cM[i];
    uint64_t t2 = k.n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = (uint64_t)0U - c00;
  for (uint32_t i = (uint32_t)0U; i < k.len; i++)
  {
    uint64_t *os = cM;
    uint64_t x = (c2 & tmp[i]) | (~c2 & cM[i]);
    os[i] = x;
  }
}

/*
Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_mul
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n 
*/
void
Hacl_GenericField64_mul(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
)
{
  Hacl_Bignum_Montgomery_bn_mont_mul_u64(k.len, k.n, k.mu, aM, bM, cM);
}

/*
Write `aM * aM mod n` in `cM`.

  The arguments aM and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_sqr
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n 
*/
void
Hacl_GenericField64_sqr(Hacl_Bignum_GenericField_bn_mont_ctx_u64 k, uint64_t *aM, uint64_t *cM)
{
  Hacl_Bignum_Montgomery_bn_mont_sqr_u64(k.len, k.n, k.mu, aM, cM);
}

/*
Convert a bignum `one` to its Montgomery representation.

  The argument oneM is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void Hacl_GenericField64_one(Hacl_Bignum_GenericField_bn_mont_ctx_u64 k, uint64_t *oneM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), k.len);
  uint64_t *one = alloca(k.len * sizeof (uint64_t));
  memset(one, 0U, k.len * sizeof (uint64_t));
  memset(one, 0U, k.len * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), k.len + k.len);
  uint64_t *c = alloca((k.len + k.len) * sizeof (uint64_t));
  memset(c, 0U, (k.len + k.len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * k.len);
  uint64_t *tmp = alloca((uint32_t)4U * k.len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * k.len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(k.len, one, k.r2, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(k.len, k.n, k.mu, c, oneM);
}

/*
Write `aM ^ (-1) mod n` in `aInvM`.

  The arguments aM and aInvM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_inv
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • 0 < aM 
*/
void
Hacl_GenericField64_inverse(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *aInvM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), k.len);
  uint64_t *n2 = alloca(k.len * sizeof (uint64_t));
  memset(n2, 0U, k.len * sizeof (uint64_t));
  uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, k.n[0U], (uint64_t)2U, n2);
  uint64_t c2;
  if ((uint32_t)1U < k.len)
  {
    uint32_t rLen = k.len - (uint32_t)1U;
    uint64_t *a1 = k.n + (uint32_t)1U;
    uint64_t *res1 = n2 + (uint32_t)1U;
    uint64_t c = c0;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c1 = c;
    c2 = c1;
  }
  else
  {
    c2 = c0;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), k.len);
  uint64_t *one1 = alloca(k.len * sizeof (uint64_t));
  memset(one1, 0U, k.len * sizeof (uint64_t));
  memset(one1, 0U, k.len * sizeof (uint64_t));
  one1[0U] = (uint64_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), k.len + k.len);
  uint64_t *c1 = alloca((k.len + k.len) * sizeof (uint64_t));
  memset(c1, 0U, (k.len + k.len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * k.len);
  uint64_t *tmp = alloca((uint32_t)4U * k.len * sizeof (uint64_t));
  memset(tmp, 0U, (uint32_t)4U * k.len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(k.len, one1, k.r2, tmp, c1);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64(k.len, k.n, k.mu, c1, aInvM);
  uint32_t table_len = (uint32_t)16U;
  KRML_CHECK_SIZE(sizeof (uint64_t), table_len * k.len);
  uint64_t *table = alloca(table_len * k.len * sizeof (uint64_t));
  memset(table, 0U, table_len * k.len * sizeof (uint64_t));
  memcpy(table, aInvM, k.len * sizeof (uint64_t));
  uint64_t *t1 = table + k.len;
  memcpy(t1, aM, k.len * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < table_len - (uint32_t)2U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * k.len;
    uint64_t *t2 = table + (i + (uint32_t)2U) * k.len;
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(k.len, k.n, k.mu, t11, aM, t2);
  }
  for (uint32_t i = (uint32_t)0U; i < k.nBits / (uint32_t)4U; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(k.len, k.n, k.mu, aInvM, aInvM);
    }
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
    uint32_t i1 = (k.nBits - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (k.nBits - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = n2[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < k.len && (uint32_t)0U < j)
    {
      ite = p1 | n2[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    uint32_t bits_l32 = (uint32_t)bits_l;
    uint64_t *a_bits_l = table + bits_l32 * k.len;
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(k.len, k.n, k.mu, aInvM, a_bits_l, aInvM);
  }
  if (!(k.nBits % (uint32_t)4U == (uint32_t)0U))
  {
    uint32_t c10 = k.nBits % (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < c10; i++)
    {
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(k.len, k.n, k.mu, aInvM, aInvM);
    }
    uint32_t c20 = k.nBits % (uint32_t)4U;
    uint64_t mask_l = ((uint64_t)1U << c20) - (uint64_t)1U;
    uint32_t i = (uint32_t)0U;
    uint32_t j = (uint32_t)0U;
    uint64_t p1 = n2[i] >> j;
    uint64_t ite;
    if (i + (uint32_t)1U < k.len && (uint32_t)0U < j)
    {
      ite = p1 | n2[i + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_c = ite & mask_l;
    uint64_t bits_c0 = bits_c;
    uint32_t bits_c32 = (uint32_t)bits_c0;
    uint64_t *a_bits_c = table + bits_c32 * k.len;
    Hacl_Bignum_Montgomery_bn_mont_mul_u64(k.len, k.n, k.mu, aInvM, a_bits_c, aInvM);
  }
}
