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


#include "Hacl_Impl_P521_Exponent.h"

void Hacl_Impl_P521_Exponent_exponent_p521(uint64_t *t, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)9U;
  uint64_t *t2 = tempBuffer + (uint32_t)18U;
  uint64_t *t3 = tempBuffer + (uint32_t)27U;
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t, t0);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t, t0, t0);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t0, t1);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t1, t1);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t0, t1, t1);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t1, t2);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)3U, t2);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t1, t2, t2);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t2, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)7U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t2, t2);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t2, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)15U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t2, t3);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t2, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)31U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t2, t3);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t2, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)64U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t2, t2);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t2, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t, t3, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)129U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t2, t2);
  Hacl_Impl_P521_Exponent_montgomery_square_buffer(t2, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t, t3, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)259U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t2, t3);
  Hacl_Impl_P521_Exponent_fsquarePowN((uint32_t)2U, t3);
  Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(t3, t, result);
}

