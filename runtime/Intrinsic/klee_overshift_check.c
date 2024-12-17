//===-- klee_overshift_check.c ---------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <assert.h>

#include "klee/klee.h"

/* This instrumentation call is used to check for overshifting.
 * If we do try to do x << y or x >> y
 * where
 *   bitWidth = sizeof(x)*8
 *   shift = y
 *
 * then we can detect overshifting (which has undefined behaviour).
 */
void klee_overshift_check(unsigned long long bitWidth, unsigned long long shift) {
  assert(shift < bitWidth);
}


