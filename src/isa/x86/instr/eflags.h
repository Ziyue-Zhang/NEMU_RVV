/***************************************************************************************
* Copyright (c) 2014-2021 Zihao Yu, Nanjing University
*
* NEMU is licensed under Mulan PSL v2.
* You can use this software according to the terms and conditions of the Mulan PSL v2.
* You may obtain a copy of Mulan PSL v2 at:
*          http://license.coscl.org.cn/MulanPSL2
*
* THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
* EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
* MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
*
* See the Mulan PSL v2 for more details.
***************************************************************************************/

def_EHelper(pushf) {
  void rtl_compute_eflags(Decode *s, rtlreg_t *dest);
  rtl_compute_eflags(s, s0);
  rtl_push(s, s0);

  extern void difftest_fix_eflags(void *arg);
  difftest_set_patch(difftest_fix_eflags, (void *)(uintptr_t)cpu.esp);
}

def_EHelper(clc) {
  rtl_set_CF(s, rz);
}

def_EHelper(stc) {
  rtl_li(s, s0, 1);
  rtl_set_CF(s, s0);
}

def_EHelper(cld) {
  rtl_set_DF(s, rz);
}

#if 0
static inline def_EHelper(std) {
  rtl_li(s, s0, 1);
  rtl_set_DF(s, s0);
  print_asm("std");
}

static inline def_EHelper(cli) {
  rtl_set_IF(s, rz);
  print_asm("cli");
}

static inline def_EHelper(sti) {
  rtl_li(s, s0, 1);
  rtl_set_IF(s, s0);
  print_asm("sti");
}

static inline def_EHelper(popf) {
  void rtl_set_eflags(Decode *s, const rtlreg_t *src);
  rtl_pop(s, s0);
  rtl_set_eflags(s, s0);
  print_asm("popf");
}

static inline def_EHelper(sahf) {
  void rtl_set_eflags(Decode *s, const rtlreg_t *src);
  void rtl_compute_eflags(Decode *s, rtlreg_t *dest);

  rtl_compute_eflags(s, s0);
  rtl_andi(s, s0, s0, ~0xff);
  rtl_lr(s, s1, R_AH, 1);
  rtl_or(s, s0, s0, s1);
  rtl_set_eflags(s, s0);

  print_asm("sahf");
}
#endif
