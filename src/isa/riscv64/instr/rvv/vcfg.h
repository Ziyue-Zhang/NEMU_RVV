/***************************************************************************************
* Copyright (c) 2020-2022 Institute of Computing Technology, Chinese Academy of Sciences
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

#include <common.h>

#ifdef CONFIG_RVV_010

#include "cpu/exec.h"
#include "../local-include/vreg.h"
#include "../local-include/csr.h"
#include <stdio.h>
#include "../local-include/intr.h"
#include "../local-include/rtl.h"
#include <setjmp.h>

def_EHelper(vsetvl) {

  //vlmul+lg2(VLEN) <= vsew + vl
  // previous decode does not load vals for us
  rtl_lr(s, &(id_src1->val), id_src1->reg, 4);
  int mode = 0;
  if (id_src1->reg == 0 && id_dest->reg != 0) {
    mode = 1;
  }
  else if (id_src1->reg == 0 && id_dest->reg == 0) {
    mode = 2;
  }
  rtlreg_t vl = check_vsetvl(id_src2->val, id_src1->val, mode);
  printf("vl = %ld\n", vl);
  rtlreg_t error = 1ul << 63;
  if(vl==(uint64_t)-1) vcsr_write(IDXVTYPE, &error); //TODO: may cause error.
  else vcsr_write(IDXVTYPE, &(id_src2->val));
  vcsr_write(IDXVL, &vl);

  rtl_sr(s, id_dest->reg, &vl, 8/*4*/);

  rtl_li(s, &(s->tmp_reg[0]), 0);
  vcsr_write(IDXVSTART, &(s->tmp_reg[0]));

  // print_asm_template3(vsetvl);
}

def_EHelper(vsetvli) {

  //vlmul+lg2(VLEN) <= vsew + vl
  // previous decode does not load vals for us
  rtl_lr(s, &id_src1->val, id_src1->reg, 4);
  int mode = 0;
  if (id_src1->reg == 0 && id_dest->reg != 0) {
    mode = 1;
  }
  else if (id_src1->reg == 0 && id_dest->reg == 0) {
    mode = 2;
  }
  rtlreg_t vl = check_vsetvl(id_src2->val, id_src1->val, mode);
  rtlreg_t error = 1ul << 63;
  if(vl==(uint64_t)-1) vcsr_write(IDXVTYPE, &error); //TODO: may cause error.
  else vcsr_write(IDXVTYPE, &(id_src2->val));
  vcsr_write(IDXVL, &vl);

  rtl_sr(s, id_dest->reg, &vl, 8/*4*/);

  rtl_li(s, &(s->tmp_reg[0]), 0);
  vcsr_write(IDXVSTART, &(s->tmp_reg[0]));

  // print_asm_template3(vsetvl);
}

def_EHelper(vsetivli) {
  //vlmul+lg2(VLEN) <= vsew + vl
  // previous decode does not load vals for us
  rtlreg_t vl = check_vsetvl(id_src2->val, id_src1->val, 0);
  rtlreg_t error = 1ul << 63;
  if(vl==(uint64_t)-1) vcsr_write(IDXVTYPE, &error); //TODO: may cause error.
  else vcsr_write(IDXVTYPE, &(id_src2->val));
  vcsr_write(IDXVL, &vl);

  rtl_sr(s, id_dest->reg, &vl, 8/*4*/);

  rtl_li(s, &(s->tmp_reg[0]), 0);
  vcsr_write(IDXVSTART, &(s->tmp_reg[0]));

  // print_asm_template3(vsetvl);
}

#endif // CONFIG_RVV_010