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
#ifdef CONFIG_RVV

#include "vcompute_impl.h"

// #define PERMInstr(opcode) permutation_instr(opcode, pc);
// static void permutation_instr(int opcode, vaddr_t* pc) {
//   // only move/ext here, no slide
//   switch (opcode) {
//     case EXT_X_V : 
//   }
// }

def_EHelper(vadd) {
  ARTHI(ADD, SIGNED)
  // print_asm_template3(vadd);
}

def_EHelper(vsub) {
  Assert(s->src_vmode != SRC_VI, "vsub.vi not supported\n");
  ARTHI(SUB, SIGNED)
  // print_asm_template3(vsub);
}

def_EHelper(vrsub) {
  Assert(s->src_vmode != SRC_VV, "vrsub.vv not supported\n");
  ARTHI(RSUB, SIGNED)
  // print_asm_template3(vrsub);
}

def_EHelper(vminu) {
  ARTHI(MINU, UNSIGNED)
}

def_EHelper(vmin) {
  ARTHI(MIN, SIGNED)
}

def_EHelper(vmaxu) {
  ARTHI(MAXU, UNSIGNED)
}

def_EHelper(vmax) {
  ARTHI(MAX, SIGNED)
}

def_EHelper(vand) {
  ARTHI(AND, SIGNED)
  // print_asm_template3(vand);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vor) {
  ARTHI(OR, SIGNED)
  // print_asm_template3(vor);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vxor) {
  ARTHI(XOR, SIGNED)
  // print_asm_template3(vxor);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vrgather) {
  ARTHI(RGATHER, UNSIGNED)
}

def_EHelper(vrgatherei16) {
  ARTHI(RGATHEREI16, UNSIGNED)
}

def_EHelper(vslideup) {
  ARTHI(SLIDEUP, UNSIGNED)
}

def_EHelper(vslidedown) {
  ARTHI(SLIDEDOWN, UNSIGNED)
}

def_EHelper(vslide1up) {
  ARTHI(SLIDE1UP, UNSIGNED)
}

def_EHelper(vslide1down) {
  ARTHI(SLIDE1DOWN, UNSIGNED)
}

def_EHelper(vadc) {
  ARTHI(ADC, SIGNED)
}

def_EHelper(vmadc) {
  ARTHI_MASK(MADC, UNSIGNED)
}

def_EHelper(vsbc) {
  ARTHI(SBC, SIGNED)
}

def_EHelper(vmsbc) {
  ARTHI_MASK(MSBC, UNSIGNED)
}

def_EHelper(vmerge) {
  ARTHI(MERGE, SIGNED)
  // print_asm_template3(vmerge);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmseq) {
  ARTHI_MASK(MSEQ, SIGNED)
  // print_asm_template3(vmseq);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmsne) {
  ARTHI_MASK(MSNE, SIGNED)
  // print_asm_template3(vmsne);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmsltu) {
  Assert(s->src_vmode != SRC_VI, "vmsltu not supprt SRC_VI\n");
  ARTHI_MASK(MSLTU, UNSIGNED)
  // print_asm_template3(vmsltu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmslt) {
  Assert(s->src_vmode != SRC_VI, "vmslt not supprt SRC_VI\n");
  ARTHI_MASK(MSLT, SIGNED)
  // print_asm_template3(vmslt);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmsleu) {
  ARTHI_MASK(MSLEU, UNSIGNED)
  // print_asm_template3(vmsleu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmsle) {
  ARTHI_MASK(MSLE, SIGNED);
  // print_asm_template3(vmsle);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmsgtu) {
  Assert(s->src_vmode != SRC_VV, "vmsgtu not support SRC_VV\n");
  ARTHI_MASK(MSGTU, UNSIGNED)
  // print_asm_template3(vmsgtu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmsgt) {
  Assert(s->src_vmode != SRC_VV, "vmsgt not support SRC_VV\n");
  ARTHI_MASK(MSGT, SIGNED)
  // print_asm_template3(vmsgt);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vsaddu) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vsadd) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vssubu) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vssub) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vaadd) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vsll) {
  ARTHI(SLL, UNSIGNED)
  // print_asm_template3(vsll);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vasub) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vsmul) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vsrl) {
  ARTHI(SRL, UNSIGNED)
  // print_asm_template3(vsrl);
  //longjmp_raise_intr(EX_II);
}

def_EHelper(vsra) {
  ARTHI(SRA, UNSIGNED)
  // print_asm_template3(vsra);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vssrl) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vssra) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vnsrl) {
  ARTHI_NARROW(SRL, UNSIGNED, 1)
}

def_EHelper(vnsra) {
  ARTHI_NARROW(SRA, UNSIGNED, 1)
}

def_EHelper(vnclipu) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vnclip) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vwredsumu) {
  REDInstr_WIDE(REDSUM, UNSIGNED);
}

def_EHelper(vwredsum) {
  REDInstr_WIDE(REDSUM, SIGNED);
}

def_EHelper(vdotu) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vdot) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vwsmaccu) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vwsmacc) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vwsmaccsu) {
  longjmp_raise_intr(EX_II);
}

def_EHelper(vwsmaccus) {
  longjmp_raise_intr(EX_II);
}


//op-m
def_EHelper(vredsum) {
  REDInstr(REDSUM, SIGNED);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vredand) {
  REDInstr(REDAND, UNSIGNED);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vredor) {
  REDInstr(REDOR, UNSIGNED);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vredxor) {
  REDInstr(REDXOR, UNSIGNED);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vredminu) {
  REDInstr(REDMINU, UNSIGNED);
}

def_EHelper(vredmin) {
  REDInstr(REDMIN, SIGNED);
}

def_EHelper(vredmaxu) {
  REDInstr(REDMAXU, UNSIGNED);
}

def_EHelper(vredmax) {
  REDInstr(REDMAX, SIGNED);
}

def_EHelper(vmvsx) {
  rtl_lr(s, &(id_src->val), id_src1->reg, 4);
  rtl_mv(s, s1, &id_src->val); 
  rtl_sext(s, s1, s1, 1 << vtype->vsew);
  set_vreg(id_dest->reg, 0, *s1, vtype->vsew, vtype->vlmul, 1);
}

def_EHelper(vmvxs) {
  get_vreg(id_src2->reg, 0, s0, vtype->vsew, vtype->vlmul, 1, 1);
  rtl_sext(s, s0, s0, 1 << 3);
  rtl_sr(s, id_dest->reg, s0, 4);
}

def_EHelper(vmvnr) {
    rtl_li(s, s1, s->isa.instr.v_opv3.v_imm5 );
    int NREG = (*s1) + 1;
    int len = (VLEN >> 6) * NREG;
    int vlmul = 0;
    while (NREG > 1) {
      NREG = NREG >> 1;
      vlmul++;
    }
    for (int i = 0; i < len; i++) {
      get_vreg(id_src2->reg, i, s0, 3, vlmul, 1, 1);
      set_vreg(id_dest->reg, i, *s0, 3, vlmul, 1);
    }
}

def_EHelper(vcpop) {
  // longjmp_raise_intr(EX_II);
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);
  
  rtl_li(s, s1, 0);
  for(int idx = vstart->val; idx < vl->val; idx ++) {
        // mask
    rtlreg_t mask = get_mask(0, idx, vtype->vsew, vtype->vlmul);
    if(s->vm == 0 && mask == 0)
      continue;

    *s0 = get_mask(id_src2->reg, idx, vtype->vsew, vtype->vlmul);
    *s0 &= 1;

    if(*s0 == 1)
      rtl_addi(s, s1, s1, 1);
  }
  rtl_sr(s, id_dest->reg, s1, 4);
}

def_EHelper(vfirst) {
  // longjmp_raise_intr(EX_II);
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);
  
  int pos = -1;
  for(int idx = vstart->val; idx < vl->val; idx ++) {
    *s0 = get_mask(id_src2->reg, idx, vtype->vsew, vtype->vlmul);
    *s0 &= 1;
    if(*s0 == 1) {
        pos = idx;
        break;
    }
  }
  rtl_li(s, s1, pos);
  rtl_sr(s, id_dest->reg, s1, 4);
}

def_EHelper(vmsbf) {
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);

  bool first_one = false;
  for(int idx = vstart->val; idx < vl->val; idx ++) {
    rtlreg_t mask = get_mask(0, idx, vtype->vsew, vtype->vlmul);
    if(s->vm == 0 && mask == 0)
      continue;
    
    *s0 = get_mask(id_src2->reg, idx, vtype->vsew, vtype->vlmul);
    *s0 &= 1;

    if(!first_one && *s0 == 1) {
      first_one = true;
    }

    if(first_one) {
      set_mask(id_dest->reg, idx, 0, vtype->vsew, vtype->vlmul);
    } else{
      set_mask(id_dest->reg, idx, 1, vtype->vsew, vtype->vlmul);
    }
  }
}

def_EHelper(vmsof) {
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);

  bool first_one = false;
  for(int idx = vstart->val; idx < vl->val; idx ++) {
    rtlreg_t mask = get_mask(0, idx, vtype->vsew, vtype->vlmul);
    if(s->vm == 0 && mask == 0)
      continue;
    
    *s0 = get_mask(id_src2->reg, idx, vtype->vsew, vtype->vlmul);
    *s0 &= 1;

    if(!first_one && *s0 == 1) {
      set_mask(id_dest->reg, idx, 1, vtype->vsew, vtype->vlmul);
      first_one = true;
      continue;
    }
    set_mask(id_dest->reg, idx, 0, vtype->vsew, vtype->vlmul);
  }
}

def_EHelper(vmsif) {
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);

  bool first_one = false;
  for(int idx = vstart->val; idx < vl->val; idx ++) {
    rtlreg_t mask = get_mask(0, idx, vtype->vsew, vtype->vlmul);
    if(s->vm == 0 && mask == 0)
      continue;
    
    *s0 = get_mask(id_src2->reg, idx, vtype->vsew, vtype->vlmul);
    *s0 &= 1;

    if(first_one) {
      set_mask(id_dest->reg, idx, 0, vtype->vsew, vtype->vlmul);
    } else{
      set_mask(id_dest->reg, idx, 1, vtype->vsew, vtype->vlmul);
    }

    if(!first_one && *s0 == 1) {
      first_one = true;
    }
  }
}

def_EHelper(viota) {
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);

  rtl_li(s, s1, 0);
  for(int idx = vstart->val; idx < vl->val; idx ++) {
    rtlreg_t mask = get_mask(0, idx, vtype->vsew, vtype->vlmul);
    if(s->vm == 0 && mask == 0)
      continue;
    
    *s0 = get_mask(id_src2->reg, idx, vtype->vsew, vtype->vlmul);
    *s0 &= 1;

    set_vreg(id_dest->reg, idx, *s1, vtype->vsew, vtype->vlmul, 1);
    
    if(*s0 == 1) {
      rtl_addi(s, s1, s1, 1);
    }
  }
}

def_EHelper(vid) {
  for(int idx = 0; idx < vl->val; idx ++) {
        // mask
    rtlreg_t mask = get_mask(0, idx, vtype->vsew, vtype->vlmul);
    // Masking does not change the index value written to active elements.
    if(s->vm == 0 && mask == 0)
      continue;

    rtl_li(s, s1, idx);
    set_vreg(id_dest->reg, idx, *s1, vtype->vsew, vtype->vlmul, 1);
  }
}

def_EHelper(vzextvf8) {
  ARTHI_NARROW(VEXT, UNSIGNED, -3);
}

def_EHelper(vsextvf8) {
  ARTHI_NARROW(VEXT, SIGNED, -3);
}

def_EHelper(vzextvf4) {
  ARTHI_NARROW(VEXT, UNSIGNED, -2);
}

def_EHelper(vsextvf4) {
  ARTHI_NARROW(VEXT, SIGNED, -2);
}

def_EHelper(vzextvf2) {
  ARTHI_NARROW(VEXT, UNSIGNED, -1);
}

def_EHelper(vsextvf2) {
  ARTHI_NARROW(VEXT, SIGNED, -1);
}

def_EHelper(vcompress) {
  if(vstart->val != 0)
    longjmp_raise_intr(EX_II);

  rtl_li(s, s1, 0);
  for(int idx = vstart->val; idx < vl->val; idx ++) {
    rtlreg_t mask = get_mask(id_src1->reg, idx, vtype->vsew, vtype->vlmul);
    
    if (mask == 0) {
        continue;
    }

    get_vreg(id_src2->reg, idx, s0, vtype->vsew, vtype->vlmul, 1, 1);

    set_vreg(id_dest->reg, *s1, *s0, vtype->vsew, vtype->vlmul, 1);
    
    rtl_addi(s, s1, s1, 1);
  }
}

def_EHelper(vmandnot) {
  MASKINSTR(MANDNOT)
  // print_asm_template3(vmandnot);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmand) {
  MASKINSTR(MAND)
  // print_asm_template3(vmand);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmor) {
  MASKINSTR(MOR)
  // print_asm_template3(vmor);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmxor) {
  MASKINSTR(MXOR)
  // print_asm_template3(vmxor);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmornot) {
  MASKINSTR(MORNOT)
  // print_asm_template3(vmornot);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmnand) {
  MASKINSTR(MNAND)
  // print_asm_template3(vmnand);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmnor) {
  MASKINSTR(MNOR)
  // print_asm_template3(vmnor);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmxnor) {
  MASKINSTR(MXNOR);
  // print_asm_template3(vmnor);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vdivu) {
  Assert(s->src_vmode != SRC_VI, "vdivu does not support SRC_VI\n");
  ARTHI(DIVU, UNSIGNED)
  // print_asm_template3(vdivu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vdiv) {
  Assert(s->src_vmode != SRC_VI, "vdiv does not support SRC_VI\n");
  ARTHI(DIV, SIGNED)
  // print_asm_template3(vdiv);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vremu) {
  Assert(s->src_vmode != SRC_VI, "vremu does not support SRC_VI\n");
  ARTHI(REMU, UNSIGNED)
  // print_asm_template3(vremu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vrem) {
  Assert(s->src_vmode != SRC_VI, "vrem does not support SRC_VI\n");
  ARTHI(REM, SIGNED)
  // print_asm_template3(vrem);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmulhu) {
  Assert(s->src_vmode != SRC_VI, "vmulhu does not support SRC_VI\n");
  ARTHI(MULHU, UNSIGNED)
  // print_asm_template3(vmulhu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmul) {
  Assert(s->src_vmode != SRC_VI, "vmul does not support SRC_VI\n");
  ARTHI(MUL, SIGNED)
  // print_asm_template3(vmul);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmulhsu) {
  Assert(s->src_vmode != SRC_VI, "vmulhsu does not support SRC_VI\n");
  ARTHI(MULHSU, UNSIGNED)
  // print_asm_template3(vmulshu);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmulh) {
  Assert(s->src_vmode != SRC_VI, "vmulh does not support SRC_VI\n");
  ARTHI(MULH, SIGNED)
  // print_asm_template3(vmulh);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmadd) {
  ARTHI(MADD, SIGNED)
  // print_asm_template3(vmadd);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vnmsub) {
  ARTHI(NMSUB, SIGNED)
  // print_asm_template3(vnmsub);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vmacc) {
  ARTHI(MACC, SIGNED)
  // print_asm_template3(vmacc);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vnmsac) {
  ARTHI(NMSAC, SIGNED)
  // print_asm_template3(vmacc);
  // longjmp_raise_intr(EX_II);
}

def_EHelper(vwaddu) {
  ARTHI_WIDE(ADD, UNSIGNED)
}

def_EHelper(vwadd) {
  ARTHI_WIDE(ADD, SIGNED)
}

def_EHelper(vwsubu) {
  ARTHI_WIDE(SUB, UNSIGNED)
}

def_EHelper(vwsub) {
  ARTHI_WIDE(SUB, SIGNED)
}

def_EHelper(vwaddu_w) {
  arthimetic_instr(ADD, UNSIGNED, 1, 1, 0, s);
}

def_EHelper(vwadd_w) {
  arthimetic_instr(ADD, SIGNED, 1, 1, 0, s);
}

def_EHelper(vwsubu_w) {
  arthimetic_instr(SUB, UNSIGNED, 1, 1, 0, s);
}

def_EHelper(vwsub_w) {
  arthimetic_instr(SUB, SIGNED, 1, 1, 0, s);
}

def_EHelper(vwmulu) {
  ARTHI_WIDE(MUL, UNSIGNED)
}

def_EHelper(vwmulsu) {
  ARTHI_WIDE(MULSU, UNSIGNED)
}

def_EHelper(vwmul) {
  ARTHI_WIDE(MUL, SIGNED)
}

def_EHelper(vwmaccu) {
  ARTHI_WIDE(MACC, UNSIGNED)
}

def_EHelper(vwmacc) {
  ARTHI_WIDE(MACC, SIGNED)
}

def_EHelper(vwmaccsu) {
  ARTHI_WIDE(MACCSU, UNSIGNED)
}

def_EHelper(vwmaccus) {
  ARTHI_WIDE(MACCUS, UNSIGNED)
}

def_EHelper(vfadd) {
  print_asm_template3(vfadd);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfredusum) {
  print_asm_template3(vfredusum);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfsub) {
  print_asm_template3(vfsub);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfredosum) {
  print_asm_template3(vfredosum);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmin) {
  print_asm_template3(vfmin);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfredmin) {
  print_asm_template3(vfredmin);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmax) {
  print_asm_template3(vfmax);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfredmax) {
  print_asm_template3(vfredmax);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfsgnj) {
  print_asm_template3(vfsgnj);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfsgnjn) {
  print_asm_template3(vfsgnjn);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfsgnjx) {
  print_asm_template3(vfsgnjx);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfslide1up) {
  print_asm_template3(vfslide1up);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfslide1down) {
  print_asm_template3(vfslide1down);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmvfs) {
  print_asm_template3(vfmvfs);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmvsf) {
  print_asm_template3(vfmvsf);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfcvt_xufv) {
  print_asm_template3(vfcvt_xufv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfcvt_xfv) {
  print_asm_template3(vfcvt_xfv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfcvt_fxuv) {
  print_asm_template3(vfcvt_fxuv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfcvt_fxv) {
  print_asm_template3(vfcvt_fxv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfcvt_rtz_xufv) {
  print_asm_template3(vfcvt_rtz_xufv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfcvt_rtz_xfv) {
  print_asm_template3(vfcvt_rtz_xfv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_xufv) {
  print_asm_template3(vfwcvt_xufv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_xfv) {
  print_asm_template3(vfwcvt_xfv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_fxuv) {
  print_asm_template3(vfwcvt_fxuv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_fxv) {
  print_asm_template3(vfwcvt_fxv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_ffv) {
  print_asm_template3(vfwcvt_ffv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_rtz_xufv) {
  print_asm_template3(vfwcvt_rtz_xufv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwcvt_rtz_xfv) {
  print_asm_template3(vfwcvt_rtz_xfv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_xufw) {
  print_asm_template3(vfncvt_xufw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_xfw) {
  print_asm_template3(vfncvt_xfw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_fxuw) {
  print_asm_template3(vfncvt_fxuw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_fxw) {
  print_asm_template3(vfncvt_fxw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_ffw) {
  print_asm_template3(vfncvt_ffw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_rod_ffw) {
  print_asm_template3(vfncvt_rod_ffw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_rtz_xufw) {
  print_asm_template3(vfncvt_rtz_xufw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfncvt_rtz_xfw) {
  print_asm_template3(vfncvt_rtz_xfw);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfsqrt_v) {
  print_asm_template3(vfsqrt_v);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfrsqrt7_v) {
  print_asm_template3(vfrsqrt7_v);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfrec7_v) {
  print_asm_template3(vfrec7_v);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfclass_v) {
  print_asm_template3(vfclass_v);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmerge) {
  print_asm_template3(vfmerge);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vmfeq) {
  print_asm_template3(vmfeq);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vmfle) {
  print_asm_template3(vmfle);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vmflt) {
  print_asm_template3(vmflt);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vmfne) {
  print_asm_template3(vmfne);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vmfgt) {
  print_asm_template3(vmfgt);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vmfge) {
  print_asm_template3(vmfge);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfdiv) {
  print_asm_template3(vfdiv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfrdiv) {
  print_asm_template3(vfrdiv);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmul) {
  print_asm_template3(vfmul);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfrsub) {
  print_asm_template3(vfrsub);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmadd) {
  print_asm_template3(vfmadd);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfnmadd) {
  print_asm_template3(vfnmadd);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmsub) {
  print_asm_template3(vfmsub);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfnmsub) {
  print_asm_template3(vfnmsub);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmacc) {
  print_asm_template3(vfmacc);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfnmacc) {
  print_asm_template3(vfnmacc);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfmsac) {
  print_asm_template3(vfmsac);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfnmsac) {
  print_asm_template3(vfnmsac);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwadd) {
  print_asm_template3(vfwadd);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwredusum) {
  print_asm_template3(vfwredusum);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwsub) {
  print_asm_template3(vfwsub);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwredosum) {
  print_asm_template3(vfwredosum);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwadd_w) {
  print_asm_template3(vfwadd_w);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwsub_w) {
  print_asm_template3(vfwsub_w);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwmul) {
  print_asm_template3(vfwmul);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwmacc) {
  print_asm_template3(vfwmacc);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwnmacc) {
  print_asm_template3(vfwnmacc);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwmsac) {
  print_asm_template3(vfwmsac);
  longjmp_raise_intr(EX_II);
}

def_EHelper(vfwnmsac) {
  print_asm_template3(vfwnmsac);
  longjmp_raise_intr(EX_II);
}

#endif // CONFIG_RVV