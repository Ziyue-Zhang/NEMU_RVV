#include <cpu/exec.h>
#include "local-include/rtl.h"
#include "local-include/reg.h"
#include "local-include/decode.h"

typedef union {
  struct {
    uint8_t R_M		:3;
    uint8_t reg		:3;
    uint8_t mod		:2;
  };
  struct {
    uint8_t dont_care	:3;
    uint8_t opcode		:3;
  };
  uint8_t val;
} ModR_M;

typedef union {
  struct {
    uint8_t base	:3;
    uint8_t index	:3;
    uint8_t ss		:2;
  };
  uint8_t val;
} SIB;

static inline void load_addr(DecodeExecState *s, ModR_M *m, Operand *rm) {
  assert(m->mod != 3);

  sword_t disp = 0;
  int disp_size = 4;
  int base_reg = -1, index_reg = -1, scale = 0;

  if (m->R_M == R_ESP) {
    SIB sib;
    sib.val = instr_fetch(&s->seq_pc, 1);
    base_reg = sib.base;
    scale = sib.ss;

    if (sib.index != R_ESP) { index_reg = sib.index; }
  }
  else {
    /* no SIB */
    base_reg = m->R_M;
  }

  if (m->mod == 0) {
    if (base_reg == R_EBP) { base_reg = -1; }
    else { disp_size = 0; }
  }
  else if (m->mod == 1) { disp_size = 1; }

  if (disp_size != 0) {
    /* has disp */
    disp = instr_fetch(&s->seq_pc, disp_size);
    if (disp_size == 1) { disp = (int8_t)disp; }
  }

  s->isa.mbase = (base_reg != -1 ? &reg_l(base_reg) : rz);
  if (index_reg != -1) {
    rtl_shli(s, s1, &reg_l(index_reg), scale);
    rtl_add(s, &s->isa.mbr, s->isa.mbase, s1);
    s->isa.mbase = &s->isa.mbr;
  }
#ifndef __PA__
  if (s->isa.sreg_base != NULL) {
    rtl_add(s, &s->isa.mbr, s->isa.mbase, s->isa.sreg_base);
    s->isa.mbase = &s->isa.mbr;
  }
#endif
  s->isa.moff = disp;

#ifdef DEBUG
  char disp_buf[16];
  char base_buf[8];
  char index_buf[8];

  if (disp_size != 0) {
    /* has disp */
    sprintf(disp_buf, "%s%#x", (disp < 0 ? "-" : ""), (disp < 0 ? -disp : disp));
  }
  else { disp_buf[0] = '\0'; }

  if (base_reg == -1) { base_buf[0] = '\0'; }
  else { 
    sprintf(base_buf, "%%%s", reg_name(base_reg, 4));
  }

  if (index_reg == -1) { index_buf[0] = '\0'; }
  else { 
    sprintf(index_buf, ",%%%s,%d", reg_name(index_reg, 4), 1 << scale);
  }

  if (base_reg == -1 && index_reg == -1) {
    sprintf(rm->str, "%s", disp_buf);
  }
  else {
    sprintf(rm->str, "%s(%s%s)", disp_buf, base_buf, index_buf);
  }
#endif

  rm->type = OP_TYPE_MEM;
}

void read_ModR_M(DecodeExecState *s, Operand *rm, bool load_rm_val, Operand *reg, bool load_reg_val) {
  ModR_M m;
  m.val = instr_fetch(&s->seq_pc, 1);
  s->isa.ext_opcode = m.opcode;
  if (reg != NULL) operand_reg(s, reg, load_reg_val, m.reg, reg->width);
  if (m.mod == 3) operand_reg(s, rm, load_rm_val, m.R_M, rm->width);
  else {
#if !defined(__PA__) && defined(DIFF_TEST) && defined(__DIFF_REF_KVM__)
    if (((s->opcode == 0x80 || s->opcode == 0x81 || s->opcode == 0x83) && s->isa.ext_opcode == 7) ||
        (s->opcode == 0x1ba && s->isa.ext_opcode == 4)) {
      cpu.lock = 0; // fix with cmp and bt, since they do not write memory
    }
#endif
    load_addr(s, &m, rm);
    if (load_rm_val) rtl_lm(s, &rm->val, s->isa.mbase, s->isa.moff, rm->width);
    rm->preg = &rm->val;
  }
}

void read_F_ModR_M(DecodeExecState *s, Operand *rm, bool load_rm_val, Operand *reg, bool load_reg_val) {
  ModR_M m;
  m.val = s->isa.ext_opcode;
  if (reg != NULL) {
    //load st(0)
    operand_freg(s, reg, load_reg_val, 0);
  }
  if (m.mod == 3) operand_freg(s, rm, load_rm_val, m.R_M);
  else {
    load_addr(s, &m, rm);
    if (load_rm_val)rtl_lmf(s, &rm->fval, s->isa.mbase, s->isa.moff);
    rm->pfreg = &rm->fval;
    rm->type = OP_TYPE_MEM;
  }
}