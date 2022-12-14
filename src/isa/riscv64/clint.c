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

#include <utils.h>
#include <device/alarm.h>
#include <device/map.h>
#include "local-include/csr.h"

#ifndef CONFIG_SHARE
#define CLINT_MTIMECMP (0x4000 / sizeof(clint_base[0]))
#define CLINT_MTIME    (0xBFF8 / sizeof(clint_base[0]))
#define TIMEBASE 10000000ul

static uint64_t *clint_base = NULL;
static uint64_t boot_time = 0;

void update_clint() {
#ifdef CONFIG_DETERMINISTIC
  clint_base[CLINT_MTIME] += TIMEBASE / 10000;
#else
  uint64_t now = get_time() - boot_time;
  clint_base[CLINT_MTIME] = TIMEBASE * now / 1000000;
#endif
  mip->mtip = (clint_base[CLINT_MTIME] >= clint_base[CLINT_MTIMECMP]);
}

uint64_t clint_uptime() {
  update_clint();
  return clint_base[CLINT_MTIME];
}

static void clint_io_handler(uint32_t offset, int len, bool is_write) {
  update_clint();
}

void init_clint() {
  clint_base = (uint64_t *)new_space(0x10000);
  add_mmio_map("clint", CONFIG_CLINT_MMIO, (uint8_t *)clint_base, 0x10000, clint_io_handler);
  IFNDEF(CONFIG_DETERMINISTIC, add_alarm_handle(update_clint));
  boot_time = get_time();
}
#endif
