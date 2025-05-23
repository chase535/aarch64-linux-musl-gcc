/* Generated automatically by gengenrtl from rtl.def.  */

#ifndef GCC_GENRTL_H
#define GCC_GENRTL_H

#include "statistics.h"

static inline rtx
init_rtx_fmt_0 (rtx rt, machine_mode mode)
{
  PUT_MODE_RAW (rt, mode);
  X0EXP (rt, 0) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_0_stat (RTX_CODE code, machine_mode mode MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_0 (rt, mode);
}

#define gen_rtx_fmt_0(c, m) \
  gen_rtx_fmt_0_stat ((c), (m) MEM_STAT_INFO)

#define alloca_rtx_fmt_0(c, m) \
  init_rtx_fmt_0 (rtx_alloca ((c)), (m))

static inline rtx
init_rtx_fmt_ee (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_ee_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ee (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_ee(c, m, arg0, arg1) \
  gen_rtx_fmt_ee_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_ee(c, m, arg0, arg1) \
  init_rtx_fmt_ee (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_ue (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_ue_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ue (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_ue(c, m, arg0, arg1) \
  gen_rtx_fmt_ue_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_ue(c, m, arg0, arg1) \
  init_rtx_fmt_ue (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_ie (rtx rt, machine_mode mode,
	int arg0,
	rtx arg1)
{
  PUT_MODE_RAW (rt, mode);
  XINT (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_ie_stat (RTX_CODE code, machine_mode mode,
	int arg0,
	rtx arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ie (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_ie(c, m, arg0, arg1) \
  gen_rtx_fmt_ie_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_ie(c, m, arg0, arg1) \
  init_rtx_fmt_ie (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_E (rtx rt, machine_mode mode,
	rtvec arg0)
{
  PUT_MODE_RAW (rt, mode);
  XVEC (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_E_stat (RTX_CODE code, machine_mode mode,
	rtvec arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_E (rt, mode, arg0);
}

#define gen_rtx_fmt_E(c, m, arg0) \
  gen_rtx_fmt_E_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_E(c, m, arg0) \
  init_rtx_fmt_E (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_i (rtx rt, machine_mode mode,
	int arg0)
{
  PUT_MODE_RAW (rt, mode);
  XINT (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_i_stat (RTX_CODE code, machine_mode mode,
	int arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_i (rt, mode, arg0);
}

#define gen_rtx_fmt_i(c, m, arg0) \
  gen_rtx_fmt_i_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_i(c, m, arg0) \
  init_rtx_fmt_i (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_uuBeLie (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3,
	location_t arg4,
	int arg5,
	rtx arg6)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XBBDEF (rt, 2) = arg2;
  XEXP (rt, 3) = arg3;
  XLOC (rt, 4) = arg4;
  XINT (rt, 5) = arg5;
  XEXP (rt, 6) = arg6;
  return rt;
}

static inline rtx
gen_rtx_fmt_uuBeLie_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3,
	location_t arg4,
	int arg5,
	rtx arg6 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_uuBeLie (rt, mode, arg0, arg1, arg2, arg3, arg4, arg5, arg6);
}

#define gen_rtx_fmt_uuBeLie(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6) \
  gen_rtx_fmt_uuBeLie_stat ((c), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6) MEM_STAT_INFO)

#define alloca_rtx_fmt_uuBeLie(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6) \
  init_rtx_fmt_uuBeLie (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6))

static inline rtx
init_rtx_fmt_uuBeLie0 (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3,
	location_t arg4,
	int arg5,
	rtx arg6)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XBBDEF (rt, 2) = arg2;
  XEXP (rt, 3) = arg3;
  XLOC (rt, 4) = arg4;
  XINT (rt, 5) = arg5;
  XEXP (rt, 6) = arg6;
  X0EXP (rt, 7) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_uuBeLie0_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3,
	location_t arg4,
	int arg5,
	rtx arg6 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_uuBeLie0 (rt, mode, arg0, arg1, arg2, arg3, arg4, arg5, arg6);
}

#define gen_rtx_fmt_uuBeLie0(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6) \
  gen_rtx_fmt_uuBeLie0_stat ((c), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6) MEM_STAT_INFO)

#define alloca_rtx_fmt_uuBeLie0(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6) \
  init_rtx_fmt_uuBeLie0 (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6))

static inline rtx
init_rtx_fmt_uuBeLiee (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3,
	location_t arg4,
	int arg5,
	rtx arg6,
	rtx arg7)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XBBDEF (rt, 2) = arg2;
  XEXP (rt, 3) = arg3;
  XLOC (rt, 4) = arg4;
  XINT (rt, 5) = arg5;
  XEXP (rt, 6) = arg6;
  XEXP (rt, 7) = arg7;
  return rt;
}

static inline rtx
gen_rtx_fmt_uuBeLiee_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3,
	location_t arg4,
	int arg5,
	rtx arg6,
	rtx arg7 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_uuBeLiee (rt, mode, arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7);
}

#define gen_rtx_fmt_uuBeLiee(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7) \
  gen_rtx_fmt_uuBeLiee_stat ((c), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6), (arg7) MEM_STAT_INFO)

#define alloca_rtx_fmt_uuBeLiee(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7) \
  init_rtx_fmt_uuBeLiee (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6), (arg7))

static inline rtx
init_rtx_fmt_uuBe0000 (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XBBDEF (rt, 2) = arg2;
  XEXP (rt, 3) = arg3;
  X0EXP (rt, 4) = NULL_RTX;
  X0EXP (rt, 5) = NULL_RTX;
  X0EXP (rt, 6) = NULL_RTX;
  X0EXP (rt, 7) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_uuBe0000_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	rtx arg3 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_uuBe0000 (rt, mode, arg0, arg1, arg2, arg3);
}

#define gen_rtx_fmt_uuBe0000(c, m, arg0, arg1, arg2, arg3) \
  gen_rtx_fmt_uuBe0000_stat ((c), (m), (arg0), (arg1), (arg2), (arg3) MEM_STAT_INFO)

#define alloca_rtx_fmt_uuBe0000(c, m, arg0, arg1, arg2, arg3) \
  init_rtx_fmt_uuBe0000 (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3))

static inline rtx
init_rtx_fmt_uu00000 (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  X0EXP (rt, 2) = NULL_RTX;
  X0EXP (rt, 3) = NULL_RTX;
  X0EXP (rt, 4) = NULL_RTX;
  X0EXP (rt, 5) = NULL_RTX;
  X0EXP (rt, 6) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_uu00000_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_uu00000 (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_uu00000(c, m, arg0, arg1) \
  gen_rtx_fmt_uu00000_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_uu00000(c, m, arg0, arg1) \
  init_rtx_fmt_uu00000 (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_uuB00is (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	int arg3,
	const char *arg4)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XBBDEF (rt, 2) = arg2;
  X0EXP (rt, 3) = NULL_RTX;
  X0EXP (rt, 4) = NULL_RTX;
  XINT (rt, 5) = arg3;
  XSTR (rt, 6) = arg4;
  return rt;
}

static inline rtx
gen_rtx_fmt_uuB00is_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1,
	basic_block arg2,
	int arg3,
	const char *arg4 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_uuB00is (rt, mode, arg0, arg1, arg2, arg3, arg4);
}

#define gen_rtx_fmt_uuB00is(c, m, arg0, arg1, arg2, arg3, arg4) \
  gen_rtx_fmt_uuB00is_stat ((c), (m), (arg0), (arg1), (arg2), (arg3), (arg4) MEM_STAT_INFO)

#define alloca_rtx_fmt_uuB00is(c, m, arg0, arg1, arg2, arg3, arg4) \
  init_rtx_fmt_uuB00is (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3), (arg4))

static inline rtx
init_rtx_fmt_sL (rtx rt, machine_mode mode,
	const char *arg0,
	location_t arg1)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XLOC (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_sL_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	location_t arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_sL (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_sL(c, m, arg0, arg1) \
  gen_rtx_fmt_sL_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_sL(c, m, arg0, arg1) \
  init_rtx_fmt_sL (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_ssiEEEL (rtx rt, machine_mode mode,
	const char *arg0,
	const char *arg1,
	int arg2,
	rtvec arg3,
	rtvec arg4,
	rtvec arg5,
	location_t arg6)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  XINT (rt, 2) = arg2;
  XVEC (rt, 3) = arg3;
  XVEC (rt, 4) = arg4;
  XVEC (rt, 5) = arg5;
  XLOC (rt, 6) = arg6;
  return rt;
}

static inline rtx
gen_rtx_fmt_ssiEEEL_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	const char *arg1,
	int arg2,
	rtvec arg3,
	rtvec arg4,
	rtvec arg5,
	location_t arg6 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ssiEEEL (rt, mode, arg0, arg1, arg2, arg3, arg4, arg5, arg6);
}

#define gen_rtx_fmt_ssiEEEL(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6) \
  gen_rtx_fmt_ssiEEEL_stat ((c), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6) MEM_STAT_INFO)

#define alloca_rtx_fmt_ssiEEEL(c, m, arg0, arg1, arg2, arg3, arg4, arg5, arg6) \
  init_rtx_fmt_ssiEEEL (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3), (arg4), (arg5), (arg6))

static inline rtx
init_rtx_fmt_Ei (rtx rt, machine_mode mode,
	rtvec arg0,
	int arg1)
{
  PUT_MODE_RAW (rt, mode);
  XVEC (rt, 0) = arg0;
  XINT (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_Ei_stat (RTX_CODE code, machine_mode mode,
	rtvec arg0,
	int arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_Ei (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_Ei(c, m, arg0, arg1) \
  gen_rtx_fmt_Ei_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_Ei(c, m, arg0, arg1) \
  init_rtx_fmt_Ei (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_eEee0 (rtx rt, machine_mode mode,
	rtx arg0,
	rtvec arg1,
	rtx arg2,
	rtx arg3)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XVEC (rt, 1) = arg1;
  XEXP (rt, 2) = arg2;
  XEXP (rt, 3) = arg3;
  X0EXP (rt, 4) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_eEee0_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtvec arg1,
	rtx arg2,
	rtx arg3 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_eEee0 (rt, mode, arg0, arg1, arg2, arg3);
}

#define gen_rtx_fmt_eEee0(c, m, arg0, arg1, arg2, arg3) \
  gen_rtx_fmt_eEee0_stat ((c), (m), (arg0), (arg1), (arg2), (arg3) MEM_STAT_INFO)

#define alloca_rtx_fmt_eEee0(c, m, arg0, arg1, arg2, arg3) \
  init_rtx_fmt_eEee0 (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3))

static inline rtx
init_rtx_fmt_eee (rtx rt, machine_mode mode,
	rtx arg0,
	rtx arg1,
	rtx arg2)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XEXP (rt, 2) = arg2;
  return rt;
}

static inline rtx
gen_rtx_fmt_eee_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtx arg1,
	rtx arg2 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_eee (rt, mode, arg0, arg1, arg2);
}

#define gen_rtx_fmt_eee(c, m, arg0, arg1, arg2) \
  gen_rtx_fmt_eee_stat ((c), (m), (arg0), (arg1), (arg2) MEM_STAT_INFO)

#define alloca_rtx_fmt_eee(c, m, arg0, arg1, arg2) \
  init_rtx_fmt_eee (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2))

static inline rtx
init_rtx_fmt_e (rtx rt, machine_mode mode,
	rtx arg0)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_e_stat (RTX_CODE code, machine_mode mode,
	rtx arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_e (rt, mode, arg0);
}

#define gen_rtx_fmt_e(c, m, arg0) \
  gen_rtx_fmt_e_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_e(c, m, arg0) \
  init_rtx_fmt_e (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_ (rtx rt, machine_mode mode)
{
  PUT_MODE_RAW (rt, mode);
  return rt;
}

static inline rtx
gen_rtx_fmt__stat (RTX_CODE code, machine_mode mode MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ (rt, mode);
}

#define gen_rtx_fmt_(c, m) \
  gen_rtx_fmt__stat ((c), (m) MEM_STAT_INFO)

#define alloca_rtx_fmt_(c, m) \
  init_rtx_fmt_ (rtx_alloca ((c)), (m))

static inline rtx
init_rtx_fmt_w (rtx rt, machine_mode mode,
	HOST_WIDE_INT arg0)
{
  PUT_MODE_RAW (rt, mode);
  XWINT (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_w_stat (RTX_CODE code, machine_mode mode,
	HOST_WIDE_INT arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_w (rt, mode, arg0);
}

#define gen_rtx_fmt_w(c, m, arg0) \
  gen_rtx_fmt_w_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_w(c, m, arg0) \
  init_rtx_fmt_w (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_www (rtx rt, machine_mode mode,
	HOST_WIDE_INT arg0,
	HOST_WIDE_INT arg1,
	HOST_WIDE_INT arg2)
{
  PUT_MODE_RAW (rt, mode);
  XWINT (rt, 0) = arg0;
  XWINT (rt, 1) = arg1;
  XWINT (rt, 2) = arg2;
  return rt;
}

static inline rtx
gen_rtx_fmt_www_stat (RTX_CODE code, machine_mode mode,
	HOST_WIDE_INT arg0,
	HOST_WIDE_INT arg1,
	HOST_WIDE_INT arg2 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_www (rt, mode, arg0, arg1, arg2);
}

#define gen_rtx_fmt_www(c, m, arg0, arg1, arg2) \
  gen_rtx_fmt_www_stat ((c), (m), (arg0), (arg1), (arg2) MEM_STAT_INFO)

#define alloca_rtx_fmt_www(c, m, arg0, arg1, arg2) \
  init_rtx_fmt_www (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2))

static inline rtx
init_rtx_fmt_s (rtx rt, machine_mode mode,
	const char *arg0)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_s_stat (RTX_CODE code, machine_mode mode,
	const char *arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_s (rt, mode, arg0);
}

#define gen_rtx_fmt_s(c, m, arg0) \
  gen_rtx_fmt_s_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_s(c, m, arg0) \
  init_rtx_fmt_s (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_ep (rtx rt, machine_mode mode,
	rtx arg0,
	poly_uint16 arg1)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  SUBREG_BYTE (rt) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_ep_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	poly_uint16 arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ep (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_ep(c, m, arg0, arg1) \
  gen_rtx_fmt_ep_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_ep(c, m, arg0, arg1) \
  init_rtx_fmt_ep (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_e0 (rtx rt, machine_mode mode,
	rtx arg0)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  X0EXP (rt, 1) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_e0_stat (RTX_CODE code, machine_mode mode,
	rtx arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_e0 (rt, mode, arg0);
}

#define gen_rtx_fmt_e0(c, m, arg0) \
  gen_rtx_fmt_e0_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_e0(c, m, arg0) \
  init_rtx_fmt_e0 (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_u (rtx rt, machine_mode mode,
	rtx arg0)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_u_stat (RTX_CODE code, machine_mode mode,
	rtx arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_u (rt, mode, arg0);
}

#define gen_rtx_fmt_u(c, m, arg0) \
  gen_rtx_fmt_u_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_u(c, m, arg0) \
  init_rtx_fmt_u (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_s0 (rtx rt, machine_mode mode,
	const char *arg0)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  X0EXP (rt, 1) = NULL_RTX;
  return rt;
}

static inline rtx
gen_rtx_fmt_s0_stat (RTX_CODE code, machine_mode mode,
	const char *arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_s0 (rt, mode, arg0);
}

#define gen_rtx_fmt_s0(c, m, arg0) \
  gen_rtx_fmt_s0_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_s0(c, m, arg0) \
  init_rtx_fmt_s0 (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_te (rtx rt, machine_mode mode,
	tree arg0,
	rtx arg1)
{
  PUT_MODE_RAW (rt, mode);
  XTREE (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_te_stat (RTX_CODE code, machine_mode mode,
	tree arg0,
	rtx arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_te (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_te(c, m, arg0, arg1) \
  gen_rtx_fmt_te_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_te(c, m, arg0, arg1) \
  init_rtx_fmt_te (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_t (rtx rt, machine_mode mode,
	tree arg0)
{
  PUT_MODE_RAW (rt, mode);
  XTREE (rt, 0) = arg0;
  return rt;
}

static inline rtx
gen_rtx_fmt_t_stat (RTX_CODE code, machine_mode mode,
	tree arg0 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_t (rt, mode, arg0);
}

#define gen_rtx_fmt_t(c, m, arg0) \
  gen_rtx_fmt_t_stat ((c), (m), (arg0) MEM_STAT_INFO)

#define alloca_rtx_fmt_t(c, m, arg0) \
  init_rtx_fmt_t (rtx_alloca ((c)), (m), (arg0))

static inline rtx
init_rtx_fmt_iss (rtx rt, machine_mode mode,
	int arg0,
	const char *arg1,
	const char *arg2)
{
  PUT_MODE_RAW (rt, mode);
  XINT (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  XSTR (rt, 2) = arg2;
  return rt;
}

static inline rtx
gen_rtx_fmt_iss_stat (RTX_CODE code, machine_mode mode,
	int arg0,
	const char *arg1,
	const char *arg2 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_iss (rt, mode, arg0, arg1, arg2);
}

#define gen_rtx_fmt_iss(c, m, arg0, arg1, arg2) \
  gen_rtx_fmt_iss_stat ((c), (m), (arg0), (arg1), (arg2) MEM_STAT_INFO)

#define alloca_rtx_fmt_iss(c, m, arg0, arg1, arg2) \
  init_rtx_fmt_iss (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2))

static inline rtx
init_rtx_fmt_is (rtx rt, machine_mode mode,
	int arg0,
	const char *arg1)
{
  PUT_MODE_RAW (rt, mode);
  XINT (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_is_stat (RTX_CODE code, machine_mode mode,
	int arg0,
	const char *arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_is (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_is(c, m, arg0, arg1) \
  gen_rtx_fmt_is_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_is(c, m, arg0, arg1) \
  init_rtx_fmt_is (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_isE (rtx rt, machine_mode mode,
	int arg0,
	const char *arg1,
	rtvec arg2)
{
  PUT_MODE_RAW (rt, mode);
  XINT (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  XVEC (rt, 2) = arg2;
  return rt;
}

static inline rtx
gen_rtx_fmt_isE_stat (RTX_CODE code, machine_mode mode,
	int arg0,
	const char *arg1,
	rtvec arg2 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_isE (rt, mode, arg0, arg1, arg2);
}

#define gen_rtx_fmt_isE(c, m, arg0, arg1, arg2) \
  gen_rtx_fmt_isE_stat ((c), (m), (arg0), (arg1), (arg2) MEM_STAT_INFO)

#define alloca_rtx_fmt_isE(c, m, arg0, arg1, arg2) \
  init_rtx_fmt_isE (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2))

static inline rtx
init_rtx_fmt_iE (rtx rt, machine_mode mode,
	int arg0,
	rtvec arg1)
{
  PUT_MODE_RAW (rt, mode);
  XINT (rt, 0) = arg0;
  XVEC (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_iE_stat (RTX_CODE code, machine_mode mode,
	int arg0,
	rtvec arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_iE (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_iE(c, m, arg0, arg1) \
  gen_rtx_fmt_iE_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_iE(c, m, arg0, arg1) \
  init_rtx_fmt_iE (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_ss (rtx rt, machine_mode mode,
	const char *arg0,
	const char *arg1)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_ss_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	const char *arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ss (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_ss(c, m, arg0, arg1) \
  gen_rtx_fmt_ss_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_ss(c, m, arg0, arg1) \
  init_rtx_fmt_ss (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_eE (rtx rt, machine_mode mode,
	rtx arg0,
	rtvec arg1)
{
  PUT_MODE_RAW (rt, mode);
  XEXP (rt, 0) = arg0;
  XVEC (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_eE_stat (RTX_CODE code, machine_mode mode,
	rtx arg0,
	rtvec arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_eE (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_eE(c, m, arg0, arg1) \
  gen_rtx_fmt_eE_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_eE(c, m, arg0, arg1) \
  init_rtx_fmt_eE (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_ses (rtx rt, machine_mode mode,
	const char *arg0,
	rtx arg1,
	const char *arg2)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  XSTR (rt, 2) = arg2;
  return rt;
}

static inline rtx
gen_rtx_fmt_ses_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	rtx arg1,
	const char *arg2 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ses (rt, mode, arg0, arg1, arg2);
}

#define gen_rtx_fmt_ses(c, m, arg0, arg1, arg2) \
  gen_rtx_fmt_ses_stat ((c), (m), (arg0), (arg1), (arg2) MEM_STAT_INFO)

#define alloca_rtx_fmt_ses(c, m, arg0, arg1, arg2) \
  init_rtx_fmt_ses (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2))

static inline rtx
init_rtx_fmt_sse (rtx rt, machine_mode mode,
	const char *arg0,
	const char *arg1,
	rtx arg2)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  XEXP (rt, 2) = arg2;
  return rt;
}

static inline rtx
gen_rtx_fmt_sse_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	const char *arg1,
	rtx arg2 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_sse (rt, mode, arg0, arg1, arg2);
}

#define gen_rtx_fmt_sse(c, m, arg0, arg1, arg2) \
  gen_rtx_fmt_sse_stat ((c), (m), (arg0), (arg1), (arg2) MEM_STAT_INFO)

#define alloca_rtx_fmt_sse(c, m, arg0, arg1, arg2) \
  init_rtx_fmt_sse (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2))

static inline rtx
init_rtx_fmt_sies (rtx rt, machine_mode mode,
	const char *arg0,
	int arg1,
	rtx arg2,
	const char *arg3)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XINT (rt, 1) = arg1;
  XEXP (rt, 2) = arg2;
  XSTR (rt, 3) = arg3;
  return rt;
}

static inline rtx
gen_rtx_fmt_sies_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	int arg1,
	rtx arg2,
	const char *arg3 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_sies (rt, mode, arg0, arg1, arg2, arg3);
}

#define gen_rtx_fmt_sies(c, m, arg0, arg1, arg2, arg3) \
  gen_rtx_fmt_sies_stat ((c), (m), (arg0), (arg1), (arg2), (arg3) MEM_STAT_INFO)

#define alloca_rtx_fmt_sies(c, m, arg0, arg1, arg2, arg3) \
  init_rtx_fmt_sies (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3))

static inline rtx
init_rtx_fmt_sE (rtx rt, machine_mode mode,
	const char *arg0,
	rtvec arg1)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XVEC (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_sE_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	rtvec arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_sE (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_sE(c, m, arg0, arg1) \
  gen_rtx_fmt_sE_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_sE(c, m, arg0, arg1) \
  init_rtx_fmt_sE (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_ww (rtx rt, machine_mode mode,
	HOST_WIDE_INT arg0,
	HOST_WIDE_INT arg1)
{
  PUT_MODE_RAW (rt, mode);
  XWINT (rt, 0) = arg0;
  XWINT (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_ww_stat (RTX_CODE code, machine_mode mode,
	HOST_WIDE_INT arg0,
	HOST_WIDE_INT arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ww (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_ww(c, m, arg0, arg1) \
  gen_rtx_fmt_ww_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_ww(c, m, arg0, arg1) \
  init_rtx_fmt_ww (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_Ee (rtx rt, machine_mode mode,
	rtvec arg0,
	rtx arg1)
{
  PUT_MODE_RAW (rt, mode);
  XVEC (rt, 0) = arg0;
  XEXP (rt, 1) = arg1;
  return rt;
}

static inline rtx
gen_rtx_fmt_Ee_stat (RTX_CODE code, machine_mode mode,
	rtvec arg0,
	rtx arg1 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_Ee (rt, mode, arg0, arg1);
}

#define gen_rtx_fmt_Ee(c, m, arg0, arg1) \
  gen_rtx_fmt_Ee_stat ((c), (m), (arg0), (arg1) MEM_STAT_INFO)

#define alloca_rtx_fmt_Ee(c, m, arg0, arg1) \
  init_rtx_fmt_Ee (rtx_alloca ((c)), (m), (arg0), (arg1))

static inline rtx
init_rtx_fmt_sEsE (rtx rt, machine_mode mode,
	const char *arg0,
	rtvec arg1,
	const char *arg2,
	rtvec arg3)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XVEC (rt, 1) = arg1;
  XSTR (rt, 2) = arg2;
  XVEC (rt, 3) = arg3;
  return rt;
}

static inline rtx
gen_rtx_fmt_sEsE_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	rtvec arg1,
	const char *arg2,
	rtvec arg3 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_sEsE (rt, mode, arg0, arg1, arg2, arg3);
}

#define gen_rtx_fmt_sEsE(c, m, arg0, arg1, arg2, arg3) \
  gen_rtx_fmt_sEsE_stat ((c), (m), (arg0), (arg1), (arg2), (arg3) MEM_STAT_INFO)

#define alloca_rtx_fmt_sEsE(c, m, arg0, arg1, arg2, arg3) \
  init_rtx_fmt_sEsE (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3))

static inline rtx
init_rtx_fmt_ssss (rtx rt, machine_mode mode,
	const char *arg0,
	const char *arg1,
	const char *arg2,
	const char *arg3)
{
  PUT_MODE_RAW (rt, mode);
  XSTR (rt, 0) = arg0;
  XSTR (rt, 1) = arg1;
  XSTR (rt, 2) = arg2;
  XSTR (rt, 3) = arg3;
  return rt;
}

static inline rtx
gen_rtx_fmt_ssss_stat (RTX_CODE code, machine_mode mode,
	const char *arg0,
	const char *arg1,
	const char *arg2,
	const char *arg3 MEM_STAT_DECL)
{
  rtx rt;

  rt = rtx_alloc (code PASS_MEM_STAT);
  return init_rtx_fmt_ssss (rt, mode, arg0, arg1, arg2, arg3);
}

#define gen_rtx_fmt_ssss(c, m, arg0, arg1, arg2, arg3) \
  gen_rtx_fmt_ssss_stat ((c), (m), (arg0), (arg1), (arg2), (arg3) MEM_STAT_INFO)

#define alloca_rtx_fmt_ssss(c, m, arg0, arg1, arg2, arg3) \
  init_rtx_fmt_ssss (rtx_alloca ((c)), (m), (arg0), (arg1), (arg2), (arg3))


#define gen_rtx_VALUE(MODE) \
  gen_rtx_fmt_0 (VALUE, (MODE))
#define gen_rtx_DEBUG_EXPR(MODE) \
  gen_rtx_fmt_0 (DEBUG_EXPR, (MODE))
#define gen_rtx_raw_EXPR_LIST(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (EXPR_LIST, (MODE), (ARG0), (ARG1))
#define gen_rtx_raw_INSN_LIST(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ue (INSN_LIST, (MODE), (ARG0), (ARG1))
#define gen_rtx_INT_LIST(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ie (INT_LIST, (MODE), (ARG0), (ARG1))
#define gen_rtx_SEQUENCE(MODE, ARG0) \
  gen_rtx_fmt_E (SEQUENCE, (MODE), (ARG0))
#define gen_rtx_ADDRESS(MODE, ARG0) \
  gen_rtx_fmt_i (ADDRESS, (MODE), (ARG0))
#define gen_rtx_DEBUG_INSN(MODE, ARG0, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6) \
  gen_rtx_fmt_uuBeLie (DEBUG_INSN, (MODE), (ARG0), (ARG1), (ARG2), (ARG3), (ARG4), (ARG5), (ARG6))
#define gen_rtx_raw_INSN(MODE, ARG0, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6) \
  gen_rtx_fmt_uuBeLie (INSN, (MODE), (ARG0), (ARG1), (ARG2), (ARG3), (ARG4), (ARG5), (ARG6))
#define gen_rtx_JUMP_INSN(MODE, ARG0, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6) \
  gen_rtx_fmt_uuBeLie0 (JUMP_INSN, (MODE), (ARG0), (ARG1), (ARG2), (ARG3), (ARG4), (ARG5), (ARG6))
#define gen_rtx_CALL_INSN(MODE, ARG0, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6, ARG7) \
  gen_rtx_fmt_uuBeLiee (CALL_INSN, (MODE), (ARG0), (ARG1), (ARG2), (ARG3), (ARG4), (ARG5), (ARG6), (ARG7))
#define gen_rtx_JUMP_TABLE_DATA(MODE, ARG0, ARG1, ARG2, ARG3) \
  gen_rtx_fmt_uuBe0000 (JUMP_TABLE_DATA, (MODE), (ARG0), (ARG1), (ARG2), (ARG3))
#define gen_rtx_BARRIER(MODE, ARG0, ARG1) \
  gen_rtx_fmt_uu00000 (BARRIER, (MODE), (ARG0), (ARG1))
#define gen_rtx_CODE_LABEL(MODE, ARG0, ARG1, ARG2, ARG3, ARG4) \
  gen_rtx_fmt_uuB00is (CODE_LABEL, (MODE), (ARG0), (ARG1), (ARG2), (ARG3), (ARG4))
#define gen_rtx_COND_EXEC(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (COND_EXEC, (MODE), (ARG0), (ARG1))
#define gen_rtx_PARALLEL(MODE, ARG0) \
  gen_rtx_fmt_E (PARALLEL, (MODE), (ARG0))
#define gen_rtx_ASM_INPUT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_sL (ASM_INPUT, (MODE), (ARG0), (ARG1))
#define gen_rtx_ASM_OPERANDS(MODE, ARG0, ARG1, ARG2, ARG3, ARG4, ARG5, ARG6) \
  gen_rtx_fmt_ssiEEEL (ASM_OPERANDS, (MODE), (ARG0), (ARG1), (ARG2), (ARG3), (ARG4), (ARG5), (ARG6))
#define gen_rtx_UNSPEC(MODE, ARG0, ARG1) \
  gen_rtx_fmt_Ei (UNSPEC, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNSPEC_VOLATILE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_Ei (UNSPEC_VOLATILE, (MODE), (ARG0), (ARG1))
#define gen_rtx_ADDR_VEC(MODE, ARG0) \
  gen_rtx_fmt_E (ADDR_VEC, (MODE), (ARG0))
#define gen_rtx_ADDR_DIFF_VEC(MODE, ARG0, ARG1, ARG2, ARG3) \
  gen_rtx_fmt_eEee0 (ADDR_DIFF_VEC, (MODE), (ARG0), (ARG1), (ARG2), (ARG3))
#define gen_rtx_PREFETCH(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_eee (PREFETCH, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_SET(ARG0, ARG1) \
  gen_rtx_fmt_ee (SET, VOIDmode, (ARG0), (ARG1))
#define gen_rtx_USE(MODE, ARG0) \
  gen_rtx_fmt_e (USE, (MODE), (ARG0))
#define gen_rtx_CLOBBER(MODE, ARG0) \
  gen_rtx_fmt_e (CLOBBER, (MODE), (ARG0))
#define gen_rtx_CALL(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (CALL, (MODE), (ARG0), (ARG1))
#define gen_rtx_raw_RETURN(MODE) \
  gen_rtx_fmt_ (RETURN, (MODE))
#define gen_rtx_raw_SIMPLE_RETURN(MODE) \
  gen_rtx_fmt_ (SIMPLE_RETURN, (MODE))
#define gen_rtx_EH_RETURN(MODE) \
  gen_rtx_fmt_ (EH_RETURN, (MODE))
#define gen_rtx_TRAP_IF(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (TRAP_IF, (MODE), (ARG0), (ARG1))
#define gen_rtx_raw_CONST_INT(MODE, ARG0) \
  gen_rtx_fmt_w (CONST_INT, (MODE), (ARG0))
#define gen_rtx_raw_CONST_VECTOR(MODE, ARG0) \
  gen_rtx_fmt_E (CONST_VECTOR, (MODE), (ARG0))
#define gen_rtx_CONST_STRING(MODE, ARG0) \
  gen_rtx_fmt_s (CONST_STRING, (MODE), (ARG0))
#define gen_rtx_CONST(MODE, ARG0) \
  gen_rtx_fmt_e (CONST, (MODE), (ARG0))
#define gen_rtx_raw_PC(MODE) \
  gen_rtx_fmt_ (PC, (MODE))
#define gen_rtx_SCRATCH(MODE) \
  gen_rtx_fmt_ (SCRATCH, (MODE))
#define gen_rtx_raw_SUBREG(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ep (SUBREG, (MODE), (ARG0), (ARG1))
#define gen_rtx_STRICT_LOW_PART(MODE, ARG0) \
  gen_rtx_fmt_e (STRICT_LOW_PART, (MODE), (ARG0))
#define gen_rtx_CONCAT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (CONCAT, (MODE), (ARG0), (ARG1))
#define gen_rtx_CONCATN(MODE, ARG0) \
  gen_rtx_fmt_E (CONCATN, (MODE), (ARG0))
#define gen_rtx_raw_MEM(MODE, ARG0) \
  gen_rtx_fmt_e0 (MEM, (MODE), (ARG0))
#define gen_rtx_LABEL_REF(MODE, ARG0) \
  gen_rtx_fmt_u (LABEL_REF, (MODE), (ARG0))
#define gen_rtx_SYMBOL_REF(MODE, ARG0) \
  gen_rtx_fmt_s0 (SYMBOL_REF, (MODE), (ARG0))
#define gen_rtx_IF_THEN_ELSE(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_eee (IF_THEN_ELSE, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_COMPARE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (COMPARE, (MODE), (ARG0), (ARG1))
#define gen_rtx_PLUS(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (PLUS, (MODE), (ARG0), (ARG1))
#define gen_rtx_MINUS(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (MINUS, (MODE), (ARG0), (ARG1))
#define gen_rtx_NEG(MODE, ARG0) \
  gen_rtx_fmt_e (NEG, (MODE), (ARG0))
#define gen_rtx_MULT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (MULT, (MODE), (ARG0), (ARG1))
#define gen_rtx_SS_MULT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SS_MULT, (MODE), (ARG0), (ARG1))
#define gen_rtx_US_MULT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (US_MULT, (MODE), (ARG0), (ARG1))
#define gen_rtx_SMUL_HIGHPART(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SMUL_HIGHPART, (MODE), (ARG0), (ARG1))
#define gen_rtx_UMUL_HIGHPART(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UMUL_HIGHPART, (MODE), (ARG0), (ARG1))
#define gen_rtx_DIV(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (DIV, (MODE), (ARG0), (ARG1))
#define gen_rtx_SS_DIV(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SS_DIV, (MODE), (ARG0), (ARG1))
#define gen_rtx_US_DIV(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (US_DIV, (MODE), (ARG0), (ARG1))
#define gen_rtx_MOD(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (MOD, (MODE), (ARG0), (ARG1))
#define gen_rtx_UDIV(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UDIV, (MODE), (ARG0), (ARG1))
#define gen_rtx_UMOD(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UMOD, (MODE), (ARG0), (ARG1))
#define gen_rtx_AND(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (AND, (MODE), (ARG0), (ARG1))
#define gen_rtx_IOR(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (IOR, (MODE), (ARG0), (ARG1))
#define gen_rtx_XOR(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (XOR, (MODE), (ARG0), (ARG1))
#define gen_rtx_NOT(MODE, ARG0) \
  gen_rtx_fmt_e (NOT, (MODE), (ARG0))
#define gen_rtx_ASHIFT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (ASHIFT, (MODE), (ARG0), (ARG1))
#define gen_rtx_ROTATE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (ROTATE, (MODE), (ARG0), (ARG1))
#define gen_rtx_ASHIFTRT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (ASHIFTRT, (MODE), (ARG0), (ARG1))
#define gen_rtx_LSHIFTRT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LSHIFTRT, (MODE), (ARG0), (ARG1))
#define gen_rtx_ROTATERT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (ROTATERT, (MODE), (ARG0), (ARG1))
#define gen_rtx_SMIN(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SMIN, (MODE), (ARG0), (ARG1))
#define gen_rtx_SMAX(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SMAX, (MODE), (ARG0), (ARG1))
#define gen_rtx_UMIN(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UMIN, (MODE), (ARG0), (ARG1))
#define gen_rtx_UMAX(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UMAX, (MODE), (ARG0), (ARG1))
#define gen_rtx_PRE_DEC(MODE, ARG0) \
  gen_rtx_fmt_e (PRE_DEC, (MODE), (ARG0))
#define gen_rtx_PRE_INC(MODE, ARG0) \
  gen_rtx_fmt_e (PRE_INC, (MODE), (ARG0))
#define gen_rtx_POST_DEC(MODE, ARG0) \
  gen_rtx_fmt_e (POST_DEC, (MODE), (ARG0))
#define gen_rtx_POST_INC(MODE, ARG0) \
  gen_rtx_fmt_e (POST_INC, (MODE), (ARG0))
#define gen_rtx_PRE_MODIFY(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (PRE_MODIFY, (MODE), (ARG0), (ARG1))
#define gen_rtx_POST_MODIFY(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (POST_MODIFY, (MODE), (ARG0), (ARG1))
#define gen_rtx_NE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (NE, (MODE), (ARG0), (ARG1))
#define gen_rtx_EQ(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (EQ, (MODE), (ARG0), (ARG1))
#define gen_rtx_GE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (GE, (MODE), (ARG0), (ARG1))
#define gen_rtx_GT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (GT, (MODE), (ARG0), (ARG1))
#define gen_rtx_LE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LE, (MODE), (ARG0), (ARG1))
#define gen_rtx_LT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LT, (MODE), (ARG0), (ARG1))
#define gen_rtx_LTGT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LTGT, (MODE), (ARG0), (ARG1))
#define gen_rtx_GEU(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (GEU, (MODE), (ARG0), (ARG1))
#define gen_rtx_GTU(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (GTU, (MODE), (ARG0), (ARG1))
#define gen_rtx_LEU(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LEU, (MODE), (ARG0), (ARG1))
#define gen_rtx_LTU(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LTU, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNORDERED(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UNORDERED, (MODE), (ARG0), (ARG1))
#define gen_rtx_ORDERED(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (ORDERED, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNEQ(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UNEQ, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNGE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UNGE, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNGT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UNGT, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNLE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UNLE, (MODE), (ARG0), (ARG1))
#define gen_rtx_UNLT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (UNLT, (MODE), (ARG0), (ARG1))
#define gen_rtx_SIGN_EXTEND(MODE, ARG0) \
  gen_rtx_fmt_e (SIGN_EXTEND, (MODE), (ARG0))
#define gen_rtx_ZERO_EXTEND(MODE, ARG0) \
  gen_rtx_fmt_e (ZERO_EXTEND, (MODE), (ARG0))
#define gen_rtx_TRUNCATE(MODE, ARG0) \
  gen_rtx_fmt_e (TRUNCATE, (MODE), (ARG0))
#define gen_rtx_FLOAT_EXTEND(MODE, ARG0) \
  gen_rtx_fmt_e (FLOAT_EXTEND, (MODE), (ARG0))
#define gen_rtx_FLOAT_TRUNCATE(MODE, ARG0) \
  gen_rtx_fmt_e (FLOAT_TRUNCATE, (MODE), (ARG0))
#define gen_rtx_FLOAT(MODE, ARG0) \
  gen_rtx_fmt_e (FLOAT, (MODE), (ARG0))
#define gen_rtx_FIX(MODE, ARG0) \
  gen_rtx_fmt_e (FIX, (MODE), (ARG0))
#define gen_rtx_UNSIGNED_FLOAT(MODE, ARG0) \
  gen_rtx_fmt_e (UNSIGNED_FLOAT, (MODE), (ARG0))
#define gen_rtx_UNSIGNED_FIX(MODE, ARG0) \
  gen_rtx_fmt_e (UNSIGNED_FIX, (MODE), (ARG0))
#define gen_rtx_FRACT_CONVERT(MODE, ARG0) \
  gen_rtx_fmt_e (FRACT_CONVERT, (MODE), (ARG0))
#define gen_rtx_UNSIGNED_FRACT_CONVERT(MODE, ARG0) \
  gen_rtx_fmt_e (UNSIGNED_FRACT_CONVERT, (MODE), (ARG0))
#define gen_rtx_SAT_FRACT(MODE, ARG0) \
  gen_rtx_fmt_e (SAT_FRACT, (MODE), (ARG0))
#define gen_rtx_UNSIGNED_SAT_FRACT(MODE, ARG0) \
  gen_rtx_fmt_e (UNSIGNED_SAT_FRACT, (MODE), (ARG0))
#define gen_rtx_ABS(MODE, ARG0) \
  gen_rtx_fmt_e (ABS, (MODE), (ARG0))
#define gen_rtx_SQRT(MODE, ARG0) \
  gen_rtx_fmt_e (SQRT, (MODE), (ARG0))
#define gen_rtx_BSWAP(MODE, ARG0) \
  gen_rtx_fmt_e (BSWAP, (MODE), (ARG0))
#define gen_rtx_FFS(MODE, ARG0) \
  gen_rtx_fmt_e (FFS, (MODE), (ARG0))
#define gen_rtx_CLRSB(MODE, ARG0) \
  gen_rtx_fmt_e (CLRSB, (MODE), (ARG0))
#define gen_rtx_CLZ(MODE, ARG0) \
  gen_rtx_fmt_e (CLZ, (MODE), (ARG0))
#define gen_rtx_CTZ(MODE, ARG0) \
  gen_rtx_fmt_e (CTZ, (MODE), (ARG0))
#define gen_rtx_POPCOUNT(MODE, ARG0) \
  gen_rtx_fmt_e (POPCOUNT, (MODE), (ARG0))
#define gen_rtx_PARITY(MODE, ARG0) \
  gen_rtx_fmt_e (PARITY, (MODE), (ARG0))
#define gen_rtx_BITREVERSE(MODE, ARG0) \
  gen_rtx_fmt_e (BITREVERSE, (MODE), (ARG0))
#define gen_rtx_SIGN_EXTRACT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_eee (SIGN_EXTRACT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_ZERO_EXTRACT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_eee (ZERO_EXTRACT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_HIGH(MODE, ARG0) \
  gen_rtx_fmt_e (HIGH, (MODE), (ARG0))
#define gen_rtx_LO_SUM(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (LO_SUM, (MODE), (ARG0), (ARG1))
#define gen_rtx_VEC_MERGE(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_eee (VEC_MERGE, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_VEC_SELECT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (VEC_SELECT, (MODE), (ARG0), (ARG1))
#define gen_rtx_VEC_CONCAT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (VEC_CONCAT, (MODE), (ARG0), (ARG1))
#define gen_rtx_VEC_DUPLICATE(MODE, ARG0) \
  gen_rtx_fmt_e (VEC_DUPLICATE, (MODE), (ARG0))
#define gen_rtx_VEC_SERIES(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (VEC_SERIES, (MODE), (ARG0), (ARG1))
#define gen_rtx_SS_PLUS(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SS_PLUS, (MODE), (ARG0), (ARG1))
#define gen_rtx_US_PLUS(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (US_PLUS, (MODE), (ARG0), (ARG1))
#define gen_rtx_SS_MINUS(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SS_MINUS, (MODE), (ARG0), (ARG1))
#define gen_rtx_SS_NEG(MODE, ARG0) \
  gen_rtx_fmt_e (SS_NEG, (MODE), (ARG0))
#define gen_rtx_US_NEG(MODE, ARG0) \
  gen_rtx_fmt_e (US_NEG, (MODE), (ARG0))
#define gen_rtx_SS_ABS(MODE, ARG0) \
  gen_rtx_fmt_e (SS_ABS, (MODE), (ARG0))
#define gen_rtx_SS_ASHIFT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (SS_ASHIFT, (MODE), (ARG0), (ARG1))
#define gen_rtx_US_ASHIFT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (US_ASHIFT, (MODE), (ARG0), (ARG1))
#define gen_rtx_US_MINUS(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (US_MINUS, (MODE), (ARG0), (ARG1))
#define gen_rtx_SS_TRUNCATE(MODE, ARG0) \
  gen_rtx_fmt_e (SS_TRUNCATE, (MODE), (ARG0))
#define gen_rtx_US_TRUNCATE(MODE, ARG0) \
  gen_rtx_fmt_e (US_TRUNCATE, (MODE), (ARG0))
#define gen_rtx_FMA(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_eee (FMA, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_COPYSIGN(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ee (COPYSIGN, (MODE), (ARG0), (ARG1))
#define gen_rtx_DEBUG_IMPLICIT_PTR(MODE, ARG0) \
  gen_rtx_fmt_t (DEBUG_IMPLICIT_PTR, (MODE), (ARG0))
#define gen_rtx_ENTRY_VALUE(MODE) \
  gen_rtx_fmt_0 (ENTRY_VALUE, (MODE))
#define gen_rtx_DEBUG_PARAMETER_REF(MODE, ARG0) \
  gen_rtx_fmt_t (DEBUG_PARAMETER_REF, (MODE), (ARG0))
#define gen_rtx_DEBUG_MARKER(MODE) \
  gen_rtx_fmt_ (DEBUG_MARKER, (MODE))
#define gen_rtx_MATCH_OPERAND(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_iss (MATCH_OPERAND, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_MATCH_SCRATCH(MODE, ARG0, ARG1) \
  gen_rtx_fmt_is (MATCH_SCRATCH, (MODE), (ARG0), (ARG1))
#define gen_rtx_MATCH_OPERATOR(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_isE (MATCH_OPERATOR, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_MATCH_PARALLEL(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_isE (MATCH_PARALLEL, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_MATCH_DUP(MODE, ARG0) \
  gen_rtx_fmt_i (MATCH_DUP, (MODE), (ARG0))
#define gen_rtx_MATCH_OP_DUP(MODE, ARG0, ARG1) \
  gen_rtx_fmt_iE (MATCH_OP_DUP, (MODE), (ARG0), (ARG1))
#define gen_rtx_MATCH_PAR_DUP(MODE, ARG0, ARG1) \
  gen_rtx_fmt_iE (MATCH_PAR_DUP, (MODE), (ARG0), (ARG1))
#define gen_rtx_MATCH_CODE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (MATCH_CODE, (MODE), (ARG0), (ARG1))
#define gen_rtx_MATCH_TEST(MODE, ARG0) \
  gen_rtx_fmt_s (MATCH_TEST, (MODE), (ARG0))
#define gen_rtx_DEFINE_DELAY(MODE, ARG0, ARG1) \
  gen_rtx_fmt_eE (DEFINE_DELAY, (MODE), (ARG0), (ARG1))
#define gen_rtx_DEFINE_PREDICATE(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_ses (DEFINE_PREDICATE, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_SPECIAL_PREDICATE(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_ses (DEFINE_SPECIAL_PREDICATE, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_CONSTRAINT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_CONSTRAINT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_MEMORY_CONSTRAINT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_MEMORY_CONSTRAINT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_SPECIAL_MEMORY_CONSTRAINT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_SPECIAL_MEMORY_CONSTRAINT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_RELAXED_MEMORY_CONSTRAINT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_RELAXED_MEMORY_CONSTRAINT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_ADDRESS_CONSTRAINT(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_ADDRESS_CONSTRAINT, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_EXCLUSION_SET(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (EXCLUSION_SET, (MODE), (ARG0), (ARG1))
#define gen_rtx_PRESENCE_SET(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (PRESENCE_SET, (MODE), (ARG0), (ARG1))
#define gen_rtx_FINAL_PRESENCE_SET(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (FINAL_PRESENCE_SET, (MODE), (ARG0), (ARG1))
#define gen_rtx_ABSENCE_SET(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (ABSENCE_SET, (MODE), (ARG0), (ARG1))
#define gen_rtx_FINAL_ABSENCE_SET(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (FINAL_ABSENCE_SET, (MODE), (ARG0), (ARG1))
#define gen_rtx_DEFINE_AUTOMATON(MODE, ARG0) \
  gen_rtx_fmt_s (DEFINE_AUTOMATON, (MODE), (ARG0))
#define gen_rtx_AUTOMATA_OPTION(MODE, ARG0) \
  gen_rtx_fmt_s (AUTOMATA_OPTION, (MODE), (ARG0))
#define gen_rtx_DEFINE_RESERVATION(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (DEFINE_RESERVATION, (MODE), (ARG0), (ARG1))
#define gen_rtx_DEFINE_INSN_RESERVATION(MODE, ARG0, ARG1, ARG2, ARG3) \
  gen_rtx_fmt_sies (DEFINE_INSN_RESERVATION, (MODE), (ARG0), (ARG1), (ARG2), (ARG3))
#define gen_rtx_DEFINE_ATTR(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_ATTR, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_DEFINE_ENUM_ATTR(MODE, ARG0, ARG1, ARG2) \
  gen_rtx_fmt_sse (DEFINE_ENUM_ATTR, (MODE), (ARG0), (ARG1), (ARG2))
#define gen_rtx_ATTR(MODE, ARG0) \
  gen_rtx_fmt_s (ATTR, (MODE), (ARG0))
#define gen_rtx_SET_ATTR(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (SET_ATTR, (MODE), (ARG0), (ARG1))
#define gen_rtx_SET_ATTR_ALTERNATIVE(MODE, ARG0, ARG1) \
  gen_rtx_fmt_sE (SET_ATTR_ALTERNATIVE, (MODE), (ARG0), (ARG1))
#define gen_rtx_EQ_ATTR(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ss (EQ_ATTR, (MODE), (ARG0), (ARG1))
#define gen_rtx_EQ_ATTR_ALT(MODE, ARG0, ARG1) \
  gen_rtx_fmt_ww (EQ_ATTR_ALT, (MODE), (ARG0), (ARG1))
#define gen_rtx_ATTR_FLAG(MODE, ARG0) \
  gen_rtx_fmt_s (ATTR_FLAG, (MODE), (ARG0))
#define gen_rtx_COND(MODE, ARG0, ARG1) \
  gen_rtx_fmt_Ee (COND, (MODE), (ARG0), (ARG1))
#define gen_rtx_DEFINE_SUBST(MODE, ARG0, ARG1, ARG2, ARG3) \
  gen_rtx_fmt_sEsE (DEFINE_SUBST, (MODE), (ARG0), (ARG1), (ARG2), (ARG3))
#define gen_rtx_DEFINE_SUBST_ATTR(MODE, ARG0, ARG1, ARG2, ARG3) \
  gen_rtx_fmt_ssss (DEFINE_SUBST_ATTR, (MODE), (ARG0), (ARG1), (ARG2), (ARG3))

#endif /* GCC_GENRTL_H */
