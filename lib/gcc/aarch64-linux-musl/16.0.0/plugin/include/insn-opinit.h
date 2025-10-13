/* Generated automatically by the program `genopinit'
   from the machine description file `md'.  */

#ifndef GCC_INSN_OPINIT_H
#define GCC_INSN_OPINIT_H 1
enum optab_tag {
  unknown_optab,
  sext_optab,
  trunc_optab,
  zext_optab,
  sfix_optab,
  ufix_optab,
  sfloat_optab,
  ufloat_optab,
  lrint_optab,
  lround_optab,
  lfloor_optab,
  lceil_optab,
  fract_optab,
  fractuns_optab,
  satfract_optab,
  satfractuns_optab,
  ustrunc_optab,
  sstrunc_optab,
  sfixtrunc_optab,
  ufixtrunc_optab,
  smul_widen_optab,
  umul_widen_optab,
  usmul_widen_optab,
  smadd_widen_optab,
  umadd_widen_optab,
  ssmadd_widen_optab,
  usmadd_widen_optab,
  smsub_widen_optab,
  umsub_widen_optab,
  ssmsub_widen_optab,
  usmsub_widen_optab,
  crc_optab,
  crc_rev_optab,
  vec_load_lanes_optab,
  vec_store_lanes_optab,
  vec_mask_load_lanes_optab,
  vec_mask_store_lanes_optab,
  vec_mask_len_load_lanes_optab,
  vec_mask_len_store_lanes_optab,
  vcond_mask_optab,
  vec_cmp_optab,
  vec_cmpu_optab,
  vec_cmpeq_optab,
  maskload_optab,
  maskstore_optab,
  mask_len_load_optab,
  mask_len_store_optab,
  gather_load_optab,
  mask_gather_load_optab,
  mask_len_gather_load_optab,
  scatter_store_optab,
  mask_scatter_store_optab,
  mask_len_scatter_store_optab,
  vec_extract_optab,
  vec_init_optab,
  sdot_prod_optab,
  udot_prod_optab,
  usdot_prod_optab,
  while_ult_optab,
  add_optab,
  addv_optab,
  ssadd_optab,
  usadd_optab,
  sub_optab,
  subv_optab,
  sssub_optab,
  ussub_optab,
  smul_optab,
  smulv_optab,
  ssmul_optab,
  usmul_optab,
  sdiv_optab,
  sdivv_optab,
  ssdiv_optab,
  udiv_optab,
  usdiv_optab,
  sdivmod_optab,
  udivmod_optab,
  smod_optab,
  umod_optab,
  ftrunc_optab,
  and_optab,
  ior_optab,
  xor_optab,
  ashl_optab,
  ssashl_optab,
  usashl_optab,
  ashr_optab,
  lshr_optab,
  rotl_optab,
  rotr_optab,
  vashl_optab,
  vashr_optab,
  vlshr_optab,
  vrotl_optab,
  vrotr_optab,
  smin_optab,
  smax_optab,
  umin_optab,
  umax_optab,
  neg_optab,
  negv_optab,
  ssneg_optab,
  usneg_optab,
  abs_optab,
  absv_optab,
  one_cmpl_optab,
  bswap_optab,
  ffs_optab,
  clz_optab,
  ctz_optab,
  clrsb_optab,
  popcount_optab,
  parity_optab,
  cmp_optab,
  ucmp_optab,
  eq_optab,
  ne_optab,
  gt_optab,
  ge_optab,
  lt_optab,
  le_optab,
  unord_optab,
  powi_optab,
  sqrt_optab,
  sync_old_add_optab,
  sync_old_sub_optab,
  sync_old_ior_optab,
  sync_old_and_optab,
  sync_old_xor_optab,
  sync_old_nand_optab,
  sync_new_add_optab,
  sync_new_sub_optab,
  sync_new_ior_optab,
  sync_new_and_optab,
  sync_new_xor_optab,
  sync_new_nand_optab,
  sync_compare_and_swap_optab,
  sync_lock_test_and_set_optab,
  mov_optab,
  movstrict_optab,
  movmisalign_optab,
  storent_optab,
  insv_optab,
  extv_optab,
  extzv_optab,
  insvmisalign_optab,
  extvmisalign_optab,
  extzvmisalign_optab,
  push_optab,
  reload_in_optab,
  reload_out_optab,
  cbranch_optab,
  tbranch_eq_optab,
  tbranch_ne_optab,
  addcc_optab,
  negcc_optab,
  notcc_optab,
  movcc_optab,
  cond_add_optab,
  cond_sub_optab,
  cond_smul_optab,
  cond_sdiv_optab,
  cond_smod_optab,
  cond_udiv_optab,
  cond_umod_optab,
  cond_and_optab,
  cond_ior_optab,
  cond_xor_optab,
  cond_ashl_optab,
  cond_ashr_optab,
  cond_lshr_optab,
  cond_smin_optab,
  cond_smax_optab,
  cond_umin_optab,
  cond_umax_optab,
  cond_copysign_optab,
  cond_fmin_optab,
  cond_fmax_optab,
  cond_fma_optab,
  cond_fms_optab,
  cond_fnma_optab,
  cond_fnms_optab,
  cond_neg_optab,
  cond_one_cmpl_optab,
  cond_len_add_optab,
  cond_len_sub_optab,
  cond_len_smul_optab,
  cond_len_sdiv_optab,
  cond_len_smod_optab,
  cond_len_udiv_optab,
  cond_len_umod_optab,
  cond_len_and_optab,
  cond_len_ior_optab,
  cond_len_xor_optab,
  cond_len_ashl_optab,
  cond_len_ashr_optab,
  cond_len_lshr_optab,
  cond_len_smin_optab,
  cond_len_smax_optab,
  cond_len_umin_optab,
  cond_len_umax_optab,
  cond_len_copysign_optab,
  cond_len_fmin_optab,
  cond_len_fmax_optab,
  cond_len_fma_optab,
  cond_len_fms_optab,
  cond_len_fnma_optab,
  cond_len_fnms_optab,
  cond_len_neg_optab,
  cond_len_one_cmpl_optab,
  vcond_mask_len_optab,
  cstore_optab,
  ctrap_optab,
  addv4_optab,
  subv4_optab,
  mulv4_optab,
  uaddv4_optab,
  usubv4_optab,
  umulv4_optab,
  negv3_optab,
  uaddc5_optab,
  usubc5_optab,
  addptr3_optab,
  spaceship_optab,
  smul_highpart_optab,
  umul_highpart_optab,
  cmpmem_optab,
  cmpstr_optab,
  cmpstrn_optab,
  cpymem_optab,
  movmem_optab,
  setmem_optab,
  strlen_optab,
  rawmemchr_optab,
  fma_optab,
  fms_optab,
  fnma_optab,
  fnms_optab,
  rint_optab,
  round_optab,
  roundeven_optab,
  floor_optab,
  ceil_optab,
  btrunc_optab,
  nearbyint_optab,
  acos_optab,
  acosh_optab,
  asin_optab,
  asinh_optab,
  atan2_optab,
  atan_optab,
  atanh_optab,
  copysign_optab,
  xorsign_optab,
  cadd90_optab,
  cadd270_optab,
  cmul_optab,
  cmul_conj_optab,
  cmla_optab,
  cmla_conj_optab,
  cmls_optab,
  cmls_conj_optab,
  cos_optab,
  cosh_optab,
  exp10_optab,
  exp2_optab,
  exp_optab,
  expm1_optab,
  fmod_optab,
  hypot_optab,
  ilogb_optab,
  isinf_optab,
  isfinite_optab,
  isnormal_optab,
  issignaling_optab,
  isnan_optab,
  ldexp_optab,
  log10_optab,
  log1p_optab,
  log2_optab,
  log_optab,
  logb_optab,
  pow_optab,
  remainder_optab,
  rsqrt_optab,
  scalb_optab,
  signbit_optab,
  significand_optab,
  sin_optab,
  sincos_optab,
  sinh_optab,
  tan_optab,
  tanh_optab,
  fegetround_optab,
  feclearexcept_optab,
  feraiseexcept_optab,
  fmax_optab,
  fmin_optab,
  reduc_fmax_scal_optab,
  reduc_fmin_scal_optab,
  reduc_smax_scal_optab,
  reduc_smin_scal_optab,
  reduc_plus_scal_optab,
  reduc_umax_scal_optab,
  reduc_umin_scal_optab,
  reduc_and_scal_optab,
  reduc_ior_scal_optab,
  reduc_xor_scal_optab,
  fold_left_plus_optab,
  mask_fold_left_plus_optab,
  mask_len_fold_left_plus_optab,
  extract_last_optab,
  fold_extract_last_optab,
  len_fold_extract_last_optab,
  uabd_optab,
  sabd_optab,
  savg_floor_optab,
  uavg_floor_optab,
  savg_ceil_optab,
  uavg_ceil_optab,
  ssum_widen_optab,
  usum_widen_optab,
  usad_optab,
  ssad_optab,
  smulhs_optab,
  smulhrs_optab,
  umulhs_optab,
  umulhrs_optab,
  sdiv_pow2_optab,
  vec_pack_sfix_trunc_optab,
  vec_pack_ssat_optab,
  vec_pack_trunc_optab,
  vec_pack_ufix_trunc_optab,
  vec_pack_sbool_trunc_optab,
  vec_pack_usat_optab,
  vec_packs_float_optab,
  vec_packu_float_optab,
  vec_perm_optab,
  vec_realign_load_optab,
  vec_set_optab,
  vec_shl_optab,
  vec_shr_optab,
  vec_unpack_sfix_trunc_hi_optab,
  vec_unpack_sfix_trunc_lo_optab,
  vec_unpack_ufix_trunc_hi_optab,
  vec_unpack_ufix_trunc_lo_optab,
  vec_unpacks_float_hi_optab,
  vec_unpacks_float_lo_optab,
  vec_unpacks_hi_optab,
  vec_unpacks_lo_optab,
  vec_unpacks_sbool_hi_optab,
  vec_unpacks_sbool_lo_optab,
  vec_unpacku_float_hi_optab,
  vec_unpacku_float_lo_optab,
  vec_unpacku_hi_optab,
  vec_unpacku_lo_optab,
  vec_widen_smult_even_optab,
  vec_widen_smult_hi_optab,
  vec_widen_smult_lo_optab,
  vec_widen_smult_odd_optab,
  vec_widen_ssub_optab,
  vec_widen_ssub_hi_optab,
  vec_widen_ssub_lo_optab,
  vec_widen_ssub_odd_optab,
  vec_widen_ssub_even_optab,
  vec_widen_sadd_optab,
  vec_widen_sadd_hi_optab,
  vec_widen_sadd_lo_optab,
  vec_widen_sadd_odd_optab,
  vec_widen_sadd_even_optab,
  vec_widen_sabd_optab,
  vec_widen_sabd_hi_optab,
  vec_widen_sabd_lo_optab,
  vec_widen_sabd_odd_optab,
  vec_widen_sabd_even_optab,
  vec_widen_sshiftl_hi_optab,
  vec_widen_sshiftl_lo_optab,
  vec_widen_umult_even_optab,
  vec_widen_umult_hi_optab,
  vec_widen_umult_lo_optab,
  vec_widen_umult_odd_optab,
  vec_widen_ushiftl_hi_optab,
  vec_widen_ushiftl_lo_optab,
  vec_widen_usub_optab,
  vec_widen_usub_hi_optab,
  vec_widen_usub_lo_optab,
  vec_widen_usub_odd_optab,
  vec_widen_usub_even_optab,
  vec_widen_uadd_optab,
  vec_widen_uadd_hi_optab,
  vec_widen_uadd_lo_optab,
  vec_widen_uadd_odd_optab,
  vec_widen_uadd_even_optab,
  vec_widen_uabd_optab,
  vec_widen_uabd_hi_optab,
  vec_widen_uabd_lo_optab,
  vec_widen_uabd_odd_optab,
  vec_widen_uabd_even_optab,
  vec_trunc_add_high_optab,
  vec_addsub_optab,
  vec_fmaddsub_optab,
  vec_fmsubadd_optab,
  sync_add_optab,
  sync_and_optab,
  sync_ior_optab,
  sync_lock_release_optab,
  sync_nand_optab,
  sync_sub_optab,
  sync_xor_optab,
  atomic_add_fetch_optab,
  atomic_add_optab,
  atomic_and_fetch_optab,
  atomic_and_optab,
  atomic_bit_test_and_set_optab,
  atomic_bit_test_and_complement_optab,
  atomic_bit_test_and_reset_optab,
  atomic_compare_and_swap_optab,
  atomic_exchange_optab,
  atomic_fetch_add_optab,
  atomic_fetch_and_optab,
  atomic_fetch_nand_optab,
  atomic_fetch_or_optab,
  atomic_fetch_sub_optab,
  atomic_fetch_xor_optab,
  atomic_load_optab,
  atomic_nand_fetch_optab,
  atomic_nand_optab,
  atomic_or_fetch_optab,
  atomic_or_optab,
  atomic_store_optab,
  atomic_sub_fetch_optab,
  atomic_sub_optab,
  atomic_xor_fetch_optab,
  atomic_xor_optab,
  atomic_add_fetch_cmp_0_optab,
  atomic_sub_fetch_cmp_0_optab,
  atomic_and_fetch_cmp_0_optab,
  atomic_or_fetch_cmp_0_optab,
  atomic_xor_fetch_cmp_0_optab,
  get_thread_pointer_optab,
  set_thread_pointer_optab,
  check_raw_ptrs_optab,
  check_war_ptrs_optab,
  vec_duplicate_optab,
  vec_series_optab,
  vec_shl_insert_optab,
  len_load_optab,
  len_store_optab,
  mask_len_strided_load_optab,
  mask_len_strided_store_optab,
  select_vl_optab,
  andn_optab,
  iorn_optab,
  FIRST_CONV_OPTAB = sext_optab,
  LAST_CONVLIB_OPTAB = sstrunc_optab,
  LAST_CONV_OPTAB = while_ult_optab,
  FIRST_NORM_OPTAB = add_optab,
  LAST_NORMLIB_OPTAB = sync_lock_test_and_set_optab,
  LAST_NORM_OPTAB = iorn_optab
};

#define NUM_OPTABS          454
#define NUM_CONVLIB_OPTABS  17
#define NUM_NORMLIB_OPTABS  80
#define NUM_OPTAB_PATTERNS  3122
typedef enum optab_tag optab;
typedef enum optab_tag convert_optab;
typedef enum optab_tag direct_optab;

struct optab_libcall_d
{
  char libcall_suffix;
  const char *libcall_basename;
  void (*libcall_gen) (optab, const char *name,
		       char suffix, machine_mode);
};

struct convert_optab_libcall_d
{
  const char *libcall_basename;
  void (*libcall_gen) (convert_optab, const char *name,
		       machine_mode, machine_mode);
};

/* Given an enum insn_code, access the function to construct
   the body of that kind of insn.  */
#define GEN_FCN(CODE) (insn_data[CODE].genfun)

#ifdef NUM_RTX_CODE
/* Contains the optab used for each rtx code, and vice-versa.  */
extern const optab code_to_optab_[NUM_RTX_CODE];
extern const enum rtx_code optab_to_code_[NUM_OPTABS];

static inline optab
code_to_optab (enum rtx_code code)
{
  return code_to_optab_[code];
}

static inline enum rtx_code
optab_to_code (optab op)
{
  return optab_to_code_[op];
}

extern insn_code maybe_code_for_aarch64_tbz (rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_tbz (rtx_code arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_tbz (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_tbz (rtx_code, machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_tbz (rtx_code arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_tbz (arg0, arg1, arg2, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_ccmp (machine_mode, machine_mode);
inline insn_code
code_for_ccmp (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_ccmp (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_ccmp (machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_ccmp (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_ccmp (arg0, arg1, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_ccmp_rev (machine_mode, machine_mode);
inline insn_code
code_for_ccmp_rev (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_ccmp_rev (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_ccmp_rev (machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_ccmp_rev (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_ccmp_rev (arg0, arg1, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_rbit (machine_mode);
inline insn_code
code_for_aarch64_rbit (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_rbit (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_rbit (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_rbit (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_rbit (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_and3nr_compare0 (machine_mode);
inline insn_code
code_for_aarch64_and3nr_compare0 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_and3nr_compare0 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_and3nr_compare0 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_and3nr_compare0 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_and3nr_compare0 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_rev16 (machine_mode);
inline insn_code
code_for_aarch64_rev16 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_rev16 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_rev16 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_rev16 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_rev16 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_xorsign3 (machine_mode);
inline insn_code
code_for_xorsign3 (machine_mode arg0)
{
  insn_code code = maybe_code_for_xorsign3 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_xorsign3 (machine_mode, rtx, rtx, rtx);
inline rtx
gen_xorsign3 (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_xorsign3 (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_reload_movcp (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_reload_movcp (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_reload_movcp (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_reload_movcp (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_reload_movcp (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_reload_movcp (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_reload_mov (machine_mode);
inline insn_code
code_for_aarch64_reload_mov (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_reload_mov (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_reload_mov (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_reload_mov (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_reload_mov (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_movdi_low (machine_mode);
inline insn_code
code_for_aarch64_movdi_low (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_movdi_low (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_movdi_low (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_movdi_low (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_movdi_low (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_movdi_high (machine_mode);
inline insn_code
code_for_aarch64_movdi_high (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_movdi_high (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_movdi_high (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_movdi_high (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_movdi_high (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_movhigh_di (machine_mode);
inline insn_code
code_for_aarch64_movhigh_di (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_movhigh_di (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_movhigh_di (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_movhigh_di (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_movhigh_di (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_movlow_di (machine_mode);
inline insn_code
code_for_aarch64_movlow_di (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_movlow_di (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_movlow_di (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_movlow_di (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_movlow_di (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_ldr_got_tiny (machine_mode);
inline insn_code
code_for_ldr_got_tiny (machine_mode arg0)
{
  insn_code code = maybe_code_for_ldr_got_tiny (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_ldr_got_tiny (machine_mode, rtx, rtx);
inline rtx
gen_ldr_got_tiny (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_ldr_got_tiny (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_probe_sve_stack_clash (machine_mode);
inline insn_code
code_for_probe_sve_stack_clash (machine_mode arg0)
{
  insn_code code = maybe_code_for_probe_sve_stack_clash (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_probe_sve_stack_clash (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_probe_sve_stack_clash (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_probe_sve_stack_clash (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_set (int, machine_mode);
inline insn_code
code_for_aarch64_set (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_set (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_set (int, machine_mode, rtx);
inline rtx
gen_aarch64_set (int arg0, machine_mode arg1, rtx x0)
{
  rtx res = maybe_gen_aarch64_set (arg0, arg1, x0);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_get (int, machine_mode);
inline insn_code
code_for_aarch64_get (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_get (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_get (int, machine_mode, rtx);
inline rtx
gen_aarch64_get (int arg0, machine_mode arg1, rtx x0)
{
  rtx res = maybe_gen_aarch64_get (arg0, arg1, x0);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_despeculate_copy (machine_mode);
inline insn_code
code_for_despeculate_copy (machine_mode arg0)
{
  insn_code code = maybe_code_for_despeculate_copy (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_despeculate_copy (machine_mode, rtx, rtx, rtx);
inline rtx
gen_despeculate_copy (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_despeculate_copy (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_dup_lane (machine_mode);
inline insn_code
code_for_aarch64_dup_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_dup_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_dup_lane (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_dup_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_dup_lane (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_dup_lane (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_dup_lane (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_dup_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_dup_lane (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_dup_lane (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_dup_lane (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_split_simd_mov (machine_mode);
inline insn_code
code_for_aarch64_split_simd_mov (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_split_simd_mov (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_split_simd_mov (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_split_simd_mov (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_split_simd_mov (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_rsqrte (machine_mode);
inline insn_code
code_for_aarch64_rsqrte (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_rsqrte (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_rsqrte (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_rsqrte (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_rsqrte (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_rsqrts (machine_mode);
inline insn_code
code_for_aarch64_rsqrts (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_rsqrts (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_rsqrts (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_rsqrts (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_rsqrts (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_vec_set (machine_mode);
inline insn_code
code_for_aarch64_simd_vec_set (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_simd_vec_set (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_vec_set (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_simd_vec_set (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_simd_vec_set (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_vec_copy_lane (machine_mode);
inline insn_code
code_for_aarch64_simd_vec_copy_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_simd_vec_copy_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_vec_copy_lane (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_simd_vec_copy_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_simd_vec_copy_lane (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_vec_copy_lane (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_simd_vec_copy_lane (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_simd_vec_copy_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_vec_copy_lane (machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_simd_vec_copy_lane (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_simd_vec_copy_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_addlp (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_addlp (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_addlp (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_addlp (rtx_code, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_addlp (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_addlp (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_bsl (machine_mode);
inline insn_code
code_for_aarch64_simd_bsl (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_simd_bsl (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_bsl (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_simd_bsl (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_simd_bsl (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_get_lane (machine_mode);
inline insn_code
code_for_aarch64_get_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_get_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_get_lane (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_get_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_get_lane (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_vec_concat (machine_mode);
inline insn_code
code_for_aarch64_vec_concat (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_vec_concat (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_vec_concat (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_vec_concat (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_vec_concat (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_combine (machine_mode);
inline insn_code
code_for_aarch64_combine (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_combine (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_combine (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_combine (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_combine (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_cm (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_cm (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_cm (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_cm (rtx_code, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_cm (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_cm (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_ld2r (machine_mode);
inline insn_code
code_for_aarch64_simd_ld2r (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_simd_ld2r (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_ld2r (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_simd_ld2r (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_simd_ld2r (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_vec_load_lanes_lane (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_vec_load_lanes_lane (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_vec_load_lanes_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_vec_load_lanes_lane (machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_vec_load_lanes_lane (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_vec_load_lanes_lane (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_ld3r (machine_mode);
inline insn_code
code_for_aarch64_simd_ld3r (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_simd_ld3r (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_ld3r (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_simd_ld3r (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_simd_ld3r (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_simd_ld4r (machine_mode);
inline insn_code
code_for_aarch64_simd_ld4r (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_simd_ld4r (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_simd_ld4r (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_simd_ld4r (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_simd_ld4r (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ld1x3 (machine_mode);
inline insn_code
code_for_aarch64_ld1x3 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ld1x3 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ld1x3 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_ld1x3 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_ld1x3 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ld1x4 (machine_mode);
inline insn_code
code_for_aarch64_ld1x4 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ld1x4 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ld1x4 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_ld1x4 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_ld1x4 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_st1x2 (machine_mode);
inline insn_code
code_for_aarch64_st1x2 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_st1x2 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_st1x2 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_st1x2 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_st1x2 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_st1x3 (machine_mode);
inline insn_code
code_for_aarch64_st1x3 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_st1x3 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_st1x3 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_st1x3 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_st1x3 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_st1x4 (machine_mode);
inline insn_code
code_for_aarch64_st1x4 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_st1x4 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_st1x4 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_st1x4 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_st1x4 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ld (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_ld (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_ld (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ld (machine_mode, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_ld (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_ld (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ld1 (machine_mode);
inline insn_code
code_for_aarch64_ld1 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ld1 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ld1 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_ld1 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_ld1 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ld1x2 (machine_mode);
inline insn_code
code_for_aarch64_ld1x2 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ld1x2 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ld1x2 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_ld1x2 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_ld1x2 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ld_lane (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_ld_lane (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_ld_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ld_lane (machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_ld_lane (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_ld_lane (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64 (int, machine_mode);
inline insn_code
code_for_aarch64 (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64 (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64 (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64 (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64 (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64 (int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64 (int arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64 (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64 (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64 (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64 (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ext (machine_mode);
inline insn_code
code_for_aarch64_ext (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ext (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ext (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_ext (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_ext (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_rev (int, machine_mode);
inline insn_code
code_for_aarch64_rev (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_rev (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_rev (int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_rev (int arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_rev (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_st (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_st (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_st (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_st (machine_mode, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_st (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_st (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_st_lane (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_st_lane (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_st_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_st_lane (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_st_lane (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_st_lane (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_st1 (machine_mode);
inline insn_code
code_for_aarch64_st1 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_st1 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_st1 (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_st1 (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_st1 (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_frecpe (machine_mode);
inline insn_code
code_for_aarch64_frecpe (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_frecpe (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_frecpe (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_frecpe (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_frecpe (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_frecps (machine_mode);
inline insn_code
code_for_aarch64_frecps (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_frecps (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_frecps (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_frecps (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_frecps (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_lut (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_lut (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_lut (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_lut (machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_lut (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_lut (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_high (int, machine_mode);
inline insn_code
code_for_aarch64_high (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_high (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_high (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_high (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_high (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_high_le (int, machine_mode);
inline insn_code
code_for_aarch64_high_le (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_high_le (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_high_be (int, machine_mode);
inline insn_code
code_for_aarch64_high_be (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_high_be (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_lane (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_lane (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_lane (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_lane (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_lane (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_lane (arg0, arg1, arg2, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_atomic_compare_and_swap (machine_mode);
inline insn_code
code_for_atomic_compare_and_swap (machine_mode arg0)
{
  insn_code code = maybe_code_for_atomic_compare_and_swap (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_atomic_compare_and_swap (machine_mode, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_atomic_compare_and_swap (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5, rtx x6, rtx x7)
{
  rtx res = maybe_gen_atomic_compare_and_swap (arg0, x0, x1, x2, x3, x4, x5, x6, x7);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_compare_and_swap (machine_mode);
inline insn_code
code_for_aarch64_compare_and_swap (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_compare_and_swap (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_compare_and_swap (machine_mode, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_compare_and_swap (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5, rtx x6)
{
  rtx res = maybe_gen_aarch64_compare_and_swap (arg0, x0, x1, x2, x3, x4, x5, x6);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_compare_and_swap_lse (machine_mode);
inline insn_code
code_for_aarch64_compare_and_swap_lse (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_compare_and_swap_lse (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_compare_and_swap_lse (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_compare_and_swap_lse (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_compare_and_swap_lse (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_load_exclusive (machine_mode);
inline insn_code
code_for_aarch64_load_exclusive (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_load_exclusive (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_load_exclusive (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_load_exclusive (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_load_exclusive (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_store_exclusive (machine_mode);
inline insn_code
code_for_aarch64_store_exclusive (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_store_exclusive (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_store_exclusive (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_store_exclusive (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_store_exclusive (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_mov (machine_mode);
inline insn_code
code_for_aarch64_pred_mov (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_mov (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_mov (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_mov (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pred_mov (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_reinterpret (machine_mode);
inline insn_code
code_for_aarch64_sve_reinterpret (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_reinterpret (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_reinterpret (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve_reinterpret (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_reinterpret (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_load (rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_load (rtx_code arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_load (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_load (rtx_code, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_load (rtx_code arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_load (arg0, arg1, arg2, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ldf1 (int, machine_mode);
inline insn_code
code_for_aarch64_ldf1 (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_ldf1 (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ldf1 (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_ldf1 (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_ldf1 (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ldf1 (int, rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_ldf1 (int arg0, rtx_code arg1, machine_mode arg2, machine_mode arg3)
{
  insn_code code = maybe_code_for_aarch64_ldf1 (arg0, arg1, arg2, arg3);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ldf1 (int, rtx_code, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_ldf1 (int arg0, rtx_code arg1, machine_mode arg2, machine_mode arg3, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_ldf1 (arg0, arg1, arg2, arg3, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ldnt1 (machine_mode);
inline insn_code
code_for_aarch64_ldnt1 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ldnt1 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ldnt1 (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_ldnt1 (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_ldnt1 (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_gather_load (rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_gather_load (rtx_code arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_gather_load (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_gather_load (rtx_code, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_gather_load (rtx_code arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5, rtx x6, rtx x7)
{
  rtx res = maybe_gen_aarch64_gather_load (arg0, arg1, arg2, x0, x1, x2, x3, x4, x5, x6, x7);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ldff1_gather (machine_mode);
inline insn_code
code_for_aarch64_ldff1_gather (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ldff1_gather (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ldff1_gather (machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_ldff1_gather (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_aarch64_ldff1_gather (arg0, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ldff1_gather (rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_ldff1_gather (rtx_code arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_ldff1_gather (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ldff1_gather (rtx_code, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_ldff1_gather (rtx_code arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5, rtx x6)
{
  rtx res = maybe_gen_aarch64_ldff1_gather (arg0, arg1, arg2, x0, x1, x2, x3, x4, x5, x6);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_prefetch (machine_mode);
inline insn_code
code_for_aarch64_sve_prefetch (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_prefetch (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_prefetch (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_prefetch (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_prefetch (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_gather_prefetch (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_gather_prefetch (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_gather_prefetch (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_gather_prefetch (machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_gather_prefetch (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5, rtx x6, rtx x7, rtx x8)
{
  rtx res = maybe_gen_aarch64_sve_gather_prefetch (arg0, arg1, x0, x1, x2, x3, x4, x5, x6, x7, x8);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_store_trunc (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_store_trunc (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_store_trunc (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_store_trunc (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_store_trunc (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_store_trunc (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_stnt1 (machine_mode);
inline insn_code
code_for_aarch64_stnt1 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_stnt1 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_stnt1 (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_stnt1 (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_stnt1 (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_scatter_store_trunc (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_scatter_store_trunc (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_scatter_store_trunc (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_scatter_store_trunc (machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_scatter_store_trunc (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_aarch64_scatter_store_trunc (arg0, arg1, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_vec_duplicate_vq_le (machine_mode);
inline insn_code
code_for_aarch64_vec_duplicate_vq_le (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_vec_duplicate_vq_le (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_vec_duplicate_vq_le (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_vec_duplicate_vq_le (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_vec_duplicate_vq_le (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_vec_duplicate_vq_be (machine_mode);
inline insn_code
code_for_aarch64_vec_duplicate_vq_be (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_vec_duplicate_vq_be (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_vec_duplicate_vq_be (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_vec_duplicate_vq_be (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_vec_duplicate_vq_be (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_ld1rq (machine_mode);
inline insn_code
code_for_aarch64_sve_ld1rq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_ld1rq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_ld1rq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_ld1rq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_ld1rq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_ld1ro (machine_mode);
inline insn_code
code_for_aarch64_sve_ld1ro (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_ld1ro (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_ld1ro (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_ld1ro (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_ld1ro (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_extract (int, machine_mode);
inline insn_code
code_for_extract (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_extract (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_extract (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_extract (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_extract (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_pred (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred (rtx_code, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pred (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_pred (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_pred (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond (rtx_code, machine_mode);
inline insn_code
code_for_cond (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_cond (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_cond (rtx_code, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_cond (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_cond (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred (int, machine_mode);
inline insn_code
code_for_aarch64_pred (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pred (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_pred (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_pred (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_pred (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_pred (int, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_aarch64_pred (arg0, arg1, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_revbhw (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_revbhw (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_revbhw (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_revbhw (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_revbhw (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_revbhw (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond (int, machine_mode);
inline insn_code
code_for_cond (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_cond (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_cond (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_cond (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_cond (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_cond (int, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_cond (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_cond (arg0, arg1, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_sxt (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_pred_sxt (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_sxt (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_sxt (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_sxt (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pred_sxt (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_cond_sxt (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_cond_sxt (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_cond_sxt (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_cond_sxt (machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_cond_sxt (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_cond_sxt (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_ptrue_cnot (machine_mode);
inline insn_code
code_for_aarch64_ptrue_cnot (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_ptrue_cnot (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_ptrue_cnot (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_ptrue_cnot (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_ptrue_cnot (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond_cnot (machine_mode);
inline insn_code
code_for_cond_cnot (machine_mode arg0)
{
  insn_code code = maybe_code_for_cond_cnot (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond_cnot (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond_cnot (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond_cnot (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve (int, machine_mode);
inline insn_code
code_for_aarch64_sve (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve (int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve (int arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sve (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sve (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_one_cmpl_z (machine_mode);
inline insn_code
code_for_aarch64_pred_one_cmpl_z (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_one_cmpl_z (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_one_cmpl_z (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_one_cmpl_z (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pred_one_cmpl_z (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_adr (machine_mode);
inline insn_code
code_for_aarch64_adr (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_adr (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_adr (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_adr (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_adr (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_adr_shift (machine_mode);
inline insn_code
code_for_aarch64_adr_shift (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_adr_shift (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_adr_shift (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_adr_shift (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_adr_shift (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_abd (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_pred_abd (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_abd (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_abd (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_abd (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_pred_abd (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_cond_abd (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_cond_abd (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_cond_abd (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_cond_abd (rtx_code, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_cond_abd (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_cond_abd (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond_bic (machine_mode);
inline insn_code
code_for_cond_bic (machine_mode arg0)
{
  insn_code code = maybe_code_for_cond_bic (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond_bic (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_cond_bic (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_cond_bic (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cadd3 (int, machine_mode);
inline insn_code
code_for_cadd3 (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_cadd3 (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cadd3 (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_cadd3 (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_cadd3 (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_abd (machine_mode);
inline insn_code
code_for_aarch64_pred_abd (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_abd (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_abd (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_abd (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_abd (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_cond_abd (machine_mode);
inline insn_code
code_for_aarch64_cond_abd (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_cond_abd (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_cond_abd (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_cond_abd (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_cond_abd (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_mul_lane (machine_mode);
inline insn_code
code_for_aarch64_mul_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_mul_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_mul_lane (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_mul_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_mul_lane (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_and3 (machine_mode);
inline insn_code
code_for_and3 (machine_mode arg0)
{
  insn_code code = maybe_code_for_and3 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_and3 (machine_mode, rtx, rtx, rtx);
inline rtx
gen_and3 (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_and3 (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_z (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_pred_z (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_z (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_z (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_z (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_pred_z (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fma (machine_mode);
inline insn_code
code_for_aarch64_pred_fma (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_fma (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fma (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fma (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fma (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fnma (machine_mode);
inline insn_code
code_for_aarch64_pred_fnma (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_fnma (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fnma (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fnma (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fnma (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_dot_prod_lane (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_dot_prod_lane (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_dot_prod_lane (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_dot_prod_lane (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_dot_prod_lane (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_dot_prod_lane (arg0, arg1, arg2, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_dot_prod (int, machine_mode, machine_mode);
inline insn_code
code_for_dot_prod (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_dot_prod (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_sve_add (int, machine_mode);
inline insn_code
code_for_aarch64_sve_add (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_add (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_add (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_add (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_add (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_lane (int, machine_mode);
inline insn_code
code_for_aarch64_lane (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_lane (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_tmad (machine_mode);
inline insn_code
code_for_aarch64_sve_tmad (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_tmad (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_tmad (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_tmad (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_tmad (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_vnx4sf (int);
inline insn_code
code_for_aarch64_sve_vnx4sf (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_vnx4sf (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_vnx4sf (int, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_vnx4sf (int arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_vnx4sf (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_lanevnx4sf (int);
inline insn_code
code_for_aarch64_sve_lanevnx4sf (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_lanevnx4sf (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_lanevnx4sf (int, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_lanevnx4sf (int arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_lanevnx4sf (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_vcond_mask (machine_mode, machine_mode);
inline insn_code
code_for_vcond_mask (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_vcond_mask (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_vcond_mask (machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_vcond_mask (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_vcond_mask (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sel_dup (machine_mode);
inline insn_code
code_for_aarch64_sel_dup (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sel_dup (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sel_dup (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sel_dup (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sel_dup (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_cmp (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_pred_cmp (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_cmp (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_cmp (rtx_code, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_cmp (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_cmp (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_cmp_acle (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_pred_cmp_acle (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_cmp_acle (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_cmp_acle (rtx_code, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_cmp_acle (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_cmp_acle (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_cmp_wide (int, machine_mode);
inline insn_code
code_for_aarch64_pred_cmp_wide (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_cmp_wide (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_cmp_wide (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_cmp_wide (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_cmp_wide (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_while (int, machine_mode, machine_mode);
inline insn_code
code_for_while (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_while (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_while (int, machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_while (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_while (arg0, arg1, arg2, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_while_acle (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_while_acle (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_while_acle (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_while_acle (int, machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_while_acle (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_while_acle (arg0, arg1, arg2, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_while_ptest (int, machine_mode, machine_mode);
inline insn_code
code_for_while_ptest (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_while_ptest (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_while_ptest (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_while_ptest (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_while_ptest (arg0, arg1, arg2, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fcm (int, machine_mode);
inline insn_code
code_for_aarch64_pred_fcm (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_fcm (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fcm (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fcm (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fcm (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fcm_acle (int, machine_mode);
inline insn_code
code_for_aarch64_pred_fcm_acle (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_fcm_acle (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fcm_acle (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fcm_acle (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fcm_acle (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fcmuo (machine_mode);
inline insn_code
code_for_aarch64_pred_fcmuo (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_fcmuo (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fcmuo (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fcmuo (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fcmuo (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fcmuo_acle (machine_mode);
inline insn_code
code_for_aarch64_pred_fcmuo_acle (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_fcmuo_acle (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fcmuo_acle (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fcmuo_acle (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fcmuo_acle (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_fac_acle (int, machine_mode);
inline insn_code
code_for_aarch64_pred_fac_acle (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_fac_acle (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_fac_acle (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_fac_acle (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_pred_fac_acle (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_fold_extract (int, machine_mode);
inline insn_code
code_for_fold_extract (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_fold_extract (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_fold_extract (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_fold_extract (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_fold_extract (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_fold_extract_vector (int, machine_mode);
inline insn_code
code_for_aarch64_fold_extract_vector (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_fold_extract_vector (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_fold_extract_vector (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_fold_extract_vector (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_fold_extract_vector (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_reduc (int, machine_mode);
inline insn_code
code_for_aarch64_pred_reduc (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_pred_reduc (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_reduc (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_reduc (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pred_reduc (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_compact (machine_mode);
inline insn_code
code_for_aarch64_sve_compact (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_compact (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_compact (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_compact (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_compact (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_dup_lane (machine_mode);
inline insn_code
code_for_aarch64_sve_dup_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_dup_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_dup_lane (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_dup_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_dup_lane (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_dupq_lane (machine_mode);
inline insn_code
code_for_aarch64_sve_dupq_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_dupq_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_dupq_lane (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_dupq_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_dupq_lane (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_rev (machine_mode);
inline insn_code
code_for_aarch64_sve_rev (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_rev (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_rev (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve_rev (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_rev (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_splice (machine_mode);
inline insn_code
code_for_aarch64_sve_splice (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_splice (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_splice (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_splice (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_splice (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_ext (machine_mode);
inline insn_code
code_for_aarch64_sve_ext (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_ext (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_ext (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_ext (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_ext (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_rev_acle (machine_mode);
inline insn_code
code_for_aarch64_sve_rev_acle (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_rev_acle (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_rev_acle (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve_rev_acle (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_rev_acle (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_acle (int, machine_mode);
inline insn_code
code_for_aarch64_sve_acle (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_acle (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_acle (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_acle (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_acle (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pack_partial (machine_mode);
inline insn_code
code_for_aarch64_pack_partial (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pack_partial (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pack_partial (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pack_partial (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pack_partial (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_unpk (int, int, machine_mode);
inline insn_code
code_for_aarch64_sve_unpk (int arg0, int arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_unpk (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_unpk (int, int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve_unpk (int arg0, int arg1, machine_mode arg2, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_unpk (arg0, arg1, arg2, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_nontrunc (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_nontrunc (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_nontrunc (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_nontrunc (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_nontrunc (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_nontrunc (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_trunc (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_trunc (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_trunc (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_trunc (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_trunc (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_trunc (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond_nontrunc (int, machine_mode, machine_mode);
inline insn_code
code_for_cond_nontrunc (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_cond_nontrunc (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond_nontrunc (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond_nontrunc (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond_nontrunc (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond_trunc (int, machine_mode, machine_mode);
inline insn_code
code_for_cond_trunc (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_cond_trunc (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond_trunc (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond_trunc (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond_trunc (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_nonextend (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_nonextend (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_nonextend (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_nonextend (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_nonextend (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_nonextend (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_extend (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_extend (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_extend (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_extend (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_extend (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_extend (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond_nonextend (int, machine_mode, machine_mode);
inline insn_code
code_for_cond_nonextend (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_cond_nonextend (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond_nonextend (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond_nonextend (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond_nonextend (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_cond_extend (int, machine_mode, machine_mode);
inline insn_code
code_for_cond_extend (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_cond_extend (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_cond_extend (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_cond_extend (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_cond_extend (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_cvtnt (machine_mode);
inline insn_code
code_for_aarch64_sve_cvtnt (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_cvtnt (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_cvtnt (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_cvtnt (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_cvtnt (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sve_cvtnt (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_cvtnt (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_cvtnt (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_punpk (int, machine_mode);
inline insn_code
code_for_aarch64_sve_punpk (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_punpk (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_punpk (int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve_punpk (int arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_punpk (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_punpk_acle (int);
inline insn_code
code_for_aarch64_sve_punpk_acle (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_punpk_acle (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_punpk_acle (int, rtx, rtx);
inline rtx
gen_aarch64_sve_punpk_acle (int arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_punpk_acle (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_brk (int);
inline insn_code
code_for_aarch64_brk (int arg0)
{
  insn_code code = maybe_code_for_aarch64_brk (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_brk (int, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_brk (int arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_brk (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_pat (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve_pat (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_pat (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_pat (rtx_code, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_pat (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_pat (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pred_cntp (machine_mode);
inline insn_code
code_for_aarch64_pred_cntp (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pred_cntp (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pred_cntp (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pred_cntp (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_pred_cntp (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_cntp (rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve_cntp (rtx_code arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve_cntp (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_cntp (rtx_code, machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_cntp (rtx_code arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_cntp (arg0, arg1, arg2, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_cntp (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve_cntp (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_cntp (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_cntp (rtx_code, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_cntp (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_cntp (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_get_neonq (machine_mode);
inline insn_code
code_for_aarch64_sve_get_neonq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_get_neonq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_get_neonq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_get_neonq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_get_neonq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_set_neonq (machine_mode);
inline insn_code
code_for_aarch64_sve_set_neonq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_set_neonq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_set_neonq (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_set_neonq (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_set_neonq (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pmov_to (machine_mode);
inline insn_code
code_for_aarch64_pmov_to (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pmov_to (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pmov_to (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_pmov_to (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_pmov_to (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pmov_lane_to (machine_mode);
inline insn_code
code_for_aarch64_pmov_lane_to (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pmov_lane_to (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pmov_lane_to (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_pmov_lane_to (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_pmov_lane_to (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pmov_from (machine_mode);
inline insn_code
code_for_aarch64_pmov_from (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pmov_from (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pmov_from (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_pmov_from (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_pmov_from (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_pmov_lane_from (machine_mode);
inline insn_code
code_for_aarch64_pmov_lane_from (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_pmov_lane_from (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_pmov_lane_from (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_pmov_lane_from (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_pmov_lane_from (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_ld1_extendq (machine_mode);
inline insn_code
code_for_aarch64_sve_ld1_extendq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_ld1_extendq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_ld1_extendq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_ld1_extendq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_ld1_extendq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_ldnq (machine_mode);
inline insn_code
code_for_aarch64_sve_ldnq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_ldnq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_ldnq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_ldnq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_ldnq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_strided2 (int, machine_mode);
inline insn_code
code_for_aarch64_strided2 (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_strided2 (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_strided2 (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_strided2 (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_strided2 (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_strided4 (int, machine_mode);
inline insn_code
code_for_aarch64_strided4 (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_strided4 (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_strided4 (int, machine_mode, rtx, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_strided4 (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4, rtx x5)
{
  rtx res = maybe_gen_aarch64_strided4 (arg0, arg1, x0, x1, x2, x3, x4, x5);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_gather_ld1q (machine_mode);
inline insn_code
code_for_aarch64_gather_ld1q (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_gather_ld1q (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_gather_ld1q (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_gather_ld1q (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_gather_ld1q (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_gather_ldnt (machine_mode);
inline insn_code
code_for_aarch64_gather_ldnt (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_gather_ldnt (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_gather_ldnt (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_gather_ldnt (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_gather_ldnt (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_gather_ldnt (rtx_code, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_gather_ldnt (rtx_code arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_gather_ldnt (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_gather_ldnt (rtx_code, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_gather_ldnt (rtx_code arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_gather_ldnt (arg0, arg1, arg2, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_st1_truncq (machine_mode);
inline insn_code
code_for_aarch64_sve_st1_truncq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_st1_truncq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_st1_truncq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_st1_truncq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_st1_truncq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_stnq (machine_mode);
inline insn_code
code_for_aarch64_sve_stnq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_stnq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_stnq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_stnq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_stnq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_scatter_stnt (machine_mode);
inline insn_code
code_for_aarch64_scatter_stnt (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_scatter_stnt (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_scatter_stnt (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_scatter_stnt (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_scatter_stnt (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_scatter_stnt (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_scatter_stnt (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_scatter_stnt (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_scatter_stnt (machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_scatter_stnt (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_scatter_stnt (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_ptrue_c (int);
inline insn_code
code_for_aarch64_sve_ptrue_c (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_ptrue_c (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_ptrue_c (int, rtx);
inline rtx
gen_aarch64_sve_ptrue_c (int arg0, rtx x0)
{
  rtx res = maybe_gen_aarch64_sve_ptrue_c (arg0, x0);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_pext (int);
inline insn_code
code_for_aarch64_sve_pext (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_pext (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_pext (int, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_pext (int arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_pext (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_pextx2 (int);
inline insn_code
code_for_aarch64_sve_pextx2 (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_pextx2 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_pextx2 (int, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_pextx2 (int arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_pextx2 (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_psel (int);
inline insn_code
code_for_aarch64_sve_psel (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_psel (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_psel (int, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_psel (int arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_psel (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_cntp_c (int);
inline insn_code
code_for_aarch64_sve_cntp_c (int arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_cntp_c (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_cntp_c (int, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_cntp_c (int arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_cntp_c (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_single (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve_single (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_single (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_single (rtx_code, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_single (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_single (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_single (int, machine_mode);
inline insn_code
code_for_aarch64_sve_single (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_single (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_single (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_single (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_single (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_clamp (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve_clamp (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_clamp (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_clamp (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_clamp (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_clamp (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_clamp_single (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve_clamp_single (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_clamp_single (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_clamp_single (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_clamp_single (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_clamp_single (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_suqadd_const (machine_mode);
inline insn_code
code_for_aarch64_sve_suqadd_const (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_suqadd_const (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_suqadd_const (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_suqadd_const (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_suqadd_const (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_lane (int, machine_mode);
inline insn_code
code_for_aarch64_sve_lane (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_lane (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_lane (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sve_lane (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_fclamp (machine_mode);
inline insn_code
code_for_aarch64_sve_fclamp (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_fclamp (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_fclamp (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_fclamp (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_fclamp (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_fclamp_single (machine_mode);
inline insn_code
code_for_aarch64_sve_fclamp_single (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_fclamp_single (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_fclamp_single (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_fclamp_single (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_fclamp_single (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_add_mul_lane (machine_mode);
inline insn_code
code_for_aarch64_sve_add_mul_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_add_mul_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_add_mul_lane (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_add_mul_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_add_mul_lane (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_sub_mul_lane (machine_mode);
inline insn_code
code_for_aarch64_sve_sub_mul_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_sub_mul_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_sub_mul_lane (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_sub_mul_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_sub_mul_lane (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_xar (machine_mode);
inline insn_code
code_for_aarch64_sve2_xar (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_xar (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_xar (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_xar (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_xar (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_bcax (machine_mode);
inline insn_code
code_for_aarch64_sve2_bcax (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_bcax (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_bcax (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_bcax (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_bcax (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_eor3 (machine_mode);
inline insn_code
code_for_aarch64_sve2_eor3 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_eor3 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_eor3 (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_eor3 (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_eor3 (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_bsl (machine_mode);
inline insn_code
code_for_aarch64_sve2_bsl (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_bsl (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_bsl (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_bsl (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_bsl (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_nbsl (machine_mode);
inline insn_code
code_for_aarch64_sve2_nbsl (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_nbsl (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_nbsl (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_nbsl (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_nbsl (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_bsl1n (machine_mode);
inline insn_code
code_for_aarch64_sve2_bsl1n (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_bsl1n (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_bsl1n (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_bsl1n (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_bsl1n (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_bsl2n (machine_mode);
inline insn_code
code_for_aarch64_sve2_bsl2n (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_bsl2n (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_bsl2n (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_bsl2n (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_bsl2n (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_add (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve_add (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_add (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_add (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_add (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_add (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_aba (rtx_code, machine_mode);
inline insn_code
code_for_aarch64_sve2_aba (rtx_code arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve2_aba (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_aba (rtx_code, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_aba (rtx_code arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_aba (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_add_lane (int, machine_mode);
inline insn_code
code_for_aarch64_sve_add_lane (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_add_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_add_lane (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_add_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_add_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_dot (machine_mode);
inline insn_code
code_for_aarch64_sve_dot (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_dot (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_dot (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_dot (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_dot (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_dot_lane (machine_mode);
inline insn_code
code_for_aarch64_sve_dot_lane (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_dot_lane (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_dot_lane (machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_dot_lane (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_dot_lane (arg0, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_qadd (int, machine_mode);
inline insn_code
code_for_aarch64_sve_qadd (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_qadd (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_qadd (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_qadd (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_qadd (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_qadd_lane (int, machine_mode);
inline insn_code
code_for_aarch64_sve_qadd_lane (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_qadd_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_qadd_lane (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_qadd_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_qadd_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_sub (int, machine_mode);
inline insn_code
code_for_aarch64_sve_sub (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_sub (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_sub (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_sub (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_sub (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_sub_lane (int, machine_mode);
inline insn_code
code_for_aarch64_sve_sub_lane (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_sub_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_sub_lane (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_sub_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_sub_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_qsub (int, machine_mode);
inline insn_code
code_for_aarch64_sve_qsub (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_qsub (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_qsub (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_qsub (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_qsub (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_qsub_lane (int, machine_mode);
inline insn_code
code_for_aarch64_sve_qsub_lane (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_qsub_lane (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_qsub_lane (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_qsub_lane (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sve_qsub_lane (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sve (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sve (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve (int, machine_mode, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve (arg0, arg1, arg2, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_fp8_cvt (int, machine_mode);
inline insn_code
code_for_aarch64_sve2_fp8_cvt (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve2_fp8_cvt (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_fp8_cvt (int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve2_fp8_cvt (int arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve2_fp8_cvt (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_cvtxnt (machine_mode);
inline insn_code
code_for_aarch64_sve2_cvtxnt (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_cvtxnt (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_sve_cvtl (machine_mode);
inline insn_code
code_for_aarch64_sve_cvtl (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_cvtl (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_sve_cvtn (machine_mode);
inline insn_code
code_for_aarch64_sve_cvtn (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_cvtn (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_cvtn (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve_cvtn (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve_cvtn (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_fp8_cvtn (machine_mode);
inline insn_code
code_for_aarch64_sve2_fp8_cvtn (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_fp8_cvtn (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_fp8_cvtn (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sve2_fp8_cvtn (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sve2_fp8_cvtn (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_fp8_cvtnb (machine_mode);
inline insn_code
code_for_aarch64_sve2_fp8_cvtnb (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_fp8_cvtnb (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_sve2_pmul (machine_mode);
inline insn_code
code_for_aarch64_sve2_pmul (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_pmul (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_sve_sel (machine_mode);
inline insn_code
code_for_aarch64_sve_sel (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_sel (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_sel (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_sel (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_sel (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_while_b_x2 (int, int);
inline insn_code
code_for_aarch64_sve_while_b_x2 (int arg0, int arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_while_b_x2 (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_while_b_x2 (int, int, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_while_b_x2 (int arg0, int arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_while_b_x2 (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_while_c (int, int);
inline insn_code
code_for_aarch64_sve_while_c (int arg0, int arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_while_c (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_while_c (int, int, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_while_c (int arg0, int arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_while_c (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_dupq (machine_mode);
inline insn_code
code_for_aarch64_sve_dupq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_dupq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_dupq (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_dupq (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve_dupq (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve_extq (machine_mode);
inline insn_code
code_for_aarch64_sve_extq (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve_extq (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_extq (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_extq (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_extq (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_tbl2 (machine_mode);
inline insn_code
code_for_aarch64_sve2_tbl2 (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_tbl2 (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_tbl2 (machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_tbl2 (machine_mode arg0, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sve2_tbl2 (arg0, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_histcnt (machine_mode);
inline insn_code
code_for_aarch64_sve2_histcnt (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_histcnt (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve2_histcnt (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve2_histcnt (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve2_histcnt (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sve2_histseg (machine_mode);
inline insn_code
code_for_aarch64_sve2_histseg (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sve2_histseg (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern insn_code maybe_code_for_aarch64_sve_luti (int, machine_mode);
inline insn_code
code_for_aarch64_sve_luti (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sve_luti (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sve_luti (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sve_luti (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sve_luti (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme (int, machine_mode);
inline insn_code
code_for_aarch64_sme (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sme (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme (int, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sme (arg0, arg1, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sme (int, machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sme (int arg0, machine_mode arg1, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sme (arg0, arg1, x0, x1);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sme (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sme (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_plus (int, machine_mode);
inline insn_code
code_for_aarch64_sme_plus (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sme_plus (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_plus (int, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_plus (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sme_plus (arg0, arg1, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_ldrn (machine_mode);
inline insn_code
code_for_aarch64_sme_ldrn (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_ldrn (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_ldrn (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_ldrn (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sme_ldrn (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_strn (machine_mode);
inline insn_code
code_for_aarch64_sme_strn (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_strn (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_strn (machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_strn (machine_mode arg0, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sme_strn (arg0, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sme (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sme (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3, rtx x4)
{
  rtx res = maybe_gen_aarch64_sme (arg0, arg1, arg2, x0, x1, x2, x3, x4);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sme (int, machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sme (arg0, arg1, arg2, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern rtx maybe_gen_aarch64_sme (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sme (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_read (machine_mode);
inline insn_code
code_for_aarch64_sme_read (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_read (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_read (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sme_read (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sme_read (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_readz (machine_mode);
inline insn_code
code_for_aarch64_sme_readz (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_readz (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_readz (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sme_readz (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sme_readz (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_write (machine_mode);
inline insn_code
code_for_aarch64_sme_write (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_write (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_write (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sme_write (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sme_write (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_write_zt (machine_mode);
inline insn_code
code_for_aarch64_sme_write_zt (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_write_zt (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_write_zt (machine_mode, rtx, rtx);
inline rtx
gen_aarch64_sme_write_zt (machine_mode arg0, rtx x0, rtx x1)
{
  rtx res = maybe_gen_aarch64_sme_write_zt (arg0, x0, x1);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_zero_za_slices (machine_mode);
inline insn_code
code_for_aarch64_sme_zero_za_slices (machine_mode arg0)
{
  insn_code code = maybe_code_for_aarch64_sme_zero_za_slices (arg0);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_zero_za_slices (machine_mode, rtx);
inline rtx
gen_aarch64_sme_zero_za_slices (machine_mode arg0, rtx x0)
{
  rtx res = maybe_gen_aarch64_sme_zero_za_slices (arg0, x0);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_single (int, machine_mode);
inline insn_code
code_for_aarch64_sme_single (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sme_single (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_single (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_single (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sme_single (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_single (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sme_single (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sme_single (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_single (int, machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_single (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sme_single (arg0, arg1, arg2, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_single_sudot (machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sme_single_sudot (machine_mode arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sme_single_sudot (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_single_sudot (machine_mode, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_single_sudot (machine_mode arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sme_single_sudot (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_lane (int, machine_mode, machine_mode);
inline insn_code
code_for_aarch64_sme_lane (int arg0, machine_mode arg1, machine_mode arg2)
{
  insn_code code = maybe_code_for_aarch64_sme_lane (arg0, arg1, arg2);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_lane (int, machine_mode, machine_mode, rtx, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_lane (int arg0, machine_mode arg1, machine_mode arg2, rtx x0, rtx x1, rtx x2, rtx x3)
{
  rtx res = maybe_gen_aarch64_sme_lane (arg0, arg1, arg2, x0, x1, x2, x3);
  gcc_assert (res);
  return res;
}

extern insn_code maybe_code_for_aarch64_sme_lut (int, machine_mode);
inline insn_code
code_for_aarch64_sme_lut (int arg0, machine_mode arg1)
{
  insn_code code = maybe_code_for_aarch64_sme_lut (arg0, arg1);
  gcc_assert (code != CODE_FOR_nothing);
  return code;
}

extern rtx maybe_gen_aarch64_sme_lut (int, machine_mode, rtx, rtx, rtx);
inline rtx
gen_aarch64_sme_lut (int arg0, machine_mode arg1, rtx x0, rtx x1, rtx x2)
{
  rtx res = maybe_gen_aarch64_sme_lut (arg0, arg1, x0, x1, x2);
  gcc_assert (res);
  return res;
}
#endif

extern const struct convert_optab_libcall_d convlib_def[NUM_CONVLIB_OPTABS];
extern const struct optab_libcall_d normlib_def[NUM_NORMLIB_OPTABS];

/* Returns the active icode for the given (encoded) optab.  */
extern enum insn_code raw_optab_handler (unsigned);
extern bool swap_optab_enable (optab, machine_mode, bool);

/* Target-dependent globals.  */
struct target_optabs {
  /* Patterns that are used by optabs that are enabled for this target.  */
  bool pat_enable[NUM_OPTAB_PATTERNS];

  /* Index VOIDmode caches if the target supports vec_gather_load for any
     vector mode.  Every other index X caches specifically for mode X.
     1 means yes, -1 means no.  */
  signed char supports_vec_gather_load[NUM_MACHINE_MODES];
  signed char supports_vec_scatter_store[NUM_MACHINE_MODES];
};
extern void init_all_optabs (struct target_optabs *);
extern bool partial_vectors_supported_p (void);

extern struct target_optabs default_target_optabs;
extern struct target_optabs *this_fn_optabs;
#if SWITCHABLE_TARGET
extern struct target_optabs *this_target_optabs;
#else
#define this_target_optabs (&default_target_optabs)
#endif
#endif
