/* Type information for GCC.
   Copyright (C) 2004-2025 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

/* This file is machine generated.  Do not edit.  */

/* GC marker procedures.  */
/* Macros and declarations.  */
#define gt_ggc_m_9tree_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_node (X);\
  } while (0)
#define gt_ggc_mx_tree_node gt_ggc_mx_lang_tree_node
#define gt_ggc_m_9line_maps(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_line_maps (X);\
  } while (0)
extern void gt_ggc_mx_line_maps (void *);
#define gt_ggc_m_9cpp_token(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cpp_token (X);\
  } while (0)
extern void gt_ggc_mx_cpp_token (void *);
#define gt_ggc_m_9cpp_macro(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cpp_macro (X);\
  } while (0)
extern void gt_ggc_mx_cpp_macro (void *);
#define gt_ggc_m_18cpp_hashnode_extra(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cpp_hashnode_extra (X);\
  } while (0)
extern void gt_ggc_mx_cpp_hashnode_extra (void *);
#define gt_ggc_m_13string_concat(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_string_concat (X);\
  } while (0)
extern void gt_ggc_mx_string_concat (void *);
#define gt_ggc_m_16string_concat_db(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_string_concat_db (X);\
  } while (0)
extern void gt_ggc_mx_string_concat_db (void *);
#define gt_ggc_m_38hash_map_location_hash_string_concat__(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_location_hash_string_concat__ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_location_hash_string_concat__ (void *);
#define gt_ggc_m_11bitmap_head(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_bitmap_head (X);\
  } while (0)
extern void gt_ggc_mx_bitmap_head (void *);
#define gt_ggc_m_7rtx_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rtx_def (X);\
  } while (0)
extern void gt_ggc_mx_rtx_def (void *);
#define gt_ggc_m_9rtvec_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rtvec_def (X);\
  } while (0)
extern void gt_ggc_mx_rtvec_def (void *);
#define gt_ggc_m_6gimple(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_gimple (X);\
  } while (0)
extern void gt_ggc_mx_gimple (void *);
#define gt_ggc_m_11dw_cfi_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_cfi_node (X);\
  } while (0)
extern void gt_ggc_mx_dw_cfi_node (void *);
#define gt_ggc_m_11symtab_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_symtab_node (X);\
  } while (0)
extern void gt_ggc_mx_symtab_node (void *);
#define gt_ggc_m_11cgraph_edge(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cgraph_edge (X);\
  } while (0)
extern void gt_ggc_mx_cgraph_edge (void *);
#define gt_ggc_m_7section(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_section (X);\
  } while (0)
extern void gt_ggc_mx_section (void *);
#define gt_ggc_m_16cl_target_option(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cl_target_option (X);\
  } while (0)
extern void gt_ggc_mx_cl_target_option (void *);
#define gt_ggc_m_15cl_optimization(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cl_optimization (X);\
  } while (0)
extern void gt_ggc_mx_cl_optimization (void *);
#define gt_ggc_m_8edge_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_edge_def (X);\
  } while (0)
extern void gt_ggc_mx_edge_def (void *);
#define gt_ggc_m_15basic_block_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_basic_block_def (X);\
  } while (0)
extern void gt_ggc_mx_basic_block_def (void *);
#define gt_ggc_m_26vec_unsigned_va_gc_atomic_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_unsigned_va_gc_atomic_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_unsigned_va_gc_atomic_ (void *);
#define gt_ggc_m_14hash_set_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_set_tree_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_set_tree_ (void *);
#define gt_ggc_m_16machine_function(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_machine_function (X);\
  } while (0)
extern void gt_ggc_mx_machine_function (void *);
#define gt_ggc_m_14bitmap_element(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_bitmap_element (X);\
  } while (0)
extern void gt_ggc_mx_bitmap_element (void *);
#define gt_ggc_m_13coverage_data(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_coverage_data (X);\
  } while (0)
extern void gt_ggc_mx_coverage_data (void *);
#define gt_ggc_m_9mem_attrs(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_mem_attrs (X);\
  } while (0)
extern void gt_ggc_mx_mem_attrs (void *);
#define gt_ggc_m_9reg_attrs(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_reg_attrs (X);\
  } while (0)
extern void gt_ggc_mx_reg_attrs (void *);
#define gt_ggc_m_12object_block(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_object_block (X);\
  } while (0)
extern void gt_ggc_mx_object_block (void *);
#define gt_ggc_m_14vec_rtx_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_rtx_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_rtx_va_gc_ (void *);
#define gt_ggc_m_11fixed_value(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_fixed_value (X);\
  } while (0)
extern void gt_ggc_mx_fixed_value (void *);
#define gt_ggc_m_23constant_descriptor_rtx(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_constant_descriptor_rtx (X);\
  } while (0)
extern void gt_ggc_mx_constant_descriptor_rtx (void *);
#define gt_ggc_m_8function(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_function (X);\
  } while (0)
extern void gt_ggc_mx_function (void *);
#define gt_ggc_m_10target_rtl(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_target_rtl (X);\
  } while (0)
extern void gt_ggc_mx_target_rtl (void *);
#define gt_ggc_m_15cgraph_rtl_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cgraph_rtl_info (X);\
  } while (0)
extern void gt_ggc_mx_cgraph_rtl_info (void *);
#define gt_ggc_m_42hash_map_tree_tree_decl_tree_cache_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_tree_decl_tree_cache_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_tree_decl_tree_cache_traits_ (void *);
#define gt_ggc_m_42hash_map_tree_tree_type_tree_cache_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_tree_type_tree_cache_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_tree_type_tree_cache_traits_ (void *);
#define gt_ggc_m_36hash_map_tree_tree_decl_tree_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_tree_decl_tree_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_tree_decl_tree_traits_ (void *);
#define gt_ggc_m_12ptr_info_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ptr_info_def (X);\
  } while (0)
extern void gt_ggc_mx_ptr_info_def (void *);
#define gt_ggc_m_10die_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_die_struct (X);\
  } while (0)
extern void gt_ggc_mx_die_struct (void *);
#define gt_ggc_m_26vec_constructor_elt_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_constructor_elt_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_constructor_elt_va_gc_ (void *);
#define gt_ggc_m_14vrange_storage(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vrange_storage (X);\
  } while (0)
extern void gt_ggc_mx_vrange_storage (void *);
#define gt_ggc_m_15vec_tree_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_tree_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_tree_va_gc_ (void *);
#define gt_ggc_m_9lang_type(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_lang_type (X);\
  } while (0)
extern void gt_ggc_mx_lang_type (void *);
#define gt_ggc_m_9lang_decl(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_lang_decl (X);\
  } while (0)
extern void gt_ggc_mx_lang_decl (void *);
#define gt_ggc_m_24tree_statement_list_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_statement_list_node (X);\
  } while (0)
extern void gt_ggc_mx_tree_statement_list_node (void *);
#define gt_ggc_m_14target_globals(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_target_globals (X);\
  } while (0)
extern void gt_ggc_mx_target_globals (void *);
#define gt_ggc_m_14lang_tree_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_lang_tree_node (X);\
  } while (0)
extern void gt_ggc_mx_lang_tree_node (void *);
#define gt_ggc_m_8tree_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_map (X);\
  } while (0)
extern void gt_ggc_mx_tree_map (void *);
#define gt_ggc_m_13tree_decl_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_decl_map (X);\
  } while (0)
extern void gt_ggc_mx_tree_decl_map (void *);
#define gt_ggc_m_12tree_int_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_int_map (X);\
  } while (0)
extern void gt_ggc_mx_tree_int_map (void *);
#define gt_ggc_m_12tree_vec_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_vec_map (X);\
  } while (0)
extern void gt_ggc_mx_tree_vec_map (void *);
#define gt_ggc_m_21vec_alias_pair_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_alias_pair_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_alias_pair_va_gc_ (void *);
#define gt_ggc_m_13libfunc_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_libfunc_entry (X);\
  } while (0)
extern void gt_ggc_mx_libfunc_entry (void *);
#define gt_ggc_m_26hash_table_libfunc_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_libfunc_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_libfunc_hasher_ (void *);
#define gt_ggc_m_15target_libfuncs(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_target_libfuncs (X);\
  } while (0)
extern void gt_ggc_mx_target_libfuncs (void *);
#define gt_ggc_m_14sequence_stack(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_sequence_stack (X);\
  } while (0)
extern void gt_ggc_mx_sequence_stack (void *);
#define gt_ggc_m_20vec_rtx_insn__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_rtx_insn__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_rtx_insn__va_gc_ (void *);
#define gt_ggc_m_18call_site_record_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_call_site_record_d (X);\
  } while (0)
extern void gt_ggc_mx_call_site_record_d (void *);
#define gt_ggc_m_16vec_uchar_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_uchar_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_uchar_va_gc_ (void *);
#define gt_ggc_m_27vec_call_site_record_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_call_site_record_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_call_site_record_va_gc_ (void *);
#define gt_ggc_m_9gimple_df(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_gimple_df (X);\
  } while (0)
extern void gt_ggc_mx_gimple_df (void *);
#define gt_ggc_m_11dw_fde_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_fde_node (X);\
  } while (0)
extern void gt_ggc_mx_dw_fde_node (void *);
#define gt_ggc_m_17rtx_constant_pool(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rtx_constant_pool (X);\
  } while (0)
extern void gt_ggc_mx_rtx_constant_pool (void *);
#define gt_ggc_m_11frame_space(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_frame_space (X);\
  } while (0)
extern void gt_ggc_mx_frame_space (void *);
#define gt_ggc_m_26vec_callinfo_callee_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_callinfo_callee_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_callinfo_callee_va_gc_ (void *);
#define gt_ggc_m_26vec_callinfo_dalloc_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_callinfo_dalloc_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_callinfo_dalloc_va_gc_ (void *);
#define gt_ggc_m_11stack_usage(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_stack_usage (X);\
  } while (0)
extern void gt_ggc_mx_stack_usage (void *);
#define gt_ggc_m_9eh_status(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_eh_status (X);\
  } while (0)
extern void gt_ggc_mx_eh_status (void *);
#define gt_ggc_m_18control_flow_graph(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_control_flow_graph (X);\
  } while (0)
extern void gt_ggc_mx_control_flow_graph (void *);
#define gt_ggc_m_5loops(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_loops (X);\
  } while (0)
extern void gt_ggc_mx_loops (void *);
#define gt_ggc_m_17language_function(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_language_function (X);\
  } while (0)
extern void gt_ggc_mx_language_function (void *);
#define gt_ggc_m_24types_used_by_vars_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_types_used_by_vars_entry (X);\
  } while (0)
extern void gt_ggc_mx_types_used_by_vars_entry (void *);
#define gt_ggc_m_28hash_table_used_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_used_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_used_type_hasher_ (void *);
#define gt_ggc_m_13nb_iter_bound(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_nb_iter_bound (X);\
  } while (0)
extern void gt_ggc_mx_nb_iter_bound (void *);
#define gt_ggc_m_9loop_exit(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_loop_exit (X);\
  } while (0)
extern void gt_ggc_mx_loop_exit (void *);
#define gt_ggc_m_4loop(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_loop (X);\
  } while (0)
extern void gt_ggc_mx_loop (void *);
#define gt_ggc_m_10control_iv(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_control_iv (X);\
  } while (0)
extern void gt_ggc_mx_control_iv (void *);
#define gt_ggc_m_17vec_loop_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_loop_p_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_loop_p_va_gc_ (void *);
#define gt_ggc_m_10niter_desc(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_niter_desc (X);\
  } while (0)
extern void gt_ggc_mx_niter_desc (void *);
#define gt_ggc_m_28hash_table_loop_exit_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_loop_exit_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_loop_exit_hasher_ (void *);
#define gt_ggc_m_22vec_basic_block_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_basic_block_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_basic_block_va_gc_ (void *);
#define gt_ggc_m_11rtl_bb_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rtl_bb_info (X);\
  } while (0)
extern void gt_ggc_mx_rtl_bb_info (void *);
#define gt_ggc_m_15vec_edge_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_edge_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_edge_va_gc_ (void *);
#define gt_ggc_m_18section_hash_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_section_hash_entry (X);\
  } while (0)
extern void gt_ggc_mx_section_hash_entry (void *);
#define gt_ggc_m_18lto_file_decl_data(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_lto_file_decl_data (X);\
  } while (0)
extern void gt_ggc_mx_lto_file_decl_data (void *);
#define gt_ggc_m_15ipa_replace_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_replace_map (X);\
  } while (0)
extern void gt_ggc_mx_ipa_replace_map (void *);
#define gt_ggc_m_17cgraph_simd_clone(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cgraph_simd_clone (X);\
  } while (0)
extern void gt_ggc_mx_cgraph_simd_clone (void *);
#define gt_ggc_m_28cgraph_function_version_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cgraph_function_version_info (X);\
  } while (0)
extern void gt_ggc_mx_cgraph_function_version_info (void *);
#define gt_ggc_m_30hash_table_cgraph_edge_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_cgraph_edge_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_cgraph_edge_hasher_ (void *);
#define gt_ggc_m_25cgraph_indirect_call_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cgraph_indirect_call_info (X);\
  } while (0)
extern void gt_ggc_mx_cgraph_indirect_call_info (void *);
#define gt_ggc_m_8asm_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_asm_node (X);\
  } while (0)
extern void gt_ggc_mx_asm_node (void *);
#define gt_ggc_m_10thunk_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_thunk_info (X);\
  } while (0)
extern void gt_ggc_mx_thunk_info (void *);
#define gt_ggc_m_29function_summary_thunk_info__(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_function_summary_thunk_info__ (X);\
  } while (0)
extern void gt_ggc_mx_function_summary_thunk_info__ (void *);
#define gt_ggc_m_10clone_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_clone_info (X);\
  } while (0)
extern void gt_ggc_mx_clone_info (void *);
#define gt_ggc_m_29function_summary_clone_info__(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_function_summary_clone_info__ (X);\
  } while (0)
extern void gt_ggc_mx_function_summary_clone_info__ (void *);
#define gt_ggc_m_12symbol_table(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_symbol_table (X);\
  } while (0)
extern void gt_ggc_mx_symbol_table (void *);
#define gt_ggc_m_31hash_table_section_name_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_section_name_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_section_name_hasher_ (void *);
#define gt_ggc_m_26hash_table_asmname_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_asmname_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_asmname_hasher_ (void *);
#define gt_ggc_m_42hash_map_symtab_node__symbol_priority_map_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_symtab_node__symbol_priority_map_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_symtab_node__symbol_priority_map_ (void *);
#define gt_ggc_m_24constant_descriptor_tree(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_constant_descriptor_tree (X);\
  } while (0)
extern void gt_ggc_mx_constant_descriptor_tree (void *);
#define gt_ggc_m_28vec_unprocessed_thunk_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_unprocessed_thunk_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_unprocessed_thunk_va_gc_ (void *);
#define gt_ggc_m_27vec_ipa_replace_map__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_replace_map__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_replace_map__va_gc_ (void *);
#define gt_ggc_m_21ipa_param_adjustments(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_param_adjustments (X);\
  } while (0)
extern void gt_ggc_mx_ipa_param_adjustments (void *);
#define gt_ggc_m_28hash_map_alias_set_hash_int_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_alias_set_hash_int_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_alias_set_hash_int_ (void *);
#define gt_ggc_m_15alias_set_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_alias_set_entry (X);\
  } while (0)
extern void gt_ggc_mx_alias_set_entry (void *);
#define gt_ggc_m_27vec_alias_set_entry__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_alias_set_entry__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_alias_set_entry__va_gc_ (void *);
#define gt_ggc_m_35hash_table_function_version_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_function_version_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_function_version_hasher_ (void *);
#define gt_ggc_m_17lto_in_decl_state(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_lto_in_decl_state (X);\
  } while (0)
extern void gt_ggc_mx_lto_in_decl_state (void *);
#define gt_ggc_m_34hash_table_ipa_vr_ggc_hash_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_ipa_vr_ggc_hash_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_ipa_vr_ggc_hash_traits_ (void *);
#define gt_ggc_m_6ipa_vr(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_vr (X);\
  } while (0)
extern void gt_ggc_mx_ipa_vr (void *);
#define gt_ggc_m_24ipa_return_value_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_return_value_summary (X);\
  } while (0)
extern void gt_ggc_mx_ipa_return_value_summary (void *);
#define gt_ggc_m_43function_summary_ipa_return_value_summary__(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_function_summary_ipa_return_value_summary__ (X);\
  } while (0)
extern void gt_ggc_mx_function_summary_ipa_return_value_summary__ (void *);
#define gt_ggc_m_15ipa_node_params(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_node_params (X);\
  } while (0)
extern void gt_ggc_mx_ipa_node_params (void *);
#define gt_ggc_m_13ipa_edge_args(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_edge_args (X);\
  } while (0)
extern void gt_ggc_mx_ipa_edge_args (void *);
#define gt_ggc_m_14ipa_fn_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_fn_summary (X);\
  } while (0)
extern void gt_ggc_mx_ipa_fn_summary (void *);
#define gt_ggc_m_10odr_type_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_odr_type_d (X);\
  } while (0)
extern void gt_ggc_mx_odr_type_d (void *);
#define gt_ggc_m_29vec_ipa_adjusted_param_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_adjusted_param_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_adjusted_param_va_gc_ (void *);
#define gt_ggc_m_12param_access(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_param_access (X);\
  } while (0)
extern void gt_ggc_mx_param_access (void *);
#define gt_ggc_m_24vec_param_access__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_param_access__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_param_access__va_gc_ (void *);
#define gt_ggc_m_17isra_func_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_isra_func_summary (X);\
  } while (0)
extern void gt_ggc_mx_isra_func_summary (void *);
#define gt_ggc_m_26vec_isra_param_desc_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_isra_param_desc_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_isra_param_desc_va_gc_ (void *);
#define gt_ggc_m_26ipa_sra_function_summaries(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_sra_function_summaries (X);\
  } while (0)
extern void gt_ggc_mx_ipa_sra_function_summaries (void *);
#define gt_ggc_m_27modref_tree_alias_set_type_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_modref_tree_alias_set_type_ (X);\
  } while (0)
extern void gt_ggc_mx_modref_tree_alias_set_type_ (void *);
#define gt_ggc_m_14modref_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_modref_summary (X);\
  } while (0)
extern void gt_ggc_mx_modref_summary (void *);
#define gt_ggc_m_18modref_summary_lto(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_modref_summary_lto (X);\
  } while (0)
extern void gt_ggc_mx_modref_summary_lto (void *);
#define gt_ggc_m_44fast_function_summary_modref_summary__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_fast_function_summary_modref_summary__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_fast_function_summary_modref_summary__va_gc_ (void *);
#define gt_ggc_m_48fast_function_summary_modref_summary_lto__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_fast_function_summary_modref_summary_lto__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_fast_function_summary_modref_summary_lto__va_gc_ (void *);
#define gt_ggc_m_17modref_tree_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_modref_tree_tree_ (X);\
  } while (0)
extern void gt_ggc_mx_modref_tree_tree_ (void *);
#define gt_ggc_m_37hash_map_location_hash_nowarn_spec_t_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_location_hash_nowarn_spec_t_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_location_hash_nowarn_spec_t_ (void *);
#define gt_ggc_m_17dw_loc_descr_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_loc_descr_node (X);\
  } while (0)
extern void gt_ggc_mx_dw_loc_descr_node (void *);
#define gt_ggc_m_18dw_loc_list_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_loc_list_struct (X);\
  } while (0)
extern void gt_ggc_mx_dw_loc_list_struct (void *);
#define gt_ggc_m_18dw_discr_list_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_discr_list_node (X);\
  } while (0)
extern void gt_ggc_mx_dw_discr_list_node (void *);
#define gt_ggc_m_11dw_wide_int(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_wide_int (X);\
  } while (0)
extern void gt_ggc_mx_dw_wide_int (void *);
#define gt_ggc_m_15dw_cfa_location(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_cfa_location (X);\
  } while (0)
extern void gt_ggc_mx_dw_cfa_location (void *);
#define gt_ggc_m_21vec_dw_cfi_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_cfi_ref_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_cfi_ref_va_gc_ (void *);
#define gt_ggc_m_16addr_table_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_addr_table_entry (X);\
  } while (0)
extern void gt_ggc_mx_addr_table_entry (void *);
#define gt_ggc_m_20indirect_string_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_indirect_string_node (X);\
  } while (0)
extern void gt_ggc_mx_indirect_string_node (void *);
#define gt_ggc_m_15dwarf_file_data(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dwarf_file_data (X);\
  } while (0)
extern void gt_ggc_mx_dwarf_file_data (void *);
#define gt_ggc_m_20hash_map_char__tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_char__tree_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_char__tree_ (void *);
#define gt_ggc_m_10dw_cfi_row(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_cfi_row (X);\
  } while (0)
extern void gt_ggc_mx_dw_cfi_row (void *);
#define gt_ggc_m_17reg_saved_in_data(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_reg_saved_in_data (X);\
  } while (0)
extern void gt_ggc_mx_reg_saved_in_data (void *);
#define gt_ggc_m_21vec_dw_fde_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_fde_ref_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_fde_ref_va_gc_ (void *);
#define gt_ggc_m_34hash_table_indirect_string_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_indirect_string_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_indirect_string_hasher_ (void *);
#define gt_ggc_m_16vec_char__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_char__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_char__va_gc_ (void *);
#define gt_ggc_m_16comdat_type_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_comdat_type_node (X);\
  } while (0)
extern void gt_ggc_mx_comdat_type_node (void *);
#define gt_ggc_m_29vec_dw_line_info_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_line_info_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_line_info_entry_va_gc_ (void *);
#define gt_ggc_m_18dw_line_info_table(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_dw_line_info_table (X);\
  } while (0)
extern void gt_ggc_mx_dw_line_info_table (void *);
#define gt_ggc_m_23vec_dw_attr_node_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_attr_node_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_attr_node_va_gc_ (void *);
#define gt_ggc_m_16limbo_die_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_limbo_die_struct (X);\
  } while (0)
extern void gt_ggc_mx_limbo_die_struct (void *);
#define gt_ggc_m_29hash_table_dwarf_file_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_dwarf_file_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_dwarf_file_hasher_ (void *);
#define gt_ggc_m_27hash_table_decl_die_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_decl_die_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_decl_die_hasher_ (void *);
#define gt_ggc_m_21vec_dw_die_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_die_ref_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_die_ref_va_gc_ (void *);
#define gt_ggc_m_21variable_value_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_variable_value_struct (X);\
  } while (0)
extern void gt_ggc_mx_variable_value_struct (void *);
#define gt_ggc_m_33hash_table_variable_value_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_variable_value_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_variable_value_hasher_ (void *);
#define gt_ggc_m_28hash_table_block_die_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_block_die_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_block_die_hasher_ (void *);
#define gt_ggc_m_12var_loc_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_var_loc_node (X);\
  } while (0)
extern void gt_ggc_mx_var_loc_node (void *);
#define gt_ggc_m_16var_loc_list_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_var_loc_list_def (X);\
  } while (0)
extern void gt_ggc_mx_var_loc_list_def (void *);
#define gt_ggc_m_17call_arg_loc_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_call_arg_loc_node (X);\
  } while (0)
extern void gt_ggc_mx_call_arg_loc_node (void *);
#define gt_ggc_m_27hash_table_decl_loc_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_decl_loc_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_decl_loc_hasher_ (void *);
#define gt_ggc_m_22cached_dw_loc_list_def(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cached_dw_loc_list_def (X);\
  } while (0)
extern void gt_ggc_mx_cached_dw_loc_list_def (void *);
#define gt_ggc_m_30hash_table_dw_loc_list_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_dw_loc_list_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_dw_loc_list_hasher_ (void *);
#define gt_ggc_m_30vec_dw_line_info_table__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_line_info_table__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_line_info_table__va_gc_ (void *);
#define gt_ggc_m_24vec_pubname_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_pubname_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_pubname_entry_va_gc_ (void *);
#define gt_ggc_m_24vec_macinfo_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_macinfo_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_macinfo_entry_va_gc_ (void *);
#define gt_ggc_m_20vec_dw_ranges_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_ranges_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_ranges_va_gc_ (void *);
#define gt_ggc_m_29vec_dw_ranges_by_label_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_dw_ranges_by_label_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_dw_ranges_by_label_va_gc_ (void *);
#define gt_ggc_m_24vec_die_arg_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_die_arg_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_die_arg_entry_va_gc_ (void *);
#define gt_ggc_m_23hash_table_addr_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_addr_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_addr_hasher_ (void *);
#define gt_ggc_m_27hash_map_tree_sym_off_pair_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_sym_off_pair_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_sym_off_pair_ (void *);
#define gt_ggc_m_17inline_entry_data(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_inline_entry_data (X);\
  } while (0)
extern void gt_ggc_mx_inline_entry_data (void *);
#define gt_ggc_m_36hash_table_inline_entry_data_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_inline_entry_data_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_inline_entry_data_hasher_ (void *);
#define gt_ggc_m_9ctf_dtdef(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ctf_dtdef (X);\
  } while (0)
extern void gt_ggc_mx_ctf_dtdef (void *);
#define gt_ggc_m_10ctf_string(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ctf_string (X);\
  } while (0)
extern void gt_ggc_mx_ctf_string (void *);
#define gt_ggc_m_9ctf_dmdef(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ctf_dmdef (X);\
  } while (0)
extern void gt_ggc_mx_ctf_dmdef (void *);
#define gt_ggc_m_12ctf_func_arg(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ctf_func_arg (X);\
  } while (0)
extern void gt_ggc_mx_ctf_func_arg (void *);
#define gt_ggc_m_9ctf_dvdef(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ctf_dvdef (X);\
  } while (0)
extern void gt_ggc_mx_ctf_dvdef (void *);
#define gt_ggc_m_27hash_table_ctfc_dtd_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_ctfc_dtd_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_ctfc_dtd_hasher_ (void *);
#define gt_ggc_m_27hash_table_ctfc_dvd_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_ctfc_dvd_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_ctfc_dvd_hasher_ (void *);
#define gt_ggc_m_13ctf_container(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ctf_container (X);\
  } while (0)
extern void gt_ggc_mx_ctf_container (void *);
#define gt_ggc_m_24vec_ctf_dtdef_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ctf_dtdef_ref_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ctf_dtdef_ref_va_gc_ (void *);
#define gt_ggc_m_37hash_map_ctf_dtdef_ref_ctf_dtdef_ref_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_ctf_dtdef_ref_ctf_dtdef_ref_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_ctf_dtdef_ref_ctf_dtdef_ref_ (void *);
#define gt_ggc_m_23hash_set_ctf_dtdef_ref_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_set_ctf_dtdef_ref_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_set_ctf_dtdef_ref_ (void *);
#define gt_ggc_m_9temp_slot(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_temp_slot (X);\
  } while (0)
extern void gt_ggc_mx_temp_slot (void *);
#define gt_ggc_m_20initial_value_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_initial_value_struct (X);\
  } while (0)
extern void gt_ggc_mx_initial_value_struct (void *);
#define gt_ggc_m_22vec_temp_slot_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_temp_slot_p_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_temp_slot_p_va_gc_ (void *);
#define gt_ggc_m_28hash_table_const_int_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_const_int_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_const_int_hasher_ (void *);
#define gt_ggc_m_33hash_table_const_wide_int_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_const_wide_int_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_const_wide_int_hasher_ (void *);
#define gt_ggc_m_33hash_table_const_poly_int_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_const_poly_int_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_const_poly_int_hasher_ (void *);
#define gt_ggc_m_27hash_table_reg_attr_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_reg_attr_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_reg_attr_hasher_ (void *);
#define gt_ggc_m_31hash_table_const_double_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_const_double_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_const_double_hasher_ (void *);
#define gt_ggc_m_30hash_table_const_fixed_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_const_fixed_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_const_fixed_hasher_ (void *);
#define gt_ggc_m_11eh_region_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_eh_region_d (X);\
  } while (0)
extern void gt_ggc_mx_eh_region_d (void *);
#define gt_ggc_m_16eh_landing_pad_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_eh_landing_pad_d (X);\
  } while (0)
extern void gt_ggc_mx_eh_landing_pad_d (void *);
#define gt_ggc_m_10eh_catch_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_eh_catch_d (X);\
  } while (0)
extern void gt_ggc_mx_eh_catch_d (void *);
#define gt_ggc_m_20vec_eh_region_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_eh_region_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_eh_region_va_gc_ (void *);
#define gt_ggc_m_25vec_eh_landing_pad_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_eh_landing_pad_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_eh_landing_pad_va_gc_ (void *);
#define gt_ggc_m_21hash_map_gimple__int_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_gimple__int_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_gimple__int_ (void *);
#define gt_ggc_m_29hash_table_insn_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_insn_cache_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_insn_cache_hasher_ (void *);
#define gt_ggc_m_23temp_slot_address_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_temp_slot_address_entry (X);\
  } while (0)
extern void gt_ggc_mx_temp_slot_address_entry (void *);
#define gt_ggc_m_31hash_table_temp_address_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_temp_address_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_temp_address_hasher_ (void *);
#define gt_ggc_m_24hash_map_tree_hash_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_hash_tree_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_hash_tree_ (void *);
#define gt_ggc_m_11test_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_test_struct (X);\
  } while (0)
extern void gt_ggc_mx_test_struct (void *);
#define gt_ggc_m_14test_of_length(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_test_of_length (X);\
  } while (0)
extern void gt_ggc_mx_test_of_length (void *);
#define gt_ggc_m_10test_other(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_test_other (X);\
  } while (0)
extern void gt_ggc_mx_test_other (void *);
#define gt_ggc_m_13test_of_union(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_test_of_union (X);\
  } while (0)
extern void gt_ggc_mx_test_of_union (void *);
#define gt_ggc_m_12example_base(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_example_base (X);\
  } while (0)
extern void gt_ggc_mx_example_base (void *);
#define gt_ggc_m_9test_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_test_node (X);\
  } while (0)
extern void gt_ggc_mx_test_node (void *);
#define gt_ggc_m_11user_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_user_struct (X);\
  } while (0)
extern void gt_ggc_mx_user_struct (void *);
#define gt_ggc_m_31hash_table_libfunc_decl_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_libfunc_decl_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_libfunc_decl_hasher_ (void *);
#define gt_ggc_m_16string_pool_data(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_string_pool_data (X);\
  } while (0)
extern void gt_ggc_mx_string_pool_data (void *);
#define gt_ggc_m_22string_pool_data_extra(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_string_pool_data_extra (X);\
  } while (0)
extern void gt_ggc_mx_string_pool_data_extra (void *);
#define gt_ggc_m_9type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_type_hash (X);\
  } while (0)
extern void gt_ggc_mx_type_hash (void *);
#define gt_ggc_m_29hash_table_type_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_type_cache_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_type_cache_hasher_ (void *);
#define gt_ggc_m_26hash_table_int_cst_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_int_cst_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_int_cst_hasher_ (void *);
#define gt_ggc_m_31hash_table_poly_int_cst_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_poly_int_cst_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_poly_int_cst_hasher_ (void *);
#define gt_ggc_m_28hash_table_cl_option_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_cl_option_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_cl_option_hasher_ (void *);
#define gt_ggc_m_38hash_table_tree_decl_map_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tree_decl_map_cache_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tree_decl_map_cache_hasher_ (void *);
#define gt_ggc_m_37hash_table_tree_vec_map_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tree_vec_map_cache_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tree_vec_map_cache_hasher_ (void *);
#define gt_ggc_m_43hash_map_tree_long_identifier_count_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_long_identifier_count_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_long_identifier_count_traits_ (void *);
#define gt_ggc_m_26hash_table_section_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_section_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_section_hasher_ (void *);
#define gt_ggc_m_31hash_table_object_block_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_object_block_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_object_block_hasher_ (void *);
#define gt_ggc_m_34hash_table_tree_descriptor_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tree_descriptor_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tree_descriptor_hasher_ (void *);
#define gt_ggc_m_33hash_table_const_rtx_desc_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_const_rtx_desc_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_const_rtx_desc_hasher_ (void *);
#define gt_ggc_m_27hash_table_tm_clone_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tm_clone_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tm_clone_hasher_ (void *);
#define gt_ggc_m_15tm_restart_node(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tm_restart_node (X);\
  } while (0)
extern void gt_ggc_mx_tm_restart_node (void *);
#define gt_ggc_m_19hash_map_tree_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_tree_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_tree_ (void *);
#define gt_ggc_m_27hash_table_ssa_name_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_ssa_name_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_ssa_name_hasher_ (void *);
#define gt_ggc_m_29hash_table_tm_restart_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tm_restart_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tm_restart_hasher_ (void *);
#define gt_ggc_m_28vec_mem_addr_template_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_mem_addr_template_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_mem_addr_template_va_gc_ (void *);
#define gt_ggc_m_13scev_info_str(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_scev_info_str (X);\
  } while (0)
extern void gt_ggc_mx_scev_info_str (void *);
#define gt_ggc_m_28hash_table_scev_info_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_scev_info_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_scev_info_hasher_ (void *);
#define gt_ggc_m_20ssa_operand_memory_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ssa_operand_memory_d (X);\
  } while (0)
extern void gt_ggc_mx_ssa_operand_memory_d (void *);
#define gt_ggc_m_24hash_map_char__unsigned_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_char__unsigned_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_char__unsigned_ (void *);
#define gt_ggc_m_18vec_gimple__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_gimple__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_gimple__va_gc_ (void *);
#define gt_ggc_m_26vec_ipa_agg_jf_item_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_agg_jf_item_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_agg_jf_item_va_gc_ (void *);
#define gt_ggc_m_19ipcp_transformation(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipcp_transformation (X);\
  } while (0)
extern void gt_ggc_mx_ipcp_transformation (void *);
#define gt_ggc_m_31vec_ipa_param_descriptor_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_param_descriptor_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_param_descriptor_va_gc_ (void *);
#define gt_ggc_m_27vec_ipa_argagg_value_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_argagg_value_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_argagg_value_va_gc_ (void *);
#define gt_ggc_m_17vec_ipa_vr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_vr_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_vr_va_gc_ (void *);
#define gt_ggc_m_33vec_ipa_uid_to_idx_map_elt_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_uid_to_idx_map_elt_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_uid_to_idx_map_elt_va_gc_ (void *);
#define gt_ggc_m_24vec_ipa_jump_func_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_jump_func_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_jump_func_va_gc_ (void *);
#define gt_ggc_m_39vec_ipa_polymorphic_call_context_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_polymorphic_call_context_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_polymorphic_call_context_va_gc_ (void *);
#define gt_ggc_m_17ipa_node_params_t(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_node_params_t (X);\
  } while (0)
extern void gt_ggc_mx_ipa_node_params_t (void *);
#define gt_ggc_m_19ipa_edge_args_sum_t(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_ipa_edge_args_sum_t (X);\
  } while (0)
extern void gt_ggc_mx_ipa_edge_args_sum_t (void *);
#define gt_ggc_m_38function_summary_ipcp_transformation__(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_function_summary_ipcp_transformation__ (X);\
  } while (0)
extern void gt_ggc_mx_function_summary_ipcp_transformation__ (void *);
#define gt_ggc_m_29hash_table_tm_wrapper_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tm_wrapper_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tm_wrapper_hasher_ (void *);
#define gt_ggc_m_29hash_table_decl_state_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_decl_state_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_decl_state_hasher_ (void *);
#define gt_ggc_m_23vec_expr_eval_op_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_expr_eval_op_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_expr_eval_op_va_gc_ (void *);
#define gt_ggc_m_20vec_condition_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_condition_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_condition_va_gc_ (void *);
#define gt_ggc_m_37vec_ipa_freqcounting_predicate_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ipa_freqcounting_predicate_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ipa_freqcounting_predicate_va_gc_ (void *);
#define gt_ggc_m_44fast_function_summary_ipa_fn_summary__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_fast_function_summary_ipa_fn_summary__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_fast_function_summary_ipa_fn_summary__va_gc_ (void *);
#define gt_ggc_m_13tree_type_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_type_map (X);\
  } while (0)
extern void gt_ggc_mx_tree_type_map (void *);
#define gt_ggc_m_38hash_table_tree_type_map_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_tree_type_map_cache_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_tree_type_map_cache_hasher_ (void *);
#define gt_ggc_m_19vec_odr_type_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_odr_type_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_odr_type_va_gc_ (void *);
#define gt_ggc_m_19registered_function(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_registered_function (X);\
  } while (0)
extern void gt_ggc_mx_registered_function (void *);
#define gt_ggc_m_31vec_registered_function__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_registered_function__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_registered_function__va_gc_ (void *);
#define gt_ggc_m_35hash_map_tree_registered_function__(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_registered_function__ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_registered_function__ (void *);
#define gt_ggc_m_35hash_table_value_annotation_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_value_annotation_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_value_annotation_hasher_ (void *);
#define gt_ggc_m_27vec_Entity_Id_va_gc_atomic_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_Entity_Id_va_gc_atomic_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_Entity_Id_va_gc_atomic_ (void *);
#define gt_ggc_m_19tree_entity_vec_map(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_entity_vec_map (X);\
  } while (0)
extern void gt_ggc_mx_tree_entity_vec_map (void *);
#define gt_ggc_m_29hash_table_dummy_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_dummy_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_dummy_type_hasher_ (void *);
#define gt_ggc_m_11parm_attr_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_parm_attr_d (X);\
  } while (0)
extern void gt_ggc_mx_parm_attr_d (void *);
#define gt_ggc_m_20vec_parm_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_parm_attr_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_parm_attr_va_gc_ (void *);
#define gt_ggc_m_10stmt_group(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_stmt_group (X);\
  } while (0)
extern void gt_ggc_mx_stmt_group (void *);
#define gt_ggc_m_9elab_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_elab_info (X);\
  } while (0)
extern void gt_ggc_mx_elab_info (void *);
#define gt_ggc_m_18range_check_info_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_range_check_info_d (X);\
  } while (0)
extern void gt_ggc_mx_range_check_info_d (void *);
#define gt_ggc_m_27vec_range_check_info_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_range_check_info_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_range_check_info_va_gc_ (void *);
#define gt_ggc_m_11loop_info_d(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_loop_info_d (X);\
  } while (0)
extern void gt_ggc_mx_loop_info_d (void *);
#define gt_ggc_m_20vec_loop_info_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_loop_info_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_loop_info_va_gc_ (void *);
#define gt_ggc_m_18gnat_binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_gnat_binding_level (X);\
  } while (0)
extern void gt_ggc_mx_gnat_binding_level (void *);
#define gt_ggc_m_18packable_type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_packable_type_hash (X);\
  } while (0)
extern void gt_ggc_mx_packable_type_hash (void *);
#define gt_ggc_m_32hash_table_packable_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_packable_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_packable_type_hasher_ (void *);
#define gt_ggc_m_13pad_type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_pad_type_hash (X);\
  } while (0)
extern void gt_ggc_mx_pad_type_hash (void *);
#define gt_ggc_m_27hash_table_pad_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_pad_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_pad_type_hasher_ (void *);
#define gt_ggc_m_15sized_type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_sized_type_hash (X);\
  } while (0)
extern void gt_ggc_mx_sized_type_hash (void *);
#define gt_ggc_m_29hash_table_sized_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_sized_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_sized_type_hasher_ (void *);
#define gt_ggc_m_12c_label_vars(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_c_label_vars (X);\
  } while (0)
extern void gt_ggc_mx_c_label_vars (void *);
#define gt_ggc_m_9c_binding(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_c_binding (X);\
  } while (0)
extern void gt_ggc_mx_c_binding (void *);
#define gt_ggc_m_18vec_c_token_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_c_token_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_c_token_va_gc_ (void *);
#define gt_ggc_m_7c_scope(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_c_scope (X);\
  } while (0)
extern void gt_ggc_mx_c_scope (void *);
#define gt_ggc_m_15c_goto_bindings(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_c_goto_bindings (X);\
  } while (0)
extern void gt_ggc_mx_c_goto_bindings (void *);
#define gt_ggc_m_28vec_c_goto_bindings_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_c_goto_bindings_p_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_c_goto_bindings_p_va_gc_ (void *);
#define gt_ggc_m_15c_inline_static(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_c_inline_static (X);\
  } while (0)
extern void gt_ggc_mx_c_inline_static (void *);
#define gt_ggc_m_27hash_table_c_struct_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_c_struct_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_c_struct_hasher_ (void *);
#define gt_ggc_m_18sorted_fields_type(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_sorted_fields_type (X);\
  } while (0)
extern void gt_ggc_mx_sorted_fields_type (void *);
#define gt_ggc_m_23vec_const_char_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_const_char_p_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_const_char_p_va_gc_ (void *);
#define gt_ggc_m_22vec_tree_gc_vec_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_tree_gc_vec_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_tree_gc_vec_va_gc_ (void *);
#define gt_ggc_m_11align_stack(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_align_stack (X);\
  } while (0)
extern void gt_ggc_mx_align_stack (void *);
#define gt_ggc_m_23vec_pending_weak_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_pending_weak_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_pending_weak_va_gc_ (void *);
#define gt_ggc_m_31vec_pending_redefinition_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_pending_redefinition_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_pending_redefinition_va_gc_ (void *);
#define gt_ggc_m_9opt_stack(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_opt_stack (X);\
  } while (0)
extern void gt_ggc_mx_opt_stack (void *);
#define gt_ggc_m_8c_parser(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_c_parser (X);\
  } while (0)
extern void gt_ggc_mx_c_parser (void *);
#define gt_ggc_m_26omp_attribute_pragma_state(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_omp_attribute_pragma_state (X);\
  } while (0)
extern void gt_ggc_mx_omp_attribute_pragma_state (void *);
#define gt_ggc_m_36vec_c_omp_declare_target_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_c_omp_declare_target_attr_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_c_omp_declare_target_attr_va_gc_ (void *);
#define gt_ggc_m_35vec_c_omp_begin_assumes_data_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_c_omp_begin_assumes_data_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_c_omp_begin_assumes_data_va_gc_ (void *);
#define gt_ggc_m_16cp_binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cp_binding_level (X);\
  } while (0)
extern void gt_ggc_mx_cp_binding_level (void *);
#define gt_ggc_m_11cxx_binding(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cxx_binding (X);\
  } while (0)
extern void gt_ggc_mx_cxx_binding (void *);
#define gt_ggc_m_27vec_cp_class_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cp_class_binding_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cp_class_binding_va_gc_ (void *);
#define gt_ggc_m_14cp_token_cache(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cp_token_cache (X);\
  } while (0)
extern void gt_ggc_mx_cp_token_cache (void *);
#define gt_ggc_m_32vec_deferred_access_check_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_deferred_access_check_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_deferred_access_check_va_gc_ (void *);
#define gt_ggc_m_28vec_cxx_saved_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cxx_saved_binding_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cxx_saved_binding_va_gc_ (void *);
#define gt_ggc_m_37vec_cp_omp_declare_target_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cp_omp_declare_target_attr_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cp_omp_declare_target_attr_va_gc_ (void *);
#define gt_ggc_m_36vec_cp_omp_begin_assumes_data_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cp_omp_begin_assumes_data_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cp_omp_begin_assumes_data_va_gc_ (void *);
#define gt_ggc_m_11saved_scope(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_saved_scope (X);\
  } while (0)
extern void gt_ggc_mx_saved_scope (void *);
#define gt_ggc_m_17named_label_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_named_label_entry (X);\
  } while (0)
extern void gt_ggc_mx_named_label_entry (void *);
#define gt_ggc_m_28hash_table_named_label_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_named_label_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_named_label_hash_ (void *);
#define gt_ggc_m_11tree_pair_s(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_pair_s (X);\
  } while (0)
extern void gt_ggc_mx_tree_pair_s (void *);
#define gt_ggc_m_22vec_tree_pair_s_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_tree_pair_s_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_tree_pair_s_va_gc_ (void *);
#define gt_ggc_m_27hash_table_named_decl_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_named_decl_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_named_decl_hash_ (void *);
#define gt_ggc_m_10spec_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_spec_entry (X);\
  } while (0)
extern void gt_ggc_mx_spec_entry (void *);
#define gt_ggc_m_11tinst_level(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tinst_level (X);\
  } while (0)
extern void gt_ggc_mx_tinst_level (void *);
#define gt_ggc_m_46hash_map_tree_location_t_decl_location_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_location_t_decl_location_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_location_t_decl_location_traits_ (void *);
#define gt_ggc_m_12module_state(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_module_state (X);\
  } while (0)
extern void gt_ggc_mx_module_state (void *);
#define gt_ggc_m_16constexpr_fundef(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_constexpr_fundef (X);\
  } while (0)
extern void gt_ggc_mx_constexpr_fundef (void *);
#define gt_ggc_m_10tree_check(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_tree_check (X);\
  } while (0)
extern void gt_ggc_mx_tree_check (void *);
#define gt_ggc_m_19vec_cp_token_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cp_token_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cp_token_va_gc_ (void *);
#define gt_ggc_m_8cp_lexer(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cp_lexer (X);\
  } while (0)
extern void gt_ggc_mx_cp_lexer (void *);
#define gt_ggc_m_31vec_cp_default_arg_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cp_default_arg_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cp_default_arg_entry_va_gc_ (void *);
#define gt_ggc_m_17cp_parser_context(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cp_parser_context (X);\
  } while (0)
extern void gt_ggc_mx_cp_parser_context (void *);
#define gt_ggc_m_38vec_cp_unparsed_functions_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_cp_unparsed_functions_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_cp_unparsed_functions_entry_va_gc_ (void *);
#define gt_ggc_m_9cp_parser(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_cp_parser (X);\
  } while (0)
extern void gt_ggc_mx_cp_parser (void *);
#define gt_ggc_m_18hash_map_tree_int_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_int_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_int_ (void *);
#define gt_ggc_m_35hash_table_constexpr_fundef_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_constexpr_fundef_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_constexpr_fundef_hasher_ (void *);
#define gt_ggc_m_14constexpr_call(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_constexpr_call (X);\
  } while (0)
extern void gt_ggc_mx_constexpr_call (void *);
#define gt_ggc_m_33hash_table_constexpr_call_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_constexpr_call_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_constexpr_call_hasher_ (void *);
#define gt_ggc_m_10norm_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_norm_entry (X);\
  } while (0)
extern void gt_ggc_mx_norm_entry (void *);
#define gt_ggc_m_23hash_table_norm_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_norm_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_norm_hasher_ (void *);
#define gt_ggc_m_23hash_table_atom_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_atom_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_atom_hasher_ (void *);
#define gt_ggc_m_9sat_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_sat_entry (X);\
  } while (0)
extern void gt_ggc_mx_sat_entry (void *);
#define gt_ggc_m_22hash_table_sat_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_sat_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_sat_hasher_ (void *);
#define gt_ggc_m_14coroutine_info(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_coroutine_info (X);\
  } while (0)
extern void gt_ggc_mx_coroutine_info (void *);
#define gt_ggc_m_33hash_table_coroutine_info_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_coroutine_info_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_coroutine_info_hasher_ (void *);
#define gt_ggc_m_27source_location_table_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_source_location_table_entry (X);\
  } while (0)
extern void gt_ggc_mx_source_location_table_entry (void *);
#define gt_ggc_m_44hash_table_source_location_table_entry_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_source_location_table_entry_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_source_location_table_entry_hash_ (void *);
#define gt_ggc_m_21named_label_use_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_named_label_use_entry (X);\
  } while (0)
extern void gt_ggc_mx_named_label_use_entry (void *);
#define gt_ggc_m_25vec_incomplete_var_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_incomplete_var_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_incomplete_var_va_gc_ (void *);
#define gt_ggc_m_27hash_table_typename_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_typename_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_typename_hasher_ (void *);
#define gt_ggc_m_29hash_table_mangled_decl_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_mangled_decl_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_mangled_decl_hash_ (void *);
#define gt_ggc_m_43hash_map_unsigned_tree_priority_map_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_unsigned_tree_priority_map_traits_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_unsigned_tree_priority_map_traits_ (void *);
#define gt_ggc_m_27vec_pending_noexcept_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_pending_noexcept_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_pending_noexcept_va_gc_ (void *);
#define gt_ggc_m_27vec_lambda_sig_count_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_lambda_sig_count_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_lambda_sig_count_va_gc_ (void *);
#define gt_ggc_m_31vec_lambda_discriminator_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_lambda_discriminator_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_lambda_discriminator_va_gc_ (void *);
#define gt_ggc_m_28hash_table_conv_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_conv_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_conv_type_hasher_ (void *);
#define gt_ggc_m_17subsumption_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_subsumption_entry (X);\
  } while (0)
extern void gt_ggc_mx_subsumption_entry (void *);
#define gt_ggc_m_30hash_table_subsumption_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_subsumption_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_subsumption_hasher_ (void *);
#define gt_ggc_m_8slurping(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_slurping (X);\
  } while (0)
extern void gt_ggc_mx_slurping (void *);
#define gt_ggc_m_24vec_module_state__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_module_state__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_module_state__va_gc_ (void *);
#define gt_ggc_m_29hash_table_module_state_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_module_state_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_module_state_hash_ (void *);
#define gt_ggc_m_33hash_table_note_def_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_note_def_cache_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_note_def_cache_hasher_ (void *);
#define gt_ggc_m_23vec_macro_export_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_macro_export_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_macro_export_va_gc_ (void *);
#define gt_ggc_m_16pending_template(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_pending_template (X);\
  } while (0)
extern void gt_ggc_mx_pending_template (void *);
#define gt_ggc_m_23hash_table_spec_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_spec_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_spec_hasher_ (void *);
#define gt_ggc_m_22hash_table_ctp_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_ctp_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_ctp_hasher_ (void *);
#define gt_ggc_m_25hash_map_const_tree_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_const_tree_tree_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_const_tree_tree_ (void *);
#define gt_ggc_m_26hash_map_tree_tree_pair_p_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_tree_pair_p_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_tree_pair_p_ (void *);
#define gt_ggc_m_18vec_tinfo_s_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_tinfo_s_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_tinfo_s_va_gc_ (void *);
#define gt_ggc_m_26vec_deferred_access_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_deferred_access_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_deferred_access_va_gc_ (void *);
#define gt_ggc_m_19hash_map_tree_bool_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_tree_bool_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_tree_bool_ (void *);
#define gt_ggc_m_30hash_table_cplus_array_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_cplus_array_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_cplus_array_hasher_ (void *);
#define gt_ggc_m_23hash_table_list_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_list_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_list_hasher_ (void *);
#define gt_ggc_m_9Statement(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_Statement (X);\
  } while (0)
extern void gt_ggc_mx_Statement (void *);
#define gt_ggc_m_13binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_binding_level (X);\
  } while (0)
extern void gt_ggc_mx_binding_level (void *);
#define gt_ggc_m_17d_label_use_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_d_label_use_entry (X);\
  } while (0)
extern void gt_ggc_mx_d_label_use_entry (void *);
#define gt_ggc_m_34hash_map_Statement__d_label_entry_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_map_Statement__d_label_entry_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_map_Statement__d_label_entry_ (void *);
#define gt_ggc_m_25hash_table_module_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_module_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_module_hasher_ (void *);
#define gt_ggc_m_17module_htab_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_module_htab_entry (X);\
  } while (0)
extern void gt_ggc_mx_module_htab_entry (void *);
#define gt_ggc_m_30hash_table_module_decl_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_module_decl_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_module_decl_hasher_ (void *);
#define gt_ggc_m_7rtenode(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rtenode (X);\
  } while (0)
extern void gt_ggc_mx_rtenode (void *);
#define gt_ggc_m_19vec_rtenode__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_rtenode__va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_rtenode__va_gc_ (void *);
#define gt_ggc_m_35vec_builtin_macro_definition_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_builtin_macro_definition_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_builtin_macro_definition_va_gc_ (void *);
#define gt_ggc_m_18struct_constructor(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_struct_constructor (X);\
  } while (0)
extern void gt_ggc_mx_struct_constructor (void *);
#define gt_ggc_m_10array_desc(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_array_desc (X);\
  } while (0)
extern void gt_ggc_mx_array_desc (void *);
#define gt_ggc_m_16objc_map_private(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_objc_map_private (X);\
  } while (0)
extern void gt_ggc_mx_objc_map_private (void *);
#define gt_ggc_m_12hashed_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hashed_entry (X);\
  } while (0)
extern void gt_ggc_mx_hashed_entry (void *);
#define gt_ggc_m_16hashed_attribute(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hashed_attribute (X);\
  } while (0)
extern void gt_ggc_mx_hashed_attribute (void *);
#define gt_ggc_m_9imp_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_imp_entry (X);\
  } while (0)
extern void gt_ggc_mx_imp_entry (void *);
#define gt_ggc_m_17string_descriptor(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_string_descriptor (X);\
  } while (0)
extern void gt_ggc_mx_string_descriptor (void *);
#define gt_ggc_m_30hash_table_objc_string_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_objc_string_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_objc_string_hasher_ (void *);
#define gt_ggc_m_27vec_ident_data_tuple_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ident_data_tuple_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ident_data_tuple_va_gc_ (void *);
#define gt_ggc_m_23vec_msgref_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_msgref_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_msgref_entry_va_gc_ (void *);
#define gt_ggc_m_26vec_prot_list_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_prot_list_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_prot_list_entry_va_gc_ (void *);
#define gt_ggc_m_24vec_ivarref_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_ivarref_entry_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_ivarref_entry_va_gc_ (void *);
#define gt_ggc_m_21rust_constexpr_fundef(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rust_constexpr_fundef (X);\
  } while (0)
extern void gt_ggc_mx_rust_constexpr_fundef (void *);
#define gt_ggc_m_19rust_constexpr_call(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rust_constexpr_call (X);\
  } while (0)
extern void gt_ggc_mx_rust_constexpr_call (void *);
#define gt_ggc_m_40hash_table_rust_constexpr_fundef_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_constexpr_fundef_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_constexpr_fundef_hasher_ (void *);
#define gt_ggc_m_38hash_table_rust_constexpr_call_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_constexpr_call_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_constexpr_call_hasher_ (void *);
#define gt_ggc_m_33vec_rust_cxx_saved_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_rust_cxx_saved_binding_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_rust_cxx_saved_binding_va_gc_ (void *);
#define gt_ggc_m_34vec_omp_declare_target_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_omp_declare_target_attr_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_omp_declare_target_attr_va_gc_ (void *);
#define gt_ggc_m_32vec_rust_cp_class_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_rust_cp_class_binding_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_rust_cp_class_binding_va_gc_ (void *);
#define gt_ggc_m_21rust_cp_binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rust_cp_binding_level (X);\
  } while (0)
extern void gt_ggc_mx_rust_cp_binding_level (void *);
#define gt_ggc_m_22rust_named_label_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_rust_named_label_entry (X);\
  } while (0)
extern void gt_ggc_mx_rust_named_label_entry (void *);
#define gt_ggc_m_33hash_table_rust_named_label_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_named_label_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_named_label_hash_ (void *);
#define gt_ggc_m_32hash_table_rust_named_decl_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_named_decl_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_named_decl_hash_ (void *);
#define gt_ggc_m_27vec_rust_tree_pair_s_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_vec_rust_tree_pair_s_va_gc_ (X);\
  } while (0)
extern void gt_ggc_mx_vec_rust_tree_pair_s_va_gc_ (void *);
#define gt_ggc_m_33hash_table_rust_conv_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_conv_type_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_conv_type_hasher_ (void *);
#define gt_ggc_m_35hash_table_rust_cplus_array_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_cplus_array_hasher_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_cplus_array_hasher_ (void *);
#define gt_ggc_m_49hash_table_rust_source_location_table_entry_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_ggc_mx_hash_table_rust_source_location_table_entry_hash_ (X);\
  } while (0)
extern void gt_ggc_mx_hash_table_rust_source_location_table_entry_hash_ (void *);

/* functions code */

/* PCH type-walking procedures.  */
/* Macros and declarations.  */
#define gt_pch_n_9tree_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_node (X);\
  } while (0)
#define gt_pch_nx_tree_node gt_pch_nx_lang_tree_node
#define gt_pch_n_9line_maps(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_line_maps (X);\
  } while (0)
extern void gt_pch_nx_line_maps (void *);
#define gt_pch_n_9cpp_token(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cpp_token (X);\
  } while (0)
extern void gt_pch_nx_cpp_token (void *);
#define gt_pch_n_9cpp_macro(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cpp_macro (X);\
  } while (0)
extern void gt_pch_nx_cpp_macro (void *);
#define gt_pch_n_18cpp_hashnode_extra(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cpp_hashnode_extra (X);\
  } while (0)
extern void gt_pch_nx_cpp_hashnode_extra (void *);
#define gt_pch_n_13string_concat(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_string_concat (X);\
  } while (0)
extern void gt_pch_nx_string_concat (void *);
#define gt_pch_n_16string_concat_db(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_string_concat_db (X);\
  } while (0)
extern void gt_pch_nx_string_concat_db (void *);
#define gt_pch_n_38hash_map_location_hash_string_concat__(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_location_hash_string_concat__ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_location_hash_string_concat__ (void *);
#define gt_pch_n_11bitmap_head(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_bitmap_head (X);\
  } while (0)
extern void gt_pch_nx_bitmap_head (void *);
#define gt_pch_n_7rtx_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rtx_def (X);\
  } while (0)
extern void gt_pch_nx_rtx_def (void *);
#define gt_pch_n_9rtvec_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rtvec_def (X);\
  } while (0)
extern void gt_pch_nx_rtvec_def (void *);
#define gt_pch_n_6gimple(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_gimple (X);\
  } while (0)
extern void gt_pch_nx_gimple (void *);
#define gt_pch_n_11dw_cfi_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_cfi_node (X);\
  } while (0)
extern void gt_pch_nx_dw_cfi_node (void *);
#define gt_pch_n_11symtab_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_symtab_node (X);\
  } while (0)
extern void gt_pch_nx_symtab_node (void *);
#define gt_pch_n_11cgraph_edge(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cgraph_edge (X);\
  } while (0)
extern void gt_pch_nx_cgraph_edge (void *);
#define gt_pch_n_7section(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_section (X);\
  } while (0)
extern void gt_pch_nx_section (void *);
#define gt_pch_n_16cl_target_option(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cl_target_option (X);\
  } while (0)
extern void gt_pch_nx_cl_target_option (void *);
#define gt_pch_n_15cl_optimization(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cl_optimization (X);\
  } while (0)
extern void gt_pch_nx_cl_optimization (void *);
#define gt_pch_n_8edge_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_edge_def (X);\
  } while (0)
extern void gt_pch_nx_edge_def (void *);
#define gt_pch_n_15basic_block_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_basic_block_def (X);\
  } while (0)
extern void gt_pch_nx_basic_block_def (void *);
#define gt_pch_n_26vec_unsigned_va_gc_atomic_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_unsigned_va_gc_atomic_ (X);\
  } while (0)
extern void gt_pch_nx_vec_unsigned_va_gc_atomic_ (void *);
#define gt_pch_n_14hash_set_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_set_tree_ (X);\
  } while (0)
extern void gt_pch_nx_hash_set_tree_ (void *);
#define gt_pch_n_16machine_function(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_machine_function (X);\
  } while (0)
extern void gt_pch_nx_machine_function (void *);
#define gt_pch_n_14bitmap_element(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_bitmap_element (X);\
  } while (0)
extern void gt_pch_nx_bitmap_element (void *);
#define gt_pch_n_13coverage_data(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_coverage_data (X);\
  } while (0)
extern void gt_pch_nx_coverage_data (void *);
#define gt_pch_n_9mem_attrs(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_mem_attrs (X);\
  } while (0)
extern void gt_pch_nx_mem_attrs (void *);
#define gt_pch_n_9reg_attrs(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_reg_attrs (X);\
  } while (0)
extern void gt_pch_nx_reg_attrs (void *);
#define gt_pch_n_12object_block(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_object_block (X);\
  } while (0)
extern void gt_pch_nx_object_block (void *);
#define gt_pch_n_14vec_rtx_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_rtx_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_rtx_va_gc_ (void *);
#define gt_pch_n_11fixed_value(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_fixed_value (X);\
  } while (0)
extern void gt_pch_nx_fixed_value (void *);
#define gt_pch_n_23constant_descriptor_rtx(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_constant_descriptor_rtx (X);\
  } while (0)
extern void gt_pch_nx_constant_descriptor_rtx (void *);
#define gt_pch_n_8function(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_function (X);\
  } while (0)
extern void gt_pch_nx_function (void *);
#define gt_pch_n_10target_rtl(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_target_rtl (X);\
  } while (0)
extern void gt_pch_nx_target_rtl (void *);
#define gt_pch_n_15cgraph_rtl_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cgraph_rtl_info (X);\
  } while (0)
extern void gt_pch_nx_cgraph_rtl_info (void *);
#define gt_pch_n_42hash_map_tree_tree_decl_tree_cache_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_tree_decl_tree_cache_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_tree_decl_tree_cache_traits_ (void *);
#define gt_pch_n_42hash_map_tree_tree_type_tree_cache_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_tree_type_tree_cache_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_tree_type_tree_cache_traits_ (void *);
#define gt_pch_n_36hash_map_tree_tree_decl_tree_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_tree_decl_tree_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_tree_decl_tree_traits_ (void *);
#define gt_pch_n_12ptr_info_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ptr_info_def (X);\
  } while (0)
extern void gt_pch_nx_ptr_info_def (void *);
#define gt_pch_n_10die_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_die_struct (X);\
  } while (0)
extern void gt_pch_nx_die_struct (void *);
#define gt_pch_n_26vec_constructor_elt_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_constructor_elt_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_constructor_elt_va_gc_ (void *);
#define gt_pch_n_14vrange_storage(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vrange_storage (X);\
  } while (0)
extern void gt_pch_nx_vrange_storage (void *);
#define gt_pch_n_15vec_tree_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_tree_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_tree_va_gc_ (void *);
#define gt_pch_n_9lang_type(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_lang_type (X);\
  } while (0)
extern void gt_pch_nx_lang_type (void *);
#define gt_pch_n_9lang_decl(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_lang_decl (X);\
  } while (0)
extern void gt_pch_nx_lang_decl (void *);
#define gt_pch_n_24tree_statement_list_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_statement_list_node (X);\
  } while (0)
extern void gt_pch_nx_tree_statement_list_node (void *);
#define gt_pch_n_14target_globals(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_target_globals (X);\
  } while (0)
extern void gt_pch_nx_target_globals (void *);
#define gt_pch_n_14lang_tree_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_lang_tree_node (X);\
  } while (0)
extern void gt_pch_nx_lang_tree_node (void *);
#define gt_pch_n_8tree_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_map (X);\
  } while (0)
extern void gt_pch_nx_tree_map (void *);
#define gt_pch_n_13tree_decl_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_decl_map (X);\
  } while (0)
extern void gt_pch_nx_tree_decl_map (void *);
#define gt_pch_n_12tree_int_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_int_map (X);\
  } while (0)
extern void gt_pch_nx_tree_int_map (void *);
#define gt_pch_n_12tree_vec_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_vec_map (X);\
  } while (0)
extern void gt_pch_nx_tree_vec_map (void *);
#define gt_pch_n_21vec_alias_pair_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_alias_pair_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_alias_pair_va_gc_ (void *);
#define gt_pch_n_13libfunc_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_libfunc_entry (X);\
  } while (0)
extern void gt_pch_nx_libfunc_entry (void *);
#define gt_pch_n_26hash_table_libfunc_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_libfunc_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_libfunc_hasher_ (void *);
#define gt_pch_n_15target_libfuncs(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_target_libfuncs (X);\
  } while (0)
extern void gt_pch_nx_target_libfuncs (void *);
#define gt_pch_n_14sequence_stack(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_sequence_stack (X);\
  } while (0)
extern void gt_pch_nx_sequence_stack (void *);
#define gt_pch_n_20vec_rtx_insn__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_rtx_insn__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_rtx_insn__va_gc_ (void *);
#define gt_pch_n_18call_site_record_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_call_site_record_d (X);\
  } while (0)
extern void gt_pch_nx_call_site_record_d (void *);
#define gt_pch_n_16vec_uchar_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_uchar_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_uchar_va_gc_ (void *);
#define gt_pch_n_27vec_call_site_record_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_call_site_record_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_call_site_record_va_gc_ (void *);
#define gt_pch_n_9gimple_df(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_gimple_df (X);\
  } while (0)
extern void gt_pch_nx_gimple_df (void *);
#define gt_pch_n_11dw_fde_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_fde_node (X);\
  } while (0)
extern void gt_pch_nx_dw_fde_node (void *);
#define gt_pch_n_17rtx_constant_pool(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rtx_constant_pool (X);\
  } while (0)
extern void gt_pch_nx_rtx_constant_pool (void *);
#define gt_pch_n_11frame_space(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_frame_space (X);\
  } while (0)
extern void gt_pch_nx_frame_space (void *);
#define gt_pch_n_26vec_callinfo_callee_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_callinfo_callee_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_callinfo_callee_va_gc_ (void *);
#define gt_pch_n_26vec_callinfo_dalloc_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_callinfo_dalloc_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_callinfo_dalloc_va_gc_ (void *);
#define gt_pch_n_11stack_usage(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_stack_usage (X);\
  } while (0)
extern void gt_pch_nx_stack_usage (void *);
#define gt_pch_n_9eh_status(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_eh_status (X);\
  } while (0)
extern void gt_pch_nx_eh_status (void *);
#define gt_pch_n_18control_flow_graph(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_control_flow_graph (X);\
  } while (0)
extern void gt_pch_nx_control_flow_graph (void *);
#define gt_pch_n_5loops(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_loops (X);\
  } while (0)
extern void gt_pch_nx_loops (void *);
#define gt_pch_n_17language_function(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_language_function (X);\
  } while (0)
extern void gt_pch_nx_language_function (void *);
#define gt_pch_n_24types_used_by_vars_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_types_used_by_vars_entry (X);\
  } while (0)
extern void gt_pch_nx_types_used_by_vars_entry (void *);
#define gt_pch_n_28hash_table_used_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_used_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_used_type_hasher_ (void *);
#define gt_pch_n_13nb_iter_bound(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_nb_iter_bound (X);\
  } while (0)
extern void gt_pch_nx_nb_iter_bound (void *);
#define gt_pch_n_9loop_exit(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_loop_exit (X);\
  } while (0)
extern void gt_pch_nx_loop_exit (void *);
#define gt_pch_n_4loop(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_loop (X);\
  } while (0)
extern void gt_pch_nx_loop (void *);
#define gt_pch_n_10control_iv(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_control_iv (X);\
  } while (0)
extern void gt_pch_nx_control_iv (void *);
#define gt_pch_n_17vec_loop_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_loop_p_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_loop_p_va_gc_ (void *);
#define gt_pch_n_10niter_desc(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_niter_desc (X);\
  } while (0)
extern void gt_pch_nx_niter_desc (void *);
#define gt_pch_n_28hash_table_loop_exit_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_loop_exit_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_loop_exit_hasher_ (void *);
#define gt_pch_n_22vec_basic_block_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_basic_block_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_basic_block_va_gc_ (void *);
#define gt_pch_n_11rtl_bb_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rtl_bb_info (X);\
  } while (0)
extern void gt_pch_nx_rtl_bb_info (void *);
#define gt_pch_n_15vec_edge_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_edge_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_edge_va_gc_ (void *);
#define gt_pch_n_18section_hash_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_section_hash_entry (X);\
  } while (0)
extern void gt_pch_nx_section_hash_entry (void *);
#define gt_pch_n_18lto_file_decl_data(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_lto_file_decl_data (X);\
  } while (0)
extern void gt_pch_nx_lto_file_decl_data (void *);
#define gt_pch_n_15ipa_replace_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_replace_map (X);\
  } while (0)
extern void gt_pch_nx_ipa_replace_map (void *);
#define gt_pch_n_17cgraph_simd_clone(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cgraph_simd_clone (X);\
  } while (0)
extern void gt_pch_nx_cgraph_simd_clone (void *);
#define gt_pch_n_28cgraph_function_version_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cgraph_function_version_info (X);\
  } while (0)
extern void gt_pch_nx_cgraph_function_version_info (void *);
#define gt_pch_n_30hash_table_cgraph_edge_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_cgraph_edge_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_cgraph_edge_hasher_ (void *);
#define gt_pch_n_25cgraph_indirect_call_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cgraph_indirect_call_info (X);\
  } while (0)
extern void gt_pch_nx_cgraph_indirect_call_info (void *);
#define gt_pch_n_8asm_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_asm_node (X);\
  } while (0)
extern void gt_pch_nx_asm_node (void *);
#define gt_pch_n_10thunk_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_thunk_info (X);\
  } while (0)
extern void gt_pch_nx_thunk_info (void *);
#define gt_pch_n_29function_summary_thunk_info__(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_function_summary_thunk_info__ (X);\
  } while (0)
extern void gt_pch_nx_function_summary_thunk_info__ (void *);
#define gt_pch_n_10clone_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_clone_info (X);\
  } while (0)
extern void gt_pch_nx_clone_info (void *);
#define gt_pch_n_29function_summary_clone_info__(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_function_summary_clone_info__ (X);\
  } while (0)
extern void gt_pch_nx_function_summary_clone_info__ (void *);
#define gt_pch_n_12symbol_table(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_symbol_table (X);\
  } while (0)
extern void gt_pch_nx_symbol_table (void *);
#define gt_pch_n_31hash_table_section_name_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_section_name_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_section_name_hasher_ (void *);
#define gt_pch_n_26hash_table_asmname_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_asmname_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_asmname_hasher_ (void *);
#define gt_pch_n_42hash_map_symtab_node__symbol_priority_map_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_symtab_node__symbol_priority_map_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_symtab_node__symbol_priority_map_ (void *);
#define gt_pch_n_24constant_descriptor_tree(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_constant_descriptor_tree (X);\
  } while (0)
extern void gt_pch_nx_constant_descriptor_tree (void *);
#define gt_pch_n_28vec_unprocessed_thunk_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_unprocessed_thunk_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_unprocessed_thunk_va_gc_ (void *);
#define gt_pch_n_27vec_ipa_replace_map__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_replace_map__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_replace_map__va_gc_ (void *);
#define gt_pch_n_21ipa_param_adjustments(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_param_adjustments (X);\
  } while (0)
extern void gt_pch_nx_ipa_param_adjustments (void *);
#define gt_pch_n_28hash_map_alias_set_hash_int_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_alias_set_hash_int_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_alias_set_hash_int_ (void *);
#define gt_pch_n_15alias_set_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_alias_set_entry (X);\
  } while (0)
extern void gt_pch_nx_alias_set_entry (void *);
#define gt_pch_n_27vec_alias_set_entry__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_alias_set_entry__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_alias_set_entry__va_gc_ (void *);
#define gt_pch_n_35hash_table_function_version_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_function_version_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_function_version_hasher_ (void *);
#define gt_pch_n_17lto_in_decl_state(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_lto_in_decl_state (X);\
  } while (0)
extern void gt_pch_nx_lto_in_decl_state (void *);
#define gt_pch_n_34hash_table_ipa_vr_ggc_hash_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_ipa_vr_ggc_hash_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_ipa_vr_ggc_hash_traits_ (void *);
#define gt_pch_n_6ipa_vr(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_vr (X);\
  } while (0)
extern void gt_pch_nx_ipa_vr (void *);
#define gt_pch_n_24ipa_return_value_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_return_value_summary (X);\
  } while (0)
extern void gt_pch_nx_ipa_return_value_summary (void *);
#define gt_pch_n_43function_summary_ipa_return_value_summary__(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_function_summary_ipa_return_value_summary__ (X);\
  } while (0)
extern void gt_pch_nx_function_summary_ipa_return_value_summary__ (void *);
#define gt_pch_n_15ipa_node_params(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_node_params (X);\
  } while (0)
extern void gt_pch_nx_ipa_node_params (void *);
#define gt_pch_n_13ipa_edge_args(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_edge_args (X);\
  } while (0)
extern void gt_pch_nx_ipa_edge_args (void *);
#define gt_pch_n_14ipa_fn_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_fn_summary (X);\
  } while (0)
extern void gt_pch_nx_ipa_fn_summary (void *);
#define gt_pch_n_10odr_type_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_odr_type_d (X);\
  } while (0)
extern void gt_pch_nx_odr_type_d (void *);
#define gt_pch_n_29vec_ipa_adjusted_param_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_adjusted_param_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_adjusted_param_va_gc_ (void *);
#define gt_pch_n_12param_access(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_param_access (X);\
  } while (0)
extern void gt_pch_nx_param_access (void *);
#define gt_pch_n_24vec_param_access__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_param_access__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_param_access__va_gc_ (void *);
#define gt_pch_n_17isra_func_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_isra_func_summary (X);\
  } while (0)
extern void gt_pch_nx_isra_func_summary (void *);
#define gt_pch_n_26vec_isra_param_desc_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_isra_param_desc_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_isra_param_desc_va_gc_ (void *);
#define gt_pch_n_26ipa_sra_function_summaries(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_sra_function_summaries (X);\
  } while (0)
extern void gt_pch_nx_ipa_sra_function_summaries (void *);
#define gt_pch_n_27modref_tree_alias_set_type_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_modref_tree_alias_set_type_ (X);\
  } while (0)
extern void gt_pch_nx_modref_tree_alias_set_type_ (void *);
#define gt_pch_n_14modref_summary(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_modref_summary (X);\
  } while (0)
extern void gt_pch_nx_modref_summary (void *);
#define gt_pch_n_18modref_summary_lto(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_modref_summary_lto (X);\
  } while (0)
extern void gt_pch_nx_modref_summary_lto (void *);
#define gt_pch_n_44fast_function_summary_modref_summary__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_fast_function_summary_modref_summary__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_fast_function_summary_modref_summary__va_gc_ (void *);
#define gt_pch_n_48fast_function_summary_modref_summary_lto__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_fast_function_summary_modref_summary_lto__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_fast_function_summary_modref_summary_lto__va_gc_ (void *);
#define gt_pch_n_17modref_tree_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_modref_tree_tree_ (X);\
  } while (0)
extern void gt_pch_nx_modref_tree_tree_ (void *);
#define gt_pch_n_37hash_map_location_hash_nowarn_spec_t_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_location_hash_nowarn_spec_t_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_location_hash_nowarn_spec_t_ (void *);
#define gt_pch_n_17dw_loc_descr_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_loc_descr_node (X);\
  } while (0)
extern void gt_pch_nx_dw_loc_descr_node (void *);
#define gt_pch_n_18dw_loc_list_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_loc_list_struct (X);\
  } while (0)
extern void gt_pch_nx_dw_loc_list_struct (void *);
#define gt_pch_n_18dw_discr_list_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_discr_list_node (X);\
  } while (0)
extern void gt_pch_nx_dw_discr_list_node (void *);
#define gt_pch_n_11dw_wide_int(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_wide_int (X);\
  } while (0)
extern void gt_pch_nx_dw_wide_int (void *);
#define gt_pch_n_15dw_cfa_location(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_cfa_location (X);\
  } while (0)
extern void gt_pch_nx_dw_cfa_location (void *);
#define gt_pch_n_21vec_dw_cfi_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_cfi_ref_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_cfi_ref_va_gc_ (void *);
#define gt_pch_n_16addr_table_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_addr_table_entry (X);\
  } while (0)
extern void gt_pch_nx_addr_table_entry (void *);
#define gt_pch_n_20indirect_string_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_indirect_string_node (X);\
  } while (0)
extern void gt_pch_nx_indirect_string_node (void *);
#define gt_pch_n_15dwarf_file_data(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dwarf_file_data (X);\
  } while (0)
extern void gt_pch_nx_dwarf_file_data (void *);
#define gt_pch_n_20hash_map_char__tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_char__tree_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_char__tree_ (void *);
#define gt_pch_n_10dw_cfi_row(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_cfi_row (X);\
  } while (0)
extern void gt_pch_nx_dw_cfi_row (void *);
#define gt_pch_n_17reg_saved_in_data(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_reg_saved_in_data (X);\
  } while (0)
extern void gt_pch_nx_reg_saved_in_data (void *);
#define gt_pch_n_21vec_dw_fde_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_fde_ref_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_fde_ref_va_gc_ (void *);
#define gt_pch_n_34hash_table_indirect_string_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_indirect_string_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_indirect_string_hasher_ (void *);
#define gt_pch_n_16vec_char__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_char__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_char__va_gc_ (void *);
#define gt_pch_n_16comdat_type_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_comdat_type_node (X);\
  } while (0)
extern void gt_pch_nx_comdat_type_node (void *);
#define gt_pch_n_29vec_dw_line_info_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_line_info_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_line_info_entry_va_gc_ (void *);
#define gt_pch_n_18dw_line_info_table(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_dw_line_info_table (X);\
  } while (0)
extern void gt_pch_nx_dw_line_info_table (void *);
#define gt_pch_n_23vec_dw_attr_node_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_attr_node_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_attr_node_va_gc_ (void *);
#define gt_pch_n_16limbo_die_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_limbo_die_struct (X);\
  } while (0)
extern void gt_pch_nx_limbo_die_struct (void *);
#define gt_pch_n_29hash_table_dwarf_file_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_dwarf_file_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_dwarf_file_hasher_ (void *);
#define gt_pch_n_27hash_table_decl_die_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_decl_die_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_decl_die_hasher_ (void *);
#define gt_pch_n_21vec_dw_die_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_die_ref_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_die_ref_va_gc_ (void *);
#define gt_pch_n_21variable_value_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_variable_value_struct (X);\
  } while (0)
extern void gt_pch_nx_variable_value_struct (void *);
#define gt_pch_n_33hash_table_variable_value_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_variable_value_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_variable_value_hasher_ (void *);
#define gt_pch_n_28hash_table_block_die_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_block_die_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_block_die_hasher_ (void *);
#define gt_pch_n_12var_loc_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_var_loc_node (X);\
  } while (0)
extern void gt_pch_nx_var_loc_node (void *);
#define gt_pch_n_16var_loc_list_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_var_loc_list_def (X);\
  } while (0)
extern void gt_pch_nx_var_loc_list_def (void *);
#define gt_pch_n_17call_arg_loc_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_call_arg_loc_node (X);\
  } while (0)
extern void gt_pch_nx_call_arg_loc_node (void *);
#define gt_pch_n_27hash_table_decl_loc_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_decl_loc_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_decl_loc_hasher_ (void *);
#define gt_pch_n_22cached_dw_loc_list_def(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cached_dw_loc_list_def (X);\
  } while (0)
extern void gt_pch_nx_cached_dw_loc_list_def (void *);
#define gt_pch_n_30hash_table_dw_loc_list_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_dw_loc_list_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_dw_loc_list_hasher_ (void *);
#define gt_pch_n_30vec_dw_line_info_table__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_line_info_table__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_line_info_table__va_gc_ (void *);
#define gt_pch_n_24vec_pubname_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_pubname_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_pubname_entry_va_gc_ (void *);
#define gt_pch_n_24vec_macinfo_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_macinfo_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_macinfo_entry_va_gc_ (void *);
#define gt_pch_n_20vec_dw_ranges_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_ranges_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_ranges_va_gc_ (void *);
#define gt_pch_n_29vec_dw_ranges_by_label_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_dw_ranges_by_label_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_dw_ranges_by_label_va_gc_ (void *);
#define gt_pch_n_24vec_die_arg_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_die_arg_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_die_arg_entry_va_gc_ (void *);
#define gt_pch_n_23hash_table_addr_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_addr_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_addr_hasher_ (void *);
#define gt_pch_n_27hash_map_tree_sym_off_pair_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_sym_off_pair_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_sym_off_pair_ (void *);
#define gt_pch_n_17inline_entry_data(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_inline_entry_data (X);\
  } while (0)
extern void gt_pch_nx_inline_entry_data (void *);
#define gt_pch_n_36hash_table_inline_entry_data_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_inline_entry_data_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_inline_entry_data_hasher_ (void *);
#define gt_pch_n_9ctf_dtdef(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ctf_dtdef (X);\
  } while (0)
extern void gt_pch_nx_ctf_dtdef (void *);
#define gt_pch_n_10ctf_string(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ctf_string (X);\
  } while (0)
extern void gt_pch_nx_ctf_string (void *);
#define gt_pch_n_9ctf_dmdef(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ctf_dmdef (X);\
  } while (0)
extern void gt_pch_nx_ctf_dmdef (void *);
#define gt_pch_n_12ctf_func_arg(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ctf_func_arg (X);\
  } while (0)
extern void gt_pch_nx_ctf_func_arg (void *);
#define gt_pch_n_9ctf_dvdef(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ctf_dvdef (X);\
  } while (0)
extern void gt_pch_nx_ctf_dvdef (void *);
#define gt_pch_n_27hash_table_ctfc_dtd_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_ctfc_dtd_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_ctfc_dtd_hasher_ (void *);
#define gt_pch_n_27hash_table_ctfc_dvd_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_ctfc_dvd_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_ctfc_dvd_hasher_ (void *);
#define gt_pch_n_13ctf_container(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ctf_container (X);\
  } while (0)
extern void gt_pch_nx_ctf_container (void *);
#define gt_pch_n_24vec_ctf_dtdef_ref_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ctf_dtdef_ref_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ctf_dtdef_ref_va_gc_ (void *);
#define gt_pch_n_37hash_map_ctf_dtdef_ref_ctf_dtdef_ref_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_ctf_dtdef_ref_ctf_dtdef_ref_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_ctf_dtdef_ref_ctf_dtdef_ref_ (void *);
#define gt_pch_n_23hash_set_ctf_dtdef_ref_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_set_ctf_dtdef_ref_ (X);\
  } while (0)
extern void gt_pch_nx_hash_set_ctf_dtdef_ref_ (void *);
#define gt_pch_n_9temp_slot(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_temp_slot (X);\
  } while (0)
extern void gt_pch_nx_temp_slot (void *);
#define gt_pch_n_20initial_value_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_initial_value_struct (X);\
  } while (0)
extern void gt_pch_nx_initial_value_struct (void *);
#define gt_pch_n_22vec_temp_slot_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_temp_slot_p_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_temp_slot_p_va_gc_ (void *);
#define gt_pch_n_28hash_table_const_int_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_const_int_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_const_int_hasher_ (void *);
#define gt_pch_n_33hash_table_const_wide_int_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_const_wide_int_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_const_wide_int_hasher_ (void *);
#define gt_pch_n_33hash_table_const_poly_int_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_const_poly_int_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_const_poly_int_hasher_ (void *);
#define gt_pch_n_27hash_table_reg_attr_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_reg_attr_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_reg_attr_hasher_ (void *);
#define gt_pch_n_31hash_table_const_double_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_const_double_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_const_double_hasher_ (void *);
#define gt_pch_n_30hash_table_const_fixed_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_const_fixed_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_const_fixed_hasher_ (void *);
#define gt_pch_n_11eh_region_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_eh_region_d (X);\
  } while (0)
extern void gt_pch_nx_eh_region_d (void *);
#define gt_pch_n_16eh_landing_pad_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_eh_landing_pad_d (X);\
  } while (0)
extern void gt_pch_nx_eh_landing_pad_d (void *);
#define gt_pch_n_10eh_catch_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_eh_catch_d (X);\
  } while (0)
extern void gt_pch_nx_eh_catch_d (void *);
#define gt_pch_n_20vec_eh_region_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_eh_region_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_eh_region_va_gc_ (void *);
#define gt_pch_n_25vec_eh_landing_pad_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_eh_landing_pad_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_eh_landing_pad_va_gc_ (void *);
#define gt_pch_n_21hash_map_gimple__int_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_gimple__int_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_gimple__int_ (void *);
#define gt_pch_n_29hash_table_insn_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_insn_cache_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_insn_cache_hasher_ (void *);
#define gt_pch_n_23temp_slot_address_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_temp_slot_address_entry (X);\
  } while (0)
extern void gt_pch_nx_temp_slot_address_entry (void *);
#define gt_pch_n_31hash_table_temp_address_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_temp_address_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_temp_address_hasher_ (void *);
#define gt_pch_n_24hash_map_tree_hash_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_hash_tree_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_hash_tree_ (void *);
#define gt_pch_n_11test_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_test_struct (X);\
  } while (0)
extern void gt_pch_nx_test_struct (void *);
#define gt_pch_n_14test_of_length(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_test_of_length (X);\
  } while (0)
extern void gt_pch_nx_test_of_length (void *);
#define gt_pch_n_10test_other(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_test_other (X);\
  } while (0)
extern void gt_pch_nx_test_other (void *);
#define gt_pch_n_13test_of_union(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_test_of_union (X);\
  } while (0)
extern void gt_pch_nx_test_of_union (void *);
#define gt_pch_n_12example_base(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_example_base (X);\
  } while (0)
extern void gt_pch_nx_example_base (void *);
#define gt_pch_n_9test_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_test_node (X);\
  } while (0)
extern void gt_pch_nx_test_node (void *);
#define gt_pch_n_11user_struct(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_user_struct (X);\
  } while (0)
extern void gt_pch_nx_user_struct (void *);
#define gt_pch_n_31hash_table_libfunc_decl_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_libfunc_decl_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_libfunc_decl_hasher_ (void *);
#define gt_pch_n_16string_pool_data(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_string_pool_data (X);\
  } while (0)
extern void gt_pch_nx_string_pool_data (void *);
#define gt_pch_n_22string_pool_data_extra(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_string_pool_data_extra (X);\
  } while (0)
extern void gt_pch_nx_string_pool_data_extra (void *);
#define gt_pch_n_9type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_type_hash (X);\
  } while (0)
extern void gt_pch_nx_type_hash (void *);
#define gt_pch_n_29hash_table_type_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_type_cache_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_type_cache_hasher_ (void *);
#define gt_pch_n_26hash_table_int_cst_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_int_cst_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_int_cst_hasher_ (void *);
#define gt_pch_n_31hash_table_poly_int_cst_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_poly_int_cst_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_poly_int_cst_hasher_ (void *);
#define gt_pch_n_28hash_table_cl_option_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_cl_option_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_cl_option_hasher_ (void *);
#define gt_pch_n_38hash_table_tree_decl_map_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tree_decl_map_cache_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tree_decl_map_cache_hasher_ (void *);
#define gt_pch_n_37hash_table_tree_vec_map_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tree_vec_map_cache_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tree_vec_map_cache_hasher_ (void *);
#define gt_pch_n_43hash_map_tree_long_identifier_count_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_long_identifier_count_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_long_identifier_count_traits_ (void *);
#define gt_pch_n_26hash_table_section_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_section_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_section_hasher_ (void *);
#define gt_pch_n_31hash_table_object_block_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_object_block_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_object_block_hasher_ (void *);
#define gt_pch_n_34hash_table_tree_descriptor_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tree_descriptor_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tree_descriptor_hasher_ (void *);
#define gt_pch_n_33hash_table_const_rtx_desc_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_const_rtx_desc_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_const_rtx_desc_hasher_ (void *);
#define gt_pch_n_27hash_table_tm_clone_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tm_clone_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tm_clone_hasher_ (void *);
#define gt_pch_n_15tm_restart_node(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tm_restart_node (X);\
  } while (0)
extern void gt_pch_nx_tm_restart_node (void *);
#define gt_pch_n_19hash_map_tree_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_tree_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_tree_ (void *);
#define gt_pch_n_27hash_table_ssa_name_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_ssa_name_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_ssa_name_hasher_ (void *);
#define gt_pch_n_29hash_table_tm_restart_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tm_restart_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tm_restart_hasher_ (void *);
#define gt_pch_n_28vec_mem_addr_template_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_mem_addr_template_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_mem_addr_template_va_gc_ (void *);
#define gt_pch_n_13scev_info_str(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_scev_info_str (X);\
  } while (0)
extern void gt_pch_nx_scev_info_str (void *);
#define gt_pch_n_28hash_table_scev_info_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_scev_info_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_scev_info_hasher_ (void *);
#define gt_pch_n_20ssa_operand_memory_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ssa_operand_memory_d (X);\
  } while (0)
extern void gt_pch_nx_ssa_operand_memory_d (void *);
#define gt_pch_n_24hash_map_char__unsigned_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_char__unsigned_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_char__unsigned_ (void *);
#define gt_pch_n_18vec_gimple__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_gimple__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_gimple__va_gc_ (void *);
#define gt_pch_n_26vec_ipa_agg_jf_item_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_agg_jf_item_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_agg_jf_item_va_gc_ (void *);
#define gt_pch_n_19ipcp_transformation(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipcp_transformation (X);\
  } while (0)
extern void gt_pch_nx_ipcp_transformation (void *);
#define gt_pch_n_31vec_ipa_param_descriptor_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_param_descriptor_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_param_descriptor_va_gc_ (void *);
#define gt_pch_n_27vec_ipa_argagg_value_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_argagg_value_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_argagg_value_va_gc_ (void *);
#define gt_pch_n_17vec_ipa_vr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_vr_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_vr_va_gc_ (void *);
#define gt_pch_n_33vec_ipa_uid_to_idx_map_elt_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_uid_to_idx_map_elt_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_uid_to_idx_map_elt_va_gc_ (void *);
#define gt_pch_n_24vec_ipa_jump_func_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_jump_func_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_jump_func_va_gc_ (void *);
#define gt_pch_n_39vec_ipa_polymorphic_call_context_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_polymorphic_call_context_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_polymorphic_call_context_va_gc_ (void *);
#define gt_pch_n_17ipa_node_params_t(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_node_params_t (X);\
  } while (0)
extern void gt_pch_nx_ipa_node_params_t (void *);
#define gt_pch_n_19ipa_edge_args_sum_t(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_ipa_edge_args_sum_t (X);\
  } while (0)
extern void gt_pch_nx_ipa_edge_args_sum_t (void *);
#define gt_pch_n_38function_summary_ipcp_transformation__(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_function_summary_ipcp_transformation__ (X);\
  } while (0)
extern void gt_pch_nx_function_summary_ipcp_transformation__ (void *);
#define gt_pch_n_29hash_table_tm_wrapper_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tm_wrapper_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tm_wrapper_hasher_ (void *);
#define gt_pch_n_29hash_table_decl_state_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_decl_state_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_decl_state_hasher_ (void *);
#define gt_pch_n_23vec_expr_eval_op_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_expr_eval_op_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_expr_eval_op_va_gc_ (void *);
#define gt_pch_n_20vec_condition_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_condition_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_condition_va_gc_ (void *);
#define gt_pch_n_37vec_ipa_freqcounting_predicate_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ipa_freqcounting_predicate_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ipa_freqcounting_predicate_va_gc_ (void *);
#define gt_pch_n_44fast_function_summary_ipa_fn_summary__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_fast_function_summary_ipa_fn_summary__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_fast_function_summary_ipa_fn_summary__va_gc_ (void *);
#define gt_pch_n_13tree_type_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_type_map (X);\
  } while (0)
extern void gt_pch_nx_tree_type_map (void *);
#define gt_pch_n_38hash_table_tree_type_map_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_tree_type_map_cache_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_tree_type_map_cache_hasher_ (void *);
#define gt_pch_n_19vec_odr_type_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_odr_type_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_odr_type_va_gc_ (void *);
#define gt_pch_n_19registered_function(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_registered_function (X);\
  } while (0)
extern void gt_pch_nx_registered_function (void *);
#define gt_pch_n_31vec_registered_function__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_registered_function__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_registered_function__va_gc_ (void *);
#define gt_pch_n_35hash_map_tree_registered_function__(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_registered_function__ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_registered_function__ (void *);
#define gt_pch_n_35hash_table_value_annotation_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_value_annotation_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_value_annotation_hasher_ (void *);
#define gt_pch_n_27vec_Entity_Id_va_gc_atomic_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_Entity_Id_va_gc_atomic_ (X);\
  } while (0)
extern void gt_pch_nx_vec_Entity_Id_va_gc_atomic_ (void *);
#define gt_pch_n_19tree_entity_vec_map(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_entity_vec_map (X);\
  } while (0)
extern void gt_pch_nx_tree_entity_vec_map (void *);
#define gt_pch_n_29hash_table_dummy_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_dummy_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_dummy_type_hasher_ (void *);
#define gt_pch_n_11parm_attr_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_parm_attr_d (X);\
  } while (0)
extern void gt_pch_nx_parm_attr_d (void *);
#define gt_pch_n_20vec_parm_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_parm_attr_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_parm_attr_va_gc_ (void *);
#define gt_pch_n_10stmt_group(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_stmt_group (X);\
  } while (0)
extern void gt_pch_nx_stmt_group (void *);
#define gt_pch_n_9elab_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_elab_info (X);\
  } while (0)
extern void gt_pch_nx_elab_info (void *);
#define gt_pch_n_18range_check_info_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_range_check_info_d (X);\
  } while (0)
extern void gt_pch_nx_range_check_info_d (void *);
#define gt_pch_n_27vec_range_check_info_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_range_check_info_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_range_check_info_va_gc_ (void *);
#define gt_pch_n_11loop_info_d(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_loop_info_d (X);\
  } while (0)
extern void gt_pch_nx_loop_info_d (void *);
#define gt_pch_n_20vec_loop_info_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_loop_info_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_loop_info_va_gc_ (void *);
#define gt_pch_n_18gnat_binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_gnat_binding_level (X);\
  } while (0)
extern void gt_pch_nx_gnat_binding_level (void *);
#define gt_pch_n_18packable_type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_packable_type_hash (X);\
  } while (0)
extern void gt_pch_nx_packable_type_hash (void *);
#define gt_pch_n_32hash_table_packable_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_packable_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_packable_type_hasher_ (void *);
#define gt_pch_n_13pad_type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_pad_type_hash (X);\
  } while (0)
extern void gt_pch_nx_pad_type_hash (void *);
#define gt_pch_n_27hash_table_pad_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_pad_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_pad_type_hasher_ (void *);
#define gt_pch_n_15sized_type_hash(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_sized_type_hash (X);\
  } while (0)
extern void gt_pch_nx_sized_type_hash (void *);
#define gt_pch_n_29hash_table_sized_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_sized_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_sized_type_hasher_ (void *);
#define gt_pch_n_12c_label_vars(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_c_label_vars (X);\
  } while (0)
extern void gt_pch_nx_c_label_vars (void *);
#define gt_pch_n_9c_binding(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_c_binding (X);\
  } while (0)
extern void gt_pch_nx_c_binding (void *);
#define gt_pch_n_18vec_c_token_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_c_token_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_c_token_va_gc_ (void *);
#define gt_pch_n_7c_scope(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_c_scope (X);\
  } while (0)
extern void gt_pch_nx_c_scope (void *);
#define gt_pch_n_15c_goto_bindings(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_c_goto_bindings (X);\
  } while (0)
extern void gt_pch_nx_c_goto_bindings (void *);
#define gt_pch_n_28vec_c_goto_bindings_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_c_goto_bindings_p_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_c_goto_bindings_p_va_gc_ (void *);
#define gt_pch_n_15c_inline_static(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_c_inline_static (X);\
  } while (0)
extern void gt_pch_nx_c_inline_static (void *);
#define gt_pch_n_27hash_table_c_struct_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_c_struct_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_c_struct_hasher_ (void *);
#define gt_pch_n_18sorted_fields_type(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_sorted_fields_type (X);\
  } while (0)
extern void gt_pch_nx_sorted_fields_type (void *);
#define gt_pch_n_23vec_const_char_p_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_const_char_p_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_const_char_p_va_gc_ (void *);
#define gt_pch_n_22vec_tree_gc_vec_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_tree_gc_vec_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_tree_gc_vec_va_gc_ (void *);
#define gt_pch_n_11align_stack(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_align_stack (X);\
  } while (0)
extern void gt_pch_nx_align_stack (void *);
#define gt_pch_n_23vec_pending_weak_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_pending_weak_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_pending_weak_va_gc_ (void *);
#define gt_pch_n_31vec_pending_redefinition_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_pending_redefinition_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_pending_redefinition_va_gc_ (void *);
#define gt_pch_n_9opt_stack(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_opt_stack (X);\
  } while (0)
extern void gt_pch_nx_opt_stack (void *);
#define gt_pch_n_8c_parser(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_c_parser (X);\
  } while (0)
extern void gt_pch_nx_c_parser (void *);
#define gt_pch_n_26omp_attribute_pragma_state(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_omp_attribute_pragma_state (X);\
  } while (0)
extern void gt_pch_nx_omp_attribute_pragma_state (void *);
#define gt_pch_n_36vec_c_omp_declare_target_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_c_omp_declare_target_attr_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_c_omp_declare_target_attr_va_gc_ (void *);
#define gt_pch_n_35vec_c_omp_begin_assumes_data_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_c_omp_begin_assumes_data_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_c_omp_begin_assumes_data_va_gc_ (void *);
#define gt_pch_n_16cp_binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cp_binding_level (X);\
  } while (0)
extern void gt_pch_nx_cp_binding_level (void *);
#define gt_pch_n_11cxx_binding(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cxx_binding (X);\
  } while (0)
extern void gt_pch_nx_cxx_binding (void *);
#define gt_pch_n_27vec_cp_class_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cp_class_binding_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cp_class_binding_va_gc_ (void *);
#define gt_pch_n_14cp_token_cache(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cp_token_cache (X);\
  } while (0)
extern void gt_pch_nx_cp_token_cache (void *);
#define gt_pch_n_32vec_deferred_access_check_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_deferred_access_check_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_deferred_access_check_va_gc_ (void *);
#define gt_pch_n_28vec_cxx_saved_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cxx_saved_binding_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cxx_saved_binding_va_gc_ (void *);
#define gt_pch_n_37vec_cp_omp_declare_target_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cp_omp_declare_target_attr_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cp_omp_declare_target_attr_va_gc_ (void *);
#define gt_pch_n_36vec_cp_omp_begin_assumes_data_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cp_omp_begin_assumes_data_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cp_omp_begin_assumes_data_va_gc_ (void *);
#define gt_pch_n_11saved_scope(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_saved_scope (X);\
  } while (0)
extern void gt_pch_nx_saved_scope (void *);
#define gt_pch_n_17named_label_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_named_label_entry (X);\
  } while (0)
extern void gt_pch_nx_named_label_entry (void *);
#define gt_pch_n_28hash_table_named_label_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_named_label_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_named_label_hash_ (void *);
#define gt_pch_n_11tree_pair_s(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_pair_s (X);\
  } while (0)
extern void gt_pch_nx_tree_pair_s (void *);
#define gt_pch_n_22vec_tree_pair_s_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_tree_pair_s_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_tree_pair_s_va_gc_ (void *);
#define gt_pch_n_27hash_table_named_decl_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_named_decl_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_named_decl_hash_ (void *);
#define gt_pch_n_10spec_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_spec_entry (X);\
  } while (0)
extern void gt_pch_nx_spec_entry (void *);
#define gt_pch_n_11tinst_level(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tinst_level (X);\
  } while (0)
extern void gt_pch_nx_tinst_level (void *);
#define gt_pch_n_46hash_map_tree_location_t_decl_location_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_location_t_decl_location_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_location_t_decl_location_traits_ (void *);
#define gt_pch_n_12module_state(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_module_state (X);\
  } while (0)
extern void gt_pch_nx_module_state (void *);
#define gt_pch_n_16constexpr_fundef(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_constexpr_fundef (X);\
  } while (0)
extern void gt_pch_nx_constexpr_fundef (void *);
#define gt_pch_n_10tree_check(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_tree_check (X);\
  } while (0)
extern void gt_pch_nx_tree_check (void *);
#define gt_pch_n_19vec_cp_token_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cp_token_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cp_token_va_gc_ (void *);
#define gt_pch_n_8cp_lexer(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cp_lexer (X);\
  } while (0)
extern void gt_pch_nx_cp_lexer (void *);
#define gt_pch_n_31vec_cp_default_arg_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cp_default_arg_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cp_default_arg_entry_va_gc_ (void *);
#define gt_pch_n_17cp_parser_context(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cp_parser_context (X);\
  } while (0)
extern void gt_pch_nx_cp_parser_context (void *);
#define gt_pch_n_38vec_cp_unparsed_functions_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_cp_unparsed_functions_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_cp_unparsed_functions_entry_va_gc_ (void *);
#define gt_pch_n_9cp_parser(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_cp_parser (X);\
  } while (0)
extern void gt_pch_nx_cp_parser (void *);
#define gt_pch_n_18hash_map_tree_int_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_int_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_int_ (void *);
#define gt_pch_n_35hash_table_constexpr_fundef_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_constexpr_fundef_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_constexpr_fundef_hasher_ (void *);
#define gt_pch_n_14constexpr_call(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_constexpr_call (X);\
  } while (0)
extern void gt_pch_nx_constexpr_call (void *);
#define gt_pch_n_33hash_table_constexpr_call_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_constexpr_call_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_constexpr_call_hasher_ (void *);
#define gt_pch_n_10norm_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_norm_entry (X);\
  } while (0)
extern void gt_pch_nx_norm_entry (void *);
#define gt_pch_n_23hash_table_norm_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_norm_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_norm_hasher_ (void *);
#define gt_pch_n_23hash_table_atom_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_atom_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_atom_hasher_ (void *);
#define gt_pch_n_9sat_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_sat_entry (X);\
  } while (0)
extern void gt_pch_nx_sat_entry (void *);
#define gt_pch_n_22hash_table_sat_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_sat_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_sat_hasher_ (void *);
#define gt_pch_n_14coroutine_info(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_coroutine_info (X);\
  } while (0)
extern void gt_pch_nx_coroutine_info (void *);
#define gt_pch_n_33hash_table_coroutine_info_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_coroutine_info_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_coroutine_info_hasher_ (void *);
#define gt_pch_n_27source_location_table_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_source_location_table_entry (X);\
  } while (0)
extern void gt_pch_nx_source_location_table_entry (void *);
#define gt_pch_n_44hash_table_source_location_table_entry_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_source_location_table_entry_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_source_location_table_entry_hash_ (void *);
#define gt_pch_n_21named_label_use_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_named_label_use_entry (X);\
  } while (0)
extern void gt_pch_nx_named_label_use_entry (void *);
#define gt_pch_n_25vec_incomplete_var_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_incomplete_var_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_incomplete_var_va_gc_ (void *);
#define gt_pch_n_27hash_table_typename_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_typename_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_typename_hasher_ (void *);
#define gt_pch_n_29hash_table_mangled_decl_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_mangled_decl_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_mangled_decl_hash_ (void *);
#define gt_pch_n_43hash_map_unsigned_tree_priority_map_traits_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_unsigned_tree_priority_map_traits_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_unsigned_tree_priority_map_traits_ (void *);
#define gt_pch_n_27vec_pending_noexcept_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_pending_noexcept_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_pending_noexcept_va_gc_ (void *);
#define gt_pch_n_27vec_lambda_sig_count_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_lambda_sig_count_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_lambda_sig_count_va_gc_ (void *);
#define gt_pch_n_31vec_lambda_discriminator_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_lambda_discriminator_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_lambda_discriminator_va_gc_ (void *);
#define gt_pch_n_28hash_table_conv_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_conv_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_conv_type_hasher_ (void *);
#define gt_pch_n_17subsumption_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_subsumption_entry (X);\
  } while (0)
extern void gt_pch_nx_subsumption_entry (void *);
#define gt_pch_n_30hash_table_subsumption_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_subsumption_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_subsumption_hasher_ (void *);
#define gt_pch_n_8slurping(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_slurping (X);\
  } while (0)
extern void gt_pch_nx_slurping (void *);
#define gt_pch_n_24vec_module_state__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_module_state__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_module_state__va_gc_ (void *);
#define gt_pch_n_29hash_table_module_state_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_module_state_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_module_state_hash_ (void *);
#define gt_pch_n_33hash_table_note_def_cache_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_note_def_cache_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_note_def_cache_hasher_ (void *);
#define gt_pch_n_23vec_macro_export_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_macro_export_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_macro_export_va_gc_ (void *);
#define gt_pch_n_16pending_template(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_pending_template (X);\
  } while (0)
extern void gt_pch_nx_pending_template (void *);
#define gt_pch_n_23hash_table_spec_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_spec_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_spec_hasher_ (void *);
#define gt_pch_n_22hash_table_ctp_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_ctp_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_ctp_hasher_ (void *);
#define gt_pch_n_25hash_map_const_tree_tree_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_const_tree_tree_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_const_tree_tree_ (void *);
#define gt_pch_n_26hash_map_tree_tree_pair_p_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_tree_pair_p_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_tree_pair_p_ (void *);
#define gt_pch_n_18vec_tinfo_s_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_tinfo_s_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_tinfo_s_va_gc_ (void *);
#define gt_pch_n_26vec_deferred_access_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_deferred_access_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_deferred_access_va_gc_ (void *);
#define gt_pch_n_19hash_map_tree_bool_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_tree_bool_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_tree_bool_ (void *);
#define gt_pch_n_30hash_table_cplus_array_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_cplus_array_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_cplus_array_hasher_ (void *);
#define gt_pch_n_23hash_table_list_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_list_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_list_hasher_ (void *);
#define gt_pch_n_9Statement(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_Statement (X);\
  } while (0)
extern void gt_pch_nx_Statement (void *);
#define gt_pch_n_13binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_binding_level (X);\
  } while (0)
extern void gt_pch_nx_binding_level (void *);
#define gt_pch_n_17d_label_use_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_d_label_use_entry (X);\
  } while (0)
extern void gt_pch_nx_d_label_use_entry (void *);
#define gt_pch_n_34hash_map_Statement__d_label_entry_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_map_Statement__d_label_entry_ (X);\
  } while (0)
extern void gt_pch_nx_hash_map_Statement__d_label_entry_ (void *);
#define gt_pch_n_25hash_table_module_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_module_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_module_hasher_ (void *);
#define gt_pch_n_17module_htab_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_module_htab_entry (X);\
  } while (0)
extern void gt_pch_nx_module_htab_entry (void *);
#define gt_pch_n_30hash_table_module_decl_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_module_decl_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_module_decl_hasher_ (void *);
#define gt_pch_n_7rtenode(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rtenode (X);\
  } while (0)
extern void gt_pch_nx_rtenode (void *);
#define gt_pch_n_19vec_rtenode__va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_rtenode__va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_rtenode__va_gc_ (void *);
#define gt_pch_n_35vec_builtin_macro_definition_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_builtin_macro_definition_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_builtin_macro_definition_va_gc_ (void *);
#define gt_pch_n_18struct_constructor(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_struct_constructor (X);\
  } while (0)
extern void gt_pch_nx_struct_constructor (void *);
#define gt_pch_n_10array_desc(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_array_desc (X);\
  } while (0)
extern void gt_pch_nx_array_desc (void *);
#define gt_pch_n_16objc_map_private(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_objc_map_private (X);\
  } while (0)
extern void gt_pch_nx_objc_map_private (void *);
#define gt_pch_n_12hashed_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hashed_entry (X);\
  } while (0)
extern void gt_pch_nx_hashed_entry (void *);
#define gt_pch_n_16hashed_attribute(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hashed_attribute (X);\
  } while (0)
extern void gt_pch_nx_hashed_attribute (void *);
#define gt_pch_n_9imp_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_imp_entry (X);\
  } while (0)
extern void gt_pch_nx_imp_entry (void *);
#define gt_pch_n_17string_descriptor(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_string_descriptor (X);\
  } while (0)
extern void gt_pch_nx_string_descriptor (void *);
#define gt_pch_n_30hash_table_objc_string_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_objc_string_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_objc_string_hasher_ (void *);
#define gt_pch_n_27vec_ident_data_tuple_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ident_data_tuple_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ident_data_tuple_va_gc_ (void *);
#define gt_pch_n_23vec_msgref_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_msgref_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_msgref_entry_va_gc_ (void *);
#define gt_pch_n_26vec_prot_list_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_prot_list_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_prot_list_entry_va_gc_ (void *);
#define gt_pch_n_24vec_ivarref_entry_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_ivarref_entry_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_ivarref_entry_va_gc_ (void *);
#define gt_pch_n_21rust_constexpr_fundef(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rust_constexpr_fundef (X);\
  } while (0)
extern void gt_pch_nx_rust_constexpr_fundef (void *);
#define gt_pch_n_19rust_constexpr_call(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rust_constexpr_call (X);\
  } while (0)
extern void gt_pch_nx_rust_constexpr_call (void *);
#define gt_pch_n_40hash_table_rust_constexpr_fundef_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_constexpr_fundef_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_constexpr_fundef_hasher_ (void *);
#define gt_pch_n_38hash_table_rust_constexpr_call_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_constexpr_call_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_constexpr_call_hasher_ (void *);
#define gt_pch_n_33vec_rust_cxx_saved_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_rust_cxx_saved_binding_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_rust_cxx_saved_binding_va_gc_ (void *);
#define gt_pch_n_34vec_omp_declare_target_attr_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_omp_declare_target_attr_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_omp_declare_target_attr_va_gc_ (void *);
#define gt_pch_n_32vec_rust_cp_class_binding_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_rust_cp_class_binding_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_rust_cp_class_binding_va_gc_ (void *);
#define gt_pch_n_21rust_cp_binding_level(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rust_cp_binding_level (X);\
  } while (0)
extern void gt_pch_nx_rust_cp_binding_level (void *);
#define gt_pch_n_22rust_named_label_entry(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_rust_named_label_entry (X);\
  } while (0)
extern void gt_pch_nx_rust_named_label_entry (void *);
#define gt_pch_n_33hash_table_rust_named_label_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_named_label_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_named_label_hash_ (void *);
#define gt_pch_n_32hash_table_rust_named_decl_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_named_decl_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_named_decl_hash_ (void *);
#define gt_pch_n_27vec_rust_tree_pair_s_va_gc_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_vec_rust_tree_pair_s_va_gc_ (X);\
  } while (0)
extern void gt_pch_nx_vec_rust_tree_pair_s_va_gc_ (void *);
#define gt_pch_n_33hash_table_rust_conv_type_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_conv_type_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_conv_type_hasher_ (void *);
#define gt_pch_n_35hash_table_rust_cplus_array_hasher_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_cplus_array_hasher_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_cplus_array_hasher_ (void *);
#define gt_pch_n_49hash_table_rust_source_location_table_entry_hash_(X) do { \
  if ((intptr_t)(X) != 0) gt_pch_nx_hash_table_rust_source_location_table_entry_hash_ (X);\
  } while (0)
extern void gt_pch_nx_hash_table_rust_source_location_table_entry_hash_ (void *);

/* functions code */

/* Local pointer-walking routines.  */
#define gt_pch_p_9tree_node gt_pch_p_14lang_tree_node
extern void gt_pch_p_9line_maps
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9cpp_token
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9cpp_macro
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18cpp_hashnode_extra
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13string_concat
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16string_concat_db
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_38hash_map_location_hash_string_concat__
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11bitmap_head
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtx_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9rtvec_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11dw_cfi_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11symtab_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11symtab_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11symtab_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11cgraph_edge
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7section
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16cl_target_option
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15cl_optimization
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8edge_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15basic_block_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_unsigned_va_gc_atomic_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14hash_set_tree_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16machine_function
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14bitmap_element
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13coverage_data
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9mem_attrs
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9reg_attrs
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12object_block
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14vec_rtx_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11fixed_value
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23constant_descriptor_rtx
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8function
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10target_rtl
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15cgraph_rtl_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_42hash_map_tree_tree_decl_tree_cache_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_42hash_map_tree_tree_type_tree_cache_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_36hash_map_tree_tree_decl_tree_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12ptr_info_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10die_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_constructor_elt_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14vrange_storage
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15vec_tree_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9lang_type
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9lang_decl
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24tree_statement_list_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14target_globals
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14lang_tree_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8tree_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13tree_decl_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12tree_int_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12tree_vec_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21vec_alias_pair_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13libfunc_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26hash_table_libfunc_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15target_libfuncs
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14sequence_stack
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20vec_rtx_insn__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18call_site_record_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16vec_uchar_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_call_site_record_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9gimple_df
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11dw_fde_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17rtx_constant_pool
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11frame_space
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_callinfo_callee_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_callinfo_dalloc_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11stack_usage
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9eh_status
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18control_flow_graph
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_5loops
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17language_function
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24types_used_by_vars_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_used_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13nb_iter_bound
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9loop_exit
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_4loop
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10control_iv
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17vec_loop_p_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10niter_desc
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_loop_exit_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22vec_basic_block_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11rtl_bb_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15vec_edge_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18section_hash_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18lto_file_decl_data
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15ipa_replace_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17cgraph_simd_clone
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28cgraph_function_version_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_cgraph_edge_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_25cgraph_indirect_call_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8asm_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10thunk_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29function_summary_thunk_info__
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10clone_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29function_summary_clone_info__
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12symbol_table
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31hash_table_section_name_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26hash_table_asmname_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_42hash_map_symtab_node__symbol_priority_map_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24constant_descriptor_tree
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28vec_unprocessed_thunk_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_ipa_replace_map__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21ipa_param_adjustments
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_map_alias_set_hash_int_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15alias_set_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_alias_set_entry__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35hash_table_function_version_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17lto_in_decl_state
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_34hash_table_ipa_vr_ggc_hash_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6ipa_vr
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24ipa_return_value_summary
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_43function_summary_ipa_return_value_summary__
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15ipa_node_params
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13ipa_edge_args
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14ipa_fn_summary
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10odr_type_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29vec_ipa_adjusted_param_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12param_access
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_param_access__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17isra_func_summary
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_isra_param_desc_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26ipa_sra_function_summaries
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27modref_tree_alias_set_type_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14modref_summary
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18modref_summary_lto
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_44fast_function_summary_modref_summary__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_48fast_function_summary_modref_summary_lto__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17modref_tree_tree_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_37hash_map_location_hash_nowarn_spec_t_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17dw_loc_descr_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18dw_loc_list_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18dw_discr_list_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11dw_wide_int
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15dw_cfa_location
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21vec_dw_cfi_ref_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16addr_table_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20indirect_string_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15dwarf_file_data
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20hash_map_char__tree_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10dw_cfi_row
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17reg_saved_in_data
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21vec_dw_fde_ref_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_34hash_table_indirect_string_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16vec_char__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16comdat_type_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29vec_dw_line_info_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18dw_line_info_table
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23vec_dw_attr_node_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16limbo_die_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_dwarf_file_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_decl_die_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21vec_dw_die_ref_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21variable_value_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_variable_value_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_block_die_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12var_loc_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16var_loc_list_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17call_arg_loc_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_decl_loc_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22cached_dw_loc_list_def
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_dw_loc_list_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30vec_dw_line_info_table__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_pubname_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_macinfo_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20vec_dw_ranges_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29vec_dw_ranges_by_label_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_die_arg_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23hash_table_addr_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_map_tree_sym_off_pair_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17inline_entry_data
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_36hash_table_inline_entry_data_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9ctf_dtdef
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10ctf_string
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9ctf_dmdef
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12ctf_func_arg
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9ctf_dvdef
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_ctfc_dtd_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_ctfc_dvd_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13ctf_container
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_ctf_dtdef_ref_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_37hash_map_ctf_dtdef_ref_ctf_dtdef_ref_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23hash_set_ctf_dtdef_ref_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9temp_slot
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20initial_value_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22vec_temp_slot_p_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_const_int_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_const_wide_int_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_const_poly_int_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_reg_attr_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31hash_table_const_double_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_const_fixed_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11eh_region_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16eh_landing_pad_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10eh_catch_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20vec_eh_region_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_25vec_eh_landing_pad_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21hash_map_gimple__int_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_insn_cache_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23temp_slot_address_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31hash_table_temp_address_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24hash_map_tree_hash_tree_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11test_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14test_of_length
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10test_other
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13test_of_union
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12example_base
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12example_base
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12example_base
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9test_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11user_struct
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31hash_table_libfunc_decl_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16string_pool_data
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22string_pool_data_extra
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9type_hash
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_type_cache_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26hash_table_int_cst_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31hash_table_poly_int_cst_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_cl_option_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_38hash_table_tree_decl_map_cache_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_37hash_table_tree_vec_map_cache_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_43hash_map_tree_long_identifier_count_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26hash_table_section_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31hash_table_object_block_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_34hash_table_tree_descriptor_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_const_rtx_desc_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_tm_clone_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_6gimple
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15tm_restart_node
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19hash_map_tree_tree_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_ssa_name_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_tm_restart_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28vec_mem_addr_template_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13scev_info_str
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_scev_info_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20ssa_operand_memory_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24hash_map_char__unsigned_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18vec_gimple__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_ipa_agg_jf_item_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19ipcp_transformation
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31vec_ipa_param_descriptor_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_ipa_argagg_value_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17vec_ipa_vr_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33vec_ipa_uid_to_idx_map_elt_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_ipa_jump_func_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_39vec_ipa_polymorphic_call_context_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17ipa_node_params_t
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19ipa_edge_args_sum_t
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_38function_summary_ipcp_transformation__
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_tm_wrapper_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_decl_state_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23vec_expr_eval_op_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20vec_condition_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_37vec_ipa_freqcounting_predicate_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_44fast_function_summary_ipa_fn_summary__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13tree_type_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_38hash_table_tree_type_map_cache_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19vec_odr_type_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19registered_function
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31vec_registered_function__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35hash_map_tree_registered_function__
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35hash_table_value_annotation_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_Entity_Id_va_gc_atomic_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19tree_entity_vec_map
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_dummy_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11parm_attr_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20vec_parm_attr_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10stmt_group
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9elab_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18range_check_info_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_range_check_info_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11loop_info_d
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_20vec_loop_info_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18gnat_binding_level
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18packable_type_hash
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_32hash_table_packable_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13pad_type_hash
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_pad_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15sized_type_hash
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_sized_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12c_label_vars
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9c_binding
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18vec_c_token_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7c_scope
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15c_goto_bindings
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28vec_c_goto_bindings_p_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_15c_inline_static
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_c_struct_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18sorted_fields_type
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23vec_const_char_p_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22vec_tree_gc_vec_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11align_stack
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23vec_pending_weak_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31vec_pending_redefinition_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9opt_stack
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8c_parser
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26omp_attribute_pragma_state
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_36vec_c_omp_declare_target_attr_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35vec_c_omp_begin_assumes_data_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16cp_binding_level
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11cxx_binding
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_cp_class_binding_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14cp_token_cache
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_32vec_deferred_access_check_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28vec_cxx_saved_binding_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_37vec_cp_omp_declare_target_attr_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_36vec_cp_omp_begin_assumes_data_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11saved_scope
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17named_label_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_named_label_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11tree_pair_s
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22vec_tree_pair_s_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_named_decl_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10spec_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_11tinst_level
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_46hash_map_tree_location_t_decl_location_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12module_state
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16constexpr_fundef
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10tree_check
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19vec_cp_token_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8cp_lexer
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31vec_cp_default_arg_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17cp_parser_context
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_38vec_cp_unparsed_functions_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9cp_parser
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18hash_map_tree_int_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35hash_table_constexpr_fundef_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14constexpr_call
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_constexpr_call_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10norm_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23hash_table_norm_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23hash_table_atom_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9sat_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22hash_table_sat_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_14coroutine_info
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_coroutine_info_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27source_location_table_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_44hash_table_source_location_table_entry_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21named_label_use_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_25vec_incomplete_var_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27hash_table_typename_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_mangled_decl_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_43hash_map_unsigned_tree_priority_map_traits_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_pending_noexcept_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_lambda_sig_count_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_31vec_lambda_discriminator_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_28hash_table_conv_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17subsumption_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_subsumption_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_8slurping
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_module_state__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_29hash_table_module_state_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_note_def_cache_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23vec_macro_export_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16pending_template
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23hash_table_spec_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22hash_table_ctp_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_25hash_map_const_tree_tree_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26hash_map_tree_tree_pair_p_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18vec_tinfo_s_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_deferred_access_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19hash_map_tree_bool_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_cplus_array_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23hash_table_list_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9Statement
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_13binding_level
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17d_label_use_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_34hash_map_Statement__d_label_entry_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_25hash_table_module_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17module_htab_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_module_decl_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_7rtenode
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19vec_rtenode__va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35vec_builtin_macro_definition_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_18struct_constructor
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_10array_desc
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16objc_map_private
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_12hashed_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_16hashed_attribute
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_9imp_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_17string_descriptor
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_30hash_table_objc_string_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_ident_data_tuple_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_23vec_msgref_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_26vec_prot_list_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_24vec_ivarref_entry_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21rust_constexpr_fundef
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_19rust_constexpr_call
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_40hash_table_rust_constexpr_fundef_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_38hash_table_rust_constexpr_call_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33vec_rust_cxx_saved_binding_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_34vec_omp_declare_target_attr_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_32vec_rust_cp_class_binding_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_21rust_cp_binding_level
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_22rust_named_label_entry
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_rust_named_label_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_32hash_table_rust_named_decl_hash_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_27vec_rust_tree_pair_s_va_gc_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_33hash_table_rust_conv_type_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_35hash_table_rust_cplus_array_hasher_
    (void *, void *, gt_pointer_operator, void *);
extern void gt_pch_p_49hash_table_rust_source_location_table_entry_hash_
    (void *, void *, gt_pointer_operator, void *);
