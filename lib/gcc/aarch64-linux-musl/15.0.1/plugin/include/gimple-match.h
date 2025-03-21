/* Gimple simplify definitions.

   Copyright (C) 2011-2025 Free Software Foundation, Inc.
   Contributed by Richard Guenther <rguenther@suse.de>

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

#ifndef GCC_GIMPLE_MATCH_H
#define GCC_GIMPLE_MATCH_H


/* Represents the condition under which an operation should happen,
   and the value to use otherwise.  The condition applies elementwise
   (as for VEC_COND_EXPR) if the values are vectors.  */
class gimple_match_cond
{
public:
  enum uncond { UNCOND };

  /* Build an unconditional op.  */
  gimple_match_cond (uncond) : cond (NULL_TREE), else_value (NULL_TREE), len
			       (NULL_TREE), bias (NULL_TREE) {}
  gimple_match_cond (tree, tree);
  gimple_match_cond (tree, tree, tree, tree);

  gimple_match_cond any_else () const;

  /* The condition under which the operation occurs, or NULL_TREE
     if the operation is unconditional.  */
  tree cond;

  /* The value to use when the condition is false.  This is NULL_TREE if
     the operation is unconditional or if the value doesn't matter.  */
  tree else_value;

  /* The length and bias parameters to be applied to a vector operation,
     so that the condition is forced to false when the element index is
     >= LEN + BIAS.  These are NULL_TREE if the operation isn't applied
     to vectors, or if no such length limit is in use.  */
  tree len;
  tree bias;
};

inline
gimple_match_cond::gimple_match_cond (tree cond_in, tree else_value_in)
  : cond (cond_in), else_value (else_value_in), len (NULL_TREE),
    bias (NULL_TREE)
{
}

inline
gimple_match_cond::gimple_match_cond (tree cond_in, tree else_value_in,
				      tree len_in, tree bias_in)
  : cond (cond_in), else_value (else_value_in), len (len_in), bias (bias_in)
{}

/* Return a gimple_match_cond with the same condition but with an
   arbitrary ELSE_VALUE.  */

inline gimple_match_cond
gimple_match_cond::any_else () const
{
  return gimple_match_cond (cond, NULL_TREE);
}

/* Represents an operation to be simplified, or the result of the
   simplification.  */
class gimple_match_op
{
public:
  gimple_match_op ();
  gimple_match_op (const gimple_match_cond &, code_helper, tree, unsigned int);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree, tree);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree, tree, tree);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree, tree, tree, tree);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree, tree, tree, tree, tree);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree, tree, tree, tree, tree, tree);
  gimple_match_op (const gimple_match_cond &,
		   code_helper, tree, tree, tree, tree, tree, tree, tree, tree);

  void set_op (code_helper, tree, unsigned int);
  void set_op (code_helper, tree, tree);
  void set_op (code_helper, tree, tree, tree);
  void set_op (code_helper, tree, tree, tree, tree);
  void set_op (code_helper, tree, tree, tree, tree, bool);
  void set_op (code_helper, tree, tree, tree, tree, tree);
  void set_op (code_helper, tree, tree, tree, tree, tree, tree);
  void set_op (code_helper, tree, tree, tree, tree, tree, tree, tree);
  void set_op (code_helper, tree, tree, tree, tree, tree, tree, tree, tree);
  void set_value (tree);

  tree op_or_null (unsigned int) const;

  bool resimplify (gimple_seq *, tree (*)(tree));

  /* The maximum value of NUM_OPS.  */
  static const unsigned int MAX_NUM_OPS = 7;

  /* The conditions under which the operation is performed, and the value to
     use as a fallback.  */
  gimple_match_cond cond;

  /* The operation being performed.  */
  code_helper code;

  /* The type of the result.  */
  tree type;

  /* For a BIT_FIELD_REF, whether the group of bits is stored in reverse order
     from the target order.  */
  bool reverse;

  /* The number of operands to CODE.  */
  unsigned int num_ops;

  /* The operands to CODE.  Only the first NUM_OPS entries are meaningful.  */
  tree ops[MAX_NUM_OPS];

  bool operands_occurs_in_abnormal_phi() const;
};

inline
gimple_match_op::gimple_match_op ()
  : cond (gimple_match_cond::UNCOND), type (NULL_TREE), reverse (false),
    num_ops (0)
{
}

/* Constructor that takes the condition, code, type and number of
   operands, but leaves the caller to fill in the operands.  */

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  unsigned int num_ops_in)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (num_ops_in)
{
}

/* Constructors for various numbers of operands.  */

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (1)
{
  ops[0] = op0;
}

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0, tree op1)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (2)
{
  ops[0] = op0;
  ops[1] = op1;
}

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0, tree op1, tree op2)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (3)
{
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
}

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0, tree op1, tree op2, tree op3)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (4)
{
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
}

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0, tree op1, tree op2, tree op3,
				  tree op4)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (5)
{
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
  ops[4] = op4;
}

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0, tree op1, tree op2, tree op3,
				  tree op4, tree op5)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (6)
{
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
  ops[4] = op4;
  ops[5] = op5;
}

inline
gimple_match_op::gimple_match_op (const gimple_match_cond &cond_in,
				  code_helper code_in, tree type_in,
				  tree op0, tree op1, tree op2, tree op3,
				  tree op4, tree op5, tree op6)
  : cond (cond_in), code (code_in), type (type_in), reverse (false),
    num_ops (7)
{
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
  ops[4] = op4;
  ops[5] = op5;
  ops[6] = op6;
}

/* Change the operation performed to CODE_IN, the type of the result to
   TYPE_IN, and the number of operands to NUM_OPS_IN.  The caller needs
   to set the operands itself.  */

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 unsigned int num_ops_in)
{
  code = code_in;
  type = type_in;
  num_ops = num_ops_in;
}

/* Functions for changing the operation performed, for various numbers
   of operands.  */

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in, tree op0)
{
  code = code_in;
  type = type_in;
  num_ops = 1;
  ops[0] = op0;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in, tree op0, tree op1)
{
  code = code_in;
  type = type_in;
  num_ops = 2;
  ops[0] = op0;
  ops[1] = op1;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 tree op0, tree op1, tree op2)
{
  code = code_in;
  type = type_in;
  num_ops = 3;
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 tree op0, tree op1, tree op2, bool reverse_in)
{
  code = code_in;
  type = type_in;
  reverse = reverse_in;
  num_ops = 3;
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 tree op0, tree op1, tree op2, tree op3)
{
  code = code_in;
  type = type_in;
  num_ops = 4;
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 tree op0, tree op1, tree op2, tree op3, tree op4)
{
  code = code_in;
  type = type_in;
  num_ops = 5;
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
  ops[4] = op4;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 tree op0, tree op1, tree op2, tree op3, tree op4,
			 tree op5)
{
  code = code_in;
  type = type_in;
  num_ops = 6;
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
  ops[4] = op4;
  ops[5] = op5;
}

inline void
gimple_match_op::set_op (code_helper code_in, tree type_in,
			 tree op0, tree op1, tree op2, tree op3, tree op4,
			 tree op5, tree op6)
{
  code = code_in;
  type = type_in;
  num_ops = 7;
  ops[0] = op0;
  ops[1] = op1;
  ops[2] = op2;
  ops[3] = op3;
  ops[4] = op4;
  ops[5] = op5;
  ops[6] = op6;
}

/* Set the "operation" to be the single value VALUE, such as a constant
   or SSA_NAME.  */

inline void
gimple_match_op::set_value (tree value)
{
  set_op (TREE_CODE (value), TREE_TYPE (value), value);
}

/* Return the value of operand I, or null if there aren't that many
   operands.  */

inline tree
gimple_match_op::op_or_null (unsigned int i) const
{
  return i < num_ops ? ops[i] : NULL_TREE;
}

/* Return whether OP is a non-expression result and a gimple value.  */

inline bool
gimple_simplified_result_is_gimple_val (const gimple_match_op *op)
{
  return (op->code.is_tree_code ()
	  && (TREE_CODE_LENGTH ((tree_code) op->code) == 0
	      || ((tree_code) op->code) == ADDR_EXPR)
	  && is_gimple_val (op->ops[0]));
}

extern tree (*mprts_hook) (gimple_match_op *);

bool gimple_extract_op (gimple *, gimple_match_op *);
bool gimple_simplify (gimple *, gimple_match_op *, gimple_seq *,
		      tree (*)(tree), tree (*)(tree));
tree maybe_push_res_to_seq (gimple_match_op *, gimple_seq *,
			    tree res = NULL_TREE);
void maybe_build_generic_op (gimple_match_op *);

bool commutative_binary_op_p (code_helper, tree);
bool commutative_ternary_op_p (code_helper, tree);
int first_commutative_argument (code_helper, tree);
bool associative_binary_op_p (code_helper, tree);
code_helper canonicalize_code (code_helper, tree);

#ifdef GCC_OPTABS_TREE_H
bool directly_supported_p (code_helper, tree, optab_subtype = optab_default);
bool directly_supported_p (code_helper, tree, tree,
			   optab_subtype = optab_default);
#endif

internal_fn get_conditional_internal_fn (code_helper, tree);

#endif  /* GCC_GIMPLE_MATCH_H */
