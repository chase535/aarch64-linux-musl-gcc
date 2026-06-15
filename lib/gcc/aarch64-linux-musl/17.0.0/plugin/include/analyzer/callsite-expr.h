/* User-facing descriptions of expressions at call sites.
   Copyright (C) 2019-2026 Free Software Foundation, Inc.
   Contributed by David Malcolm <dmalcolm@redhat.com>.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#ifndef GCC_ANALYZER_CALLSITE_EXPR_H
#define GCC_ANALYZER_CALLSITE_EXPR_H

#include "pretty-print-markup.h"

namespace ana {

/* An ID representing an expression at a callsite:
   either a parameter index, or the return value (or unknown).  */

class callsite_expr
{
 public:
  callsite_expr () : m_val (-1) {}

  static callsite_expr from_zero_based_param (int idx)
  {
    return callsite_expr (idx + 1);
  }

  static callsite_expr from_return_value ()
  {
    return callsite_expr (0);
  }

  bool param_p () const
  {
    return m_val > 0;
  }

  /* Get 1-based param number.  */
  int param_num () const
  {
    gcc_assert (param_p ());
    return m_val;
  }

  tree get_param_tree (tree fndecl) const;

  bool
  maybe_get_param_location (tree fndecl,
			    location_t *out_loc) const;

  bool return_value_p () const
  {
    return m_val == 0;
  }

 private:
  callsite_expr (int val) : m_val (val) {}

  int m_val; /* 1-based parm, 0 for return value, or -1 for "unknown".  */
};

class callsite_expr_element : public pp_element
{
public:
  callsite_expr_element (callsite_expr expr) : m_expr (expr) {}

  void
  add_to_phase_2 (pp_markup::context &ctxt) final override
  {

    if (m_expr.return_value_p ())
      pp_string (&ctxt.m_pp, "return value");
    else if (m_expr.param_p ())
      {
	/* We can't call pp_printf directly on ctxt.m_pp from within
	   formatting.  As a workaround, work with a clone of the pp.  */
	std::unique_ptr<pretty_printer> pp (ctxt.m_pp.clone ());
	pp_printf (pp.get (), "parameter %i", m_expr.param_num ());
	pp_string (&ctxt.m_pp, pp_formatted_text (pp.get ()));
      }
    else
      pp_string (&ctxt.m_pp, "unknown");
  }

private:
  callsite_expr m_expr;
};

} // namespace ana

#endif /* GCC_ANALYZER_CALLSITE_EXPR_H */
