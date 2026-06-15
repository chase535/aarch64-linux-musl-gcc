/* Classes for tracking pertinent events that happen along
   an execution path.
   Copyright (C) 2026 Free Software Foundation, Inc.
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

#ifndef GCC_ANALYZER_STATE_TRANSITION_H
#define GCC_ANALYZER_STATE_TRANSITION_H

#include "diagnostics/event-id.h"
#include "analyzer/callsite-expr.h"

namespace ana {

class state_transition
{
public:
  enum class kind
  {
    origin,
    at_call,
    at_return,
    copy,
    use
  };

  state_transition ()
  : m_prev_state_transition (nullptr)
  {
  }

  virtual ~state_transition () {}

  virtual std::unique_ptr<state_transition>
  clone () const = 0;

  virtual void
  dump_to_pp (pretty_printer *pp) const = 0;

  virtual enum kind get_kind () const = 0;

  virtual const state_transition_at_call *
  dyn_cast_state_transition_at_call () const { return nullptr; }

  virtual const state_transition_at_return *
  dyn_cast_state_transition_at_return () const { return nullptr; }

  void dump () const;

  static std::unique_ptr<state_transition>
  make (const region *src_reg,
	tree src_reg_expr,
	const region *dst_reg,
	tree dst_reg_expr);

  diagnostics::paths::event_id_t
  get_src_event_id () const;

  state_transition *m_prev_state_transition;
  diagnostics::paths::event_id_t m_event_id;
};

class state_transition_origin : public state_transition
{
public:
  state_transition_origin (tree dst_reg_expr)
  : m_dst_reg_expr (dst_reg_expr)
  {
  }

  std::unique_ptr<state_transition>
  clone () const final override;

  void
  dump_to_pp (pretty_printer *pp) const final override;

  enum kind
  get_kind () const final override { return kind::origin; }

  tree m_dst_reg_expr;
};

class state_transition_at_call : public state_transition
{
public:
  state_transition_at_call (callsite_expr expr)
  : m_expr (expr)
  {
  }

  std::unique_ptr<state_transition>
  clone () const final override;

  void
  dump_to_pp (pretty_printer *pp) const final override;

  enum kind
  get_kind () const final override { return kind::at_call; }

  const state_transition_at_call *
  dyn_cast_state_transition_at_call () const final override { return this; }

  callsite_expr
  get_callsite_expr () const { return m_expr; }

private:
  callsite_expr m_expr;
};

class state_transition_at_return : public state_transition
{
public:
  std::unique_ptr<state_transition>
  clone () const final override;

  void
  dump_to_pp (pretty_printer *pp) const final override;

  enum kind
  get_kind () const final override { return kind::at_return; }

  const state_transition_at_return *
  dyn_cast_state_transition_at_return () const final override { return this; }
};

class state_transition_copy : public state_transition
{
public:
  state_transition_copy (tree src_reg_expr,
			 tree dst_reg_expr)
  : m_src_reg_expr (src_reg_expr),
    m_dst_reg_expr (dst_reg_expr)
  {
    gcc_assert (m_src_reg_expr);
    gcc_assert (printable_expr_p (m_src_reg_expr));

    gcc_assert (m_dst_reg_expr);
    gcc_assert (printable_expr_p (m_dst_reg_expr));
  }

  std::unique_ptr<state_transition>
  clone () const final override;

  void
  dump_to_pp (pretty_printer *pp) const final override;

  enum kind
  get_kind () const final override { return kind::copy; }

  tree m_src_reg_expr;
  tree m_dst_reg_expr;
};

class state_transition_use : public state_transition
{
public:
  state_transition_use (tree src_reg_expr)
  : m_src_reg_expr (src_reg_expr)
  {
  }

  std::unique_ptr<state_transition>
  clone () const final override;

  void
  dump_to_pp (pretty_printer *pp) const final override;

  enum kind
  get_kind () const final override { return kind::use; }

  tree m_src_reg_expr;
};

} // namespace ana

#endif /* GCC_ANALYZER_STATE_TRANSITION_H */
