/* Paths within an exploded_graph.
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

#ifndef GCC_ANALYZER_EXPLODED_PATH_H
#define GCC_ANALYZER_EXPLODED_PATH_H

#include "analyzer/exploded-graph.h"
#include "analyzer/checker-event.h"
#include "analyzer/state-transition.h"

namespace ana {

/* A path within an exploded_graph: a sequence of edges.  */

class exploded_path
{
public:
  struct element_t
  {
    element_t (const exploded_edge *eedge)
    : m_eedge (eedge)
    {
    }
    element_t (const element_t &other)
    : m_eedge (other.m_eedge),
      m_state_at_src (other.m_state_at_src),
      m_state_at_dst (other.m_state_at_dst),
      m_state_transition (nullptr)
    {
      if (other.m_state_transition)
	m_state_transition = other.m_state_transition->clone ();
    }

    element_t (element_t &&other) = default;

    element_t &operator= (const element_t &other)
    {
      m_eedge = other.m_eedge;
      m_state_at_src = other.m_state_at_src;
      m_state_at_dst = other.m_state_at_dst;
      m_state_transition = (other.m_state_transition
			    ? other.m_state_transition->clone ()
			    : nullptr);
      return *this;
    }

    const exploded_edge *m_eedge;
    diagnostic_state m_state_at_src;
    diagnostic_state m_state_at_dst;
    std::unique_ptr<state_transition> m_state_transition;
  };

  exploded_path () = default;
  exploded_path (const exploded_path &other) = default;

  unsigned length () const { return m_elements.size (); }

  bool find_stmt_backwards (const gimple *search_stmt,
			    int *out_idx) const;

  exploded_node *get_final_enode () const;

  void dump_to_pp (pretty_printer *pp,
		   const extrinsic_state *ext_state) const;
  void dump (FILE *fp, const extrinsic_state *ext_state) const;
  void dump (const extrinsic_state *ext_state = nullptr) const;
  void dump_to_file (const char *filename,
		     const extrinsic_state &ext_state) const;

  void maybe_log (logger *logger, const char *desc) const;

  bool feasible_p (logger *logger, std::unique_ptr<feasibility_problem> *out,
		    engine *eng, const exploded_graph *eg) const;

  void
  append_edge (const exploded_edge *edge)
  {
    m_elements.push_back (edge);
  }

  void
  reverse ();

  std::vector<element_t> m_elements;
};

/* Finding the shortest exploded_path within an exploded_graph.  */

typedef shortest_paths<eg_traits, exploded_path> shortest_exploded_paths;

} // namespace ana

#endif /* GCC_ANALYZER_EXPLODED_PATH_H */
