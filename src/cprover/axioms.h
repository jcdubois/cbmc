/*******************************************************************\

Module: Axioms

Author:

\*******************************************************************/

/// \file
/// Axioms

#ifndef CPROVER_CPROVER_AXIOMS_H
#define CPROVER_CPROVER_AXIOMS_H

#include <util/std_expr.h>

#include <solvers/decision_procedure.h>

#include "state.h"

#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

class axiomst
{
public:
  axiomst(
    const std::unordered_set<symbol_exprt, irep_hash> &__address_taken,
    const namespacet &__ns)
    : address_taken(__address_taken), ns(__ns)
  {
  }

  void set_to_true(exprt);
  void set_to_false(exprt);
  void emit(decision_proceduret &);

protected:
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken;
  const namespacet &ns;

  std::vector<exprt> constraints;

  exprt replace(exprt);
  typet replace(typet);
  std::unordered_map<exprt, symbol_exprt, irep_hash> replacement_map;
  std::map<irep_idt, std::size_t> counters;

  void node(const exprt &, decision_proceduret &);

  std::set<evaluate_exprt> evaluate_exprs;
  void evaluate(decision_proceduret &);

  std::set<binary_exprt> is_cstring_exprs;
  void is_cstring(decision_proceduret &);
};

static inline axiomst &operator<<(axiomst &axioms, exprt src)
{
  axioms.set_to_true(std::move(src));
  return axioms;
}

#endif // CPROVER_CPROVER_AXIOMS_H
