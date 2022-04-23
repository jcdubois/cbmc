/*******************************************************************\

Module: Axioms

Author:

\*******************************************************************/

/// \file
/// Axioms

#include "axioms.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/format_expr.h>

#include "simplify_state_expr.h"
#include "state.h"

#include <iostream>

void axiomst::set_to_true(exprt src)
{
  constraints.push_back(std::move(src));
}

void axiomst::set_to_false(exprt src)
{
  set_to_true(not_exprt(src));
}

typet axiomst::replace(typet src)
{
  if(src.id() == ID_array)
  {
    auto &array_type = to_array_type(src);
    array_type.element_type() = replace(array_type.element_type());
    array_type.size() = replace(array_type.size());
    return src;
  }
  else if(src.id() == ID_pointer)
  {
    to_pointer_type(src).base_type() =
      replace(to_pointer_type(src).base_type());
    return src;
  }
  else
    return src;
}

void axiomst::evaluate(decision_proceduret &dest)
{
  // quadratic
  for(auto a_it = evaluate_exprs.begin(); a_it != evaluate_exprs.end(); a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != evaluate_exprs.end(); b_it++)
    {
      if(a_it->state() != b_it->state())
        continue;

      auto a_op = a_it->address();
      auto b_op = typecast_exprt::conditional_cast(
        b_it->address(), a_it->address().type());
      auto operands_equal = equal_exprt(a_op, b_op);
      auto implication = implies_exprt(
        operands_equal,
        equal_exprt(
          *a_it, typecast_exprt::conditional_cast(*b_it, a_it->type())));
      std::cout << "EVALUATE: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

void axiomst::is_cstring(decision_proceduret &dest)
{
  // quadratic
  for(auto a_it = is_cstring_exprs.begin(); a_it != is_cstring_exprs.end();
      a_it++)
  {
    for(auto b_it = std::next(a_it); b_it != is_cstring_exprs.end(); b_it++)
    {
      if(a_it->op0() != b_it->op0())
        continue;
      auto a_op = a_it->op1();
      auto b_op =
        typecast_exprt::conditional_cast(b_it->op1(), a_it->op1().type());
      auto operands_equal = equal_exprt(a_op, b_op);
      auto implication =
        implies_exprt(operands_equal, equal_exprt(*a_it, *b_it));
      std::cout << "IS_CSTRING: " << format(implication) << '\n';
      dest << replace(implication);
    }
  }
}

exprt axiomst::replace(exprt src)
{
  src.type() = replace(src.type());

  if(
    src.id() == ID_evaluate || src.id() == ID_state_is_cstring ||
    src.id() == ID_state_object_size || src.id() == ID_state_live_object)
  {
    auto r = replacement_map.find(src);
    if(r == replacement_map.end())
    {
      auto counter = ++counters[src.id()];
      auto s =
        symbol_exprt(src.id_string() + std::to_string(counter), src.type());
      replacement_map.emplace(src, s);

      if(src.id() == ID_state_is_cstring)
      {
        std::cout << "R " << format(s) << " --> " << format(src) << '\n';
      }
      return s;
    }
    else
      return r->second;
  }

  for(auto &op : src.operands())
    op = replace(op);

  return src;
}

void axiomst::node(const exprt &src, decision_proceduret &dest)
{
  if(src.id() == ID_state_is_cstring)
  {
    auto &is_cstring_expr = to_binary_expr(src);
    is_cstring_exprs.insert(is_cstring_expr);

    {
      // is_cstring(ς, p) ⇒ r_ok(ς, p, 1)
      auto ok_expr = ternary_exprt(
        ID_state_r_ok,
        is_cstring_expr.op0(),
        is_cstring_expr.op1(),
        from_integer(1, size_type()),
        bool_typet());
      auto instance = replace(
        implies_exprt(src, simplify_state_expr(ok_expr, address_taken, ns)));
      std::cout << "AXIOMa: " << format(instance) << "\n";
      dest << instance;
    }

    {
      // is_cstring(ς, p) --> is_cstring(ς, p + 1) ∨ ς(p)=0
      auto state = is_cstring_expr.op0();
      auto p = is_cstring_expr.op1();
      auto one = from_integer(1, signed_size_type());
      auto p_plus_one = plus_exprt(p, one, is_cstring_expr.op1().type());
      auto is_cstring_plus_one =
        binary_exprt(state, ID_state_is_cstring, p_plus_one, bool_typet());
      auto char_type = to_pointer_type(p.type()).base_type();
      auto zero = from_integer(0, char_type);
      auto star_p = evaluate_exprt(state, p, char_type);
      auto is_zero = equal_exprt(star_p, zero);
      auto instance =
        replace(implies_exprt(src, or_exprt(is_cstring_plus_one, is_zero)));
      std::cout << "AXIOMb: " << format(instance) << "\n";
      dest << instance;
      evaluate_exprs.insert(star_p);
      is_cstring_exprs.insert(is_cstring_plus_one);
    }
  }
  else if(src.id() == ID_evaluate)
  {
    const auto &evaluate_expr = to_evaluate_expr(src);
    evaluate_exprs.insert(evaluate_expr);
  }
}

void axiomst::emit(decision_proceduret &dest)
{
  for(auto &constraint : constraints)
  {
    constraint.visit_pre([&dest, this](const exprt &src) { node(src, dest); });

    auto constraint_replaced = replace(constraint);
    std::cout << "CONSTRAINT: " << format(constraint_replaced) << "\n";
    dest << constraint_replaced;
  }

  evaluate(dest);
  is_cstring(dest);
}
