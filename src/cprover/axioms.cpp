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
#include <util/pointer_predicates.h>

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
      if(a_it->state() != b_it->state())
        continue;
      auto a_op = a_it->address();
      auto b_op = typecast_exprt::conditional_cast(
        b_it->address(), a_it->address().type());
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
    src.id() == ID_state_object_size || src.id() == ID_state_live_object ||
    src.id() == ID_state_r_ok || src.id() == ID_state_w_ok ||
    src.id() == ID_state_rw_ok)
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
    auto &is_cstring_expr = to_state_is_cstring_expr(src);
    is_cstring_exprs.insert(is_cstring_expr);

    {
      // is_cstring(ς, p) ⇒ r_ok(ς, p, 1)
      auto ok_expr = ternary_exprt(
        ID_state_r_ok,
        is_cstring_expr.state(),
        is_cstring_expr.address(),
        from_integer(1, size_type()),
        bool_typet());

      auto instance1 = replace(implies_exprt(src, ok_expr));
      std::cout << "AXIOMa1: " << format(instance1) << "\n";
      dest << instance1;

      auto ok_simplified = simplify_state_expr(ok_expr, address_taken, ns);
      ok_simplified.visit_pre(
        [&dest, this](const exprt &src) { node(src, dest); });
      auto instance2 = replace(implies_exprt(src, ok_simplified));
      std::cout << "AXIOMa2: " << format(instance2) << "\n";
      dest << instance2;
    }

    {
      // is_cstring(ς, p) --> is_cstring(ς, p + 1) ∨ ς(p)=0
      auto state = is_cstring_expr.state();
      auto p = is_cstring_expr.address();
      auto one = from_integer(1, signed_size_type());
      auto p_plus_one = plus_exprt(p, one, is_cstring_expr.op1().type());
      auto is_cstring_plus_one = state_is_cstring_exprt(state, p_plus_one);
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
  else if(src.id() == ID_state_live_object)
  {
    const auto &live_object_expr = to_state_live_object_expr(src);
    live_object_exprs.insert(live_object_expr);

    {
      // live_object(ς, p) --> p!=0
      auto instance = replace(
        implies_exprt(src, not_exprt(null_pointer(live_object_expr.address()))));
      std::cout << "AXIOMc: " << format(instance) << "\n";
      dest << instance;
    }
  }
  else if(src.id() == ID_state_object_size)
  {
    const auto &object_size_expr = to_state_object_size_expr(src);
    object_size_exprs.insert(object_size_expr);
  }
  else if(
    src.id() == ID_state_r_ok || src.id() == ID_state_w_ok ||
    src.id() == ID_state_rw_ok)
  {
    const auto &ok_expr = to_ternary_expr(src);
    const auto &state = ok_expr.op0();
    const auto &pointer = ok_expr.op1();
    const auto &size = ok_expr.op2();

    // X_ok(p, s)
    //  --> live_object(p) ∧ offset(p)≥0 ∧ offset(p)+s≤object_size(p)
    auto live_object =
      binary_predicate_exprt(state, ID_state_live_object, pointer);
    auto ssize_type = signed_size_type();
    auto offset = pointer_offset_exprt(pointer, ssize_type);
    auto offset_simplified =
      simplify_state_expr_node(offset, address_taken, ns);
    auto lower = binary_relation_exprt(
      offset_simplified, ID_ge, from_integer(0, ssize_type));
    auto object_size =
      binary_exprt(state, ID_state_object_size, pointer, ssize_type);
    auto size_casted = typecast_exprt::conditional_cast(size, ssize_type);
    auto upper = binary_relation_exprt(
      plus_exprt(offset_simplified, size_casted), ID_le, object_size);

    auto instance =
      replace(implies_exprt(src, and_exprt(live_object, lower, upper)));
    std::cout << "AXIOMd: " << format(instance) << "\n";
    dest << instance;
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
