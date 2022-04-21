/*******************************************************************\

Module: Simplify State Expressions

Author:

\*******************************************************************/

/// \file
/// Simplify State Expressions

#include "simplify_state_expr.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "may_alias.h"
#include "state.h"

#include <iostream>

std::size_t allocate_counter = 0;

exprt simplify_state_expr_node(
  exprt,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

exprt simplify_evaluate_update(
  evaluate_exprt evaluate_expr,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_update_state);

  const auto &update_state_expr = to_update_state_expr(evaluate_expr.state());

  auto may_alias = ::may_alias(
    evaluate_expr.address(), update_state_expr.address(), address_taken, ns);

  if(may_alias.has_value())
  {
    // 'simple' case
    if(may_alias->is_true())
    {
      // The object is known to be the same.
      // (ς[A:=V])(A) --> V
      return typecast_exprt::conditional_cast(
        update_state_expr.new_value(), evaluate_expr.type());
    }
    else if(may_alias->is_false())
    {
      // The object is known to be different.
      // (ς[❝x❞:=V])(❝y❞) --> ς(❝y❞)
      auto new_evaluate_expr = evaluate_expr;
      new_evaluate_expr.state() = update_state_expr.state();
      return std::move(new_evaluate_expr);
    }
    else
    {
      // The object may or may not be the same.
      // (ς[A:=V])(B) --> if cond then V else ς(B) endif
      auto new_evaluate_expr = evaluate_expr;
      new_evaluate_expr.state() = update_state_expr.state();
      return if_exprt(
        std::move(*may_alias),
        typecast_exprt::conditional_cast(
          update_state_expr.new_value(), evaluate_expr.type()),
        std::move(new_evaluate_expr));
    }
  }

  // Complex case.
  auto same_object =
    ::same_object(evaluate_expr.address(), update_state_expr.address());
  auto object = update_state_expr.new_value();
  auto offset = simplify_state_expr_node(
    pointer_offset(evaluate_expr.address()), address_taken, ns);
  auto byte_extract = make_byte_extract(object, offset, evaluate_expr.type());
  auto new_evaluate_expr = evaluate_expr;
  new_evaluate_expr.state() = update_state_expr.state();
  return if_exprt(
    std::move(same_object),
    std::move(byte_extract),
    std::move(new_evaluate_expr));
}

exprt simplify_evaluate_allocate(
  evaluate_exprt evaluate_expr,
  const namespacet &ns)
{
  PRECONDITION(evaluate_expr.state().id() == ID_allocate);

  const auto &allocate_expr = to_allocate_expr(evaluate_expr.state());

  // Same address?
  if(evaluate_expr.address() == allocate_expr.address())
  {
    irep_idt identifier = "allocate-" + std::to_string(++allocate_counter);
    auto object_size = allocate_expr.size();
    auto object_type = array_typet(char_type(), object_size);
    auto symbol_expr = symbol_exprt(identifier, object_type);
    return object_address_exprt(symbol_expr);
  }
  else // different
  {
    auto new_evaluate_expr = evaluate_expr;
    new_evaluate_expr.state() = allocate_expr.state();
    return std::move(new_evaluate_expr);
  }
}

exprt simplify_object_expression_rec(exprt src)
{
  if(src.id() == ID_object_address)
    return src;
  else if(src.id() == ID_element_address)
    return simplify_object_expression_rec(to_element_address_expr(src).base());
  else if(src.id() == ID_plus)
  {
    const auto &plus_expr = to_plus_expr(src);
    for(auto &op : plus_expr.operands())
      if(op.type().id() == ID_pointer)
        return simplify_object_expression_rec(op);
    return src; // no change
  }
  else
    return src;
}

exprt simplify_object_expression(exprt src)
{
  return simplify_object_expression_rec(src);
}

exprt simplify_live_object_expr(binary_exprt src, const namespacet &ns)
{
  const auto &pointer = src.op1();

  auto object = simplify_object_expression(pointer);

  if(object.id() == ID_object_address)
  {
    const auto &symbol =
      ns.lookup(to_object_address_expr(object).object_identifier());
    if(symbol.is_static_lifetime)
    {
      return true_exprt(); // always live
    }
    else
    {
      // might be 'dead'
      return true_exprt();
    }
  }

  // A store does not affect the result.
  // live_object(ς[A:=V]), p) --> live_object(ς, p)
  if(src.op0().id() == ID_update_state)
  {
    src.op0() = to_update_state_expr(src.op0()).state();
    return std::move(src);
  }

  return std::move(src);
}

exprt simplify_object_size_expr(binary_exprt src, const namespacet &ns)
{
  const auto &pointer = src.op1();

  auto object = simplify_object_expression(pointer);

  if(object.id() == ID_object_address)
  {
    const auto &symbol =
      ns.lookup(to_object_address_expr(object).object_identifier());
    auto size_opt = size_of_expr(symbol.type, ns);
    if(size_opt.has_value())
      return typecast_exprt::conditional_cast(*size_opt, src.type());
    else
      return src; // no change
  }

  // A store does not affect the result.
  // object_size(ς[A:=V]), p) --> object_size(ς, p)
  if(src.op0().id() == ID_update_state)
  {
    src.op0() = to_update_state_expr(src.op0()).state();
    return std::move(src);
  }

  return std::move(src);
}

exprt simplify_ok_expr(
  ternary_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  const auto &state = src.op0();
  const auto &pointer = src.op1();
  const auto &size = src.op2();

  // rewrite X_ok(p, s)
  //  --> live_object(p) ∧ offset(p)≥0 ∧ offset(p)+s≤object_size(p)
  auto live_object =
    binary_predicate_exprt(state, ID_state_live_object, pointer);
  auto live_object_simplified =
    simplify_state_expr_node(live_object, address_taken, ns);
  auto ssize_type = signed_size_type();
  auto offset = pointer_offset_exprt(pointer, ssize_type);
  auto offset_simplified = simplify_state_expr_node(offset, address_taken, ns);
  auto lower = binary_relation_exprt(
    offset_simplified, ID_ge, from_integer(0, ssize_type));
  auto object_size =
    binary_exprt(state, ID_state_object_size, pointer, ssize_type);
  auto object_size_simplified =
    simplify_state_expr_node(object_size, address_taken, ns);
  auto size_casted = typecast_exprt::conditional_cast(size, ssize_type);
  auto upper = binary_relation_exprt(
    plus_exprt(offset_simplified, size_casted), ID_le, object_size_simplified);

  return and_exprt(live_object_simplified, lower, upper);

#if 0
  // A store does not affect the result.
  // X_ok(ς[A:=V]), A, S) --> X_ok(ς, A, S)
  if(src.op0().id() == ID_update_state)
  {
    src.op0() = to_update_state_expr(src.op0()).state();
    return std::move(src);
  }

  return src;
#endif
}

#if 0
static bool is_one(const exprt &src)
{
  if(src.id() == ID_typecast)
    return is_one(to_typecast_expr(src).op());
  else if(src.id() == ID_constant)
  {
    auto value_opt = numeric_cast<mp_integer>(src);
    return value_opt.has_value() && *value_opt == 1;
  }
  else
    return false;
}
#endif

exprt simplify_is_cstring_expr(
  binary_exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  PRECONDITION(src.type().id() == ID_bool);
  const auto &state = src.op0();
  const auto &pointer = src.op1();

  if(state.id() == ID_update_state)
  {
    const auto &update_state_expr = to_update_state_expr(state);

    auto cstring_in_old_state = src;
    cstring_in_old_state.op0() = update_state_expr.state();
    auto simplified_cstring_in_old_state =
      simplify_state_expr_node(cstring_in_old_state, address_taken, ns);

    auto may_alias =
      ::may_alias(pointer, update_state_expr.address(), address_taken, ns);

    if(may_alias.has_value() && may_alias->is_false())
    {
      // different objects
      // cstring(s[x:=v], p) --> cstring(s, p)
      return simplified_cstring_in_old_state;
    }

    // maybe the same

    // Are we writing zero?
    if(update_state_expr.new_value().is_zero())
    {
      // cstring(s[p:=0], q) --> if p alias q then true else cstring(s, q)
      return if_exprt(
        same_object(pointer, update_state_expr.address()),
        true_exprt(),
        simplified_cstring_in_old_state);
    }
  }

  if(pointer.id() == ID_plus)
  {
#if 0
    auto &plus_expr = to_plus_expr(pointer);
    if(plus_expr.operands().size() == 2 && is_one(plus_expr.op1()))
    {
      // is_cstring(ς, p + 1)) --> is_cstring(ς, p) ∨ ς(p)=0
      auto new_is_cstring = src;
      new_is_cstring.op1() = plus_expr.op0();
      auto type = to_pointer_type(pointer.type()).base_type();
      auto zero = from_integer(0, type);
      auto is_zero =
        equal_exprt(evaluate_exprt(state, plus_expr.op0(), type), zero);
      return or_exprt(new_is_cstring, is_zero);
    }
#endif
  }
  else if(
    pointer.id() == ID_address_of &&
    to_address_of_expr(pointer).object().id() == ID_string_constant)
  {
    // is_cstring(ς, &"...")) --> true
    return true_exprt();
  }
  else if(
    pointer.id() == ID_element_address &&
    to_element_address_expr(pointer).base().id() == ID_address_of &&
    to_address_of_expr(to_element_address_expr(pointer).base()).object().id() ==
      ID_string_constant)
  {
    // TODO: compare offset to length
    // is_cstring(ς, element_address(&"...", 0))) --> true
    return true_exprt();
  }

  return std::move(src);
}

exprt simplify_state_expr_node(
  exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_evaluate_expr(src);

    if(evaluate_expr.state().id() == ID_update_state)
    {
      return simplify_evaluate_update(evaluate_expr, address_taken, ns);
    }
    else if(evaluate_expr.state().id() == ID_allocate)
    {
      return simplify_evaluate_allocate(evaluate_expr, ns);
    }
  }
  else if(
    src.id() == ID_state_r_ok || src.id() == ID_state_w_ok ||
    src.id() == ID_state_rw_ok)
  {
    return simplify_ok_expr(to_ternary_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_state_live_object)
  {
    return simplify_live_object_expr(to_binary_expr(src), ns);
  }
  else if(src.id() == ID_state_is_cstring)
  {
    return simplify_is_cstring_expr(to_binary_expr(src), address_taken, ns);
  }
  else if(src.id() == ID_plus)
  {
    auto &plus_expr = to_plus_expr(src);
    if(
      src.type().id() == ID_pointer &&
      plus_expr.op0().id() == ID_element_address)
    {
      // element_address(X, Y) + Z --> element_address(X, Y + Z)
      auto new_element_address_expr = to_element_address_expr(plus_expr.op0());
      new_element_address_expr.index() = plus_exprt(
        new_element_address_expr.index(),
        typecast_exprt::conditional_cast(
          plus_expr.op1(), new_element_address_expr.index().type()));
      new_element_address_expr.index() =
        simplify_expr(new_element_address_expr.index(), ns);
      return std::move(new_element_address_expr);
    }
  }
  else if(src.id() == ID_pointer_offset)
  {
    auto &pointer_offset_expr = to_pointer_offset_expr(src);

    // pointer_offset(❝x❞) -> 0
    if(pointer_offset_expr.pointer().id() == ID_object_address)
    {
      return from_integer(0, pointer_offset_expr.type());
    }
  }
  else if(src.id() == ID_state_object_size)
  {
    return simplify_object_size_expr(to_binary_expr(src), ns);
  }
  else if(src.id() == ID_equal)
  {
    const auto &equal_expr = to_equal_expr(src);
    if(
      equal_expr.lhs().id() == ID_pointer_object &&
      equal_expr.rhs().id() == ID_pointer_object)
    {
      const auto &lhs_p = to_pointer_object_expr(equal_expr.lhs()).pointer();
      const auto &rhs_p = to_pointer_object_expr(equal_expr.rhs()).pointer();
      if(lhs_p.id() == ID_object_address && rhs_p.id() == ID_object_address)
      {
        if(
          to_object_address_expr(lhs_p).object_identifier() ==
          to_object_address_expr(rhs_p).object_identifier())
          return true_exprt();
        else
          return false_exprt();
      }
    }
  }

  return src;
}

exprt simplify_state_expr(
  exprt src,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &ns)
{
  // operands first, recursively
  for(auto &op : src.operands())
    op = simplify_state_expr(op, address_taken, ns);

  // now the node itself
  src = simplify_state_expr_node(src, address_taken, ns);

  return src;
}
