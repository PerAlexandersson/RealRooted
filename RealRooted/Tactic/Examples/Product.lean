module

public import RealRooted.Tactic.Examples.Product.Basic
public import RealRooted.Tactic.Examples.Product.DispatchIsolation
public import RealRooted.Tactic.Examples.Product.EndpointPair
public import RealRooted.Tactic.Examples.Product.Families
public import RealRooted.Tactic.Examples.Product.Interlacing
public import RealRooted.Tactic.Examples.Product.Lifts
public import RealRooted.Tactic.Examples.Product.UnsupportedShape
public import RealRooted.Tactic.Product

/-!
# `rr_product_factor` examples

Regression tests for OEIS recurrences where `P_n` is a real linear factor
times `P_{n-1}`.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
