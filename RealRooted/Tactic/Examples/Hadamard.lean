import RealRooted.Tactic.Hadamard

open Polynomial

namespace RealRooted
namespace Tactic

example {f g p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hfg : Interl f g) (hpq : Interl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  rr_hadamard_pf_interl

example {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Interl f g) :
    Interl (hadamardProduct f p) (hadamardProduct g p) := by
  rr_hadamard_pf_interl

example {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    Interl (hadamardProduct f p) (hadamardProduct f q) := by
  rr_hadamard_pf_interl

example {F G P Q : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hG : ∀ i : Nat, IsPFPolynomial (G i))
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hFG : ∀ i : Nat, Interl (F i) (G i))
    (hPQ : ∀ i : Nat, Interl (P i) (Q i)) :
    ∀ n : Nat,
      Interl (hadamardProduct (F n) (P n)) (hadamardProduct (G n) (Q n)) := by
  intro n
  rr_hadamard_pf_interl
end Tactic
end RealRooted

