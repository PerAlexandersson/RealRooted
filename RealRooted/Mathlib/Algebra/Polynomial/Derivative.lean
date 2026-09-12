module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative

public section

namespace Polynomial
variable {R : Type*}

section

variable [Semiring R] {p : R[X]}

/-- The coefficient of `X * p'` at `k` is `k` times the coefficient of `p`
at `k`. -/
lemma coeff_X_mul_derivative (p : R[X]) (k : ℕ) :
    (X * p.derivative).coeff k = (k : R) * p.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    simpa using (Nat.cast_comm (α := R) (k + 1) (p.coeff (k + 1))).symm

end

variable [CommRing R] {p : R[X]}

/-- The coefficient of an affine Euler derivative step. -/
lemma coeff_C_mul_add_affine_mul_derivative
    (p : R[X]) (u v w : R) (k : ℕ) :
    (C u * p + (C v + C w * X) * p.derivative).coeff k =
      (u + w * (k : R)) * p.coeff k +
        v * ((k : R) + 1) * p.coeff (k + 1) := by
  rw [show (C v + C w * X) * p.derivative =
      C v * p.derivative + C w * (X * p.derivative) by ring]
  simp only [coeff_add, coeff_C_mul]
  rw [coeff_derivative, coeff_X_mul_derivative]
  ring

/-- An affine Euler derivative step cannot raise degree. -/
lemma natDegree_C_mul_add_affine_mul_derivative_le
    (p : R[X]) (u v w : R) :
    (C u * p + (C v + C w * X) * p.derivative).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_C_mul_add_affine_mul_derivative]
  have hpk : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt hk
  have hpks : p.coeff (k + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by lia)
  simp [hpk, hpks]

/-- The prospective top coefficient of an affine Euler derivative step. -/
lemma coeff_C_mul_add_affine_mul_derivative_natDegree
    (p : R[X]) (u v w : R) :
    (C u * p + (C v + C w * X) * p.derivative).coeff p.natDegree =
      (u + w * (p.natDegree : R)) * p.leadingCoeff := by
  rw [coeff_C_mul_add_affine_mul_derivative,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self p.natDegree), coeff_natDegree]
  ring

/-- A nonzero prospective top coefficient gives the exact degree and leading
coefficient of an affine Euler derivative step. -/
lemma natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
    (p : R[X]) (u v w : R)
    (htop : (u + w * (p.natDegree : R)) * p.leadingCoeff ≠ 0) :
    let q := C u * p + (C v + C w * X) * p.derivative
    q.natDegree = p.natDegree ∧
      q.leadingCoeff = (u + w * (p.natDegree : R)) * p.leadingCoeff := by
  dsimp only
  have hle := natDegree_C_mul_add_affine_mul_derivative_le p u v w
  have hcoeff := coeff_C_mul_add_affine_mul_derivative_natDegree p u v w
  have hdegree := natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact htop)
  refine ⟨hdegree, ?_⟩
  rw [← coeff_natDegree, hdegree, hcoeff]

/-- The coefficient of `X * (1 - X) * p'` at `k + 1`. -/
lemma coeff_X_sub_X_sq_mul_derivative (p : R[X]) (k : ℕ) :
    ((X - X ^ 2) * p.derivative).coeff (k + 1) =
      ((k : R) + 1) * p.coeff (k + 1) - (k : R) * p.coeff k := by
  rw [show (X - X ^ 2) * p.derivative = X * ((1 - X) * p.derivative) by ring,
    coeff_X_mul]
  rw [sub_mul, coeff_sub, one_mul, coeff_derivative, coeff_X_mul_derivative]
  ring

/-- The coefficient at `k + 1` after multiplying `p'` by a quadratic with no
constant term and `p` by a linear polynomial. -/
lemma coeff_quadratic_derivative_add_linear_mul_succ
    (p : R[X]) (a b c d : R) (k : ℕ) :
    (((C a * X + C b * X ^ 2) * p.derivative +
      (C c + C d * X) * p).coeff (k + 1)) =
      (a * ((k : R) + 1) + c) * p.coeff (k + 1) +
        (b * (k : R) + d) * p.coeff k := by
  rw [show (C a * X + C b * X ^ 2) * p.derivative =
      C a * (X * p.derivative) + C b * (X * (X * p.derivative)) by ring]
  rw [show (C c + C d * X) * p = C c * p + C d * (X * p) by ring]
  simp only [coeff_add, coeff_C_mul]
  rw [coeff_X_mul_derivative, coeff_X_mul, coeff_X_mul_derivative, coeff_X_mul]
  push_cast
  ring

/-- A quadratic-derivative plus linear-multiple step, with a bounded remainder,
has degree at most one more than the input. -/
lemma natDegree_quadratic_derivative_add_linear_mul_add_le
    (p r : R[X]) (a b c d : R) (hr : r.natDegree ≤ p.natDegree) :
    ((C a * X + C b * X ^ 2) * p.derivative +
      (C c + C d * X) * p + r).natDegree ≤ p.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero => lia
  | succ k =>
      have hk : p.natDegree < k := by lia
      have hksucc : p.natDegree < k + 1 := by lia
      have hrzero : r.coeff (k + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr hksucc)
      rw [coeff_add, coeff_quadratic_derivative_add_linear_mul_succ,
        coeff_eq_zero_of_natDegree_lt hk, coeff_eq_zero_of_natDegree_lt hksucc,
        hrzero]
      ring

/-- The prospective top coefficient of a quadratic-derivative plus
linear-multiple step; a bounded remainder does not contribute there. -/
lemma coeff_quadratic_derivative_add_linear_mul_add_natDegree_succ
    (p r : R[X]) (a b c d : R) (hr : r.natDegree ≤ p.natDegree) :
    ((C a * X + C b * X ^ 2) * p.derivative +
      (C c + C d * X) * p + r).coeff (p.natDegree + 1) =
      (b * (p.natDegree : R) + d) * p.leadingCoeff := by
  have hpzero : p.coeff (p.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self p.natDegree)
  have hrzero : r.coeff (p.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr (Nat.lt_succ_self p.natDegree))
  rw [coeff_add, coeff_quadratic_derivative_add_linear_mul_succ, hpzero,
    hrzero, coeff_natDegree]
  ring

/-- A nonzero prospective top coefficient gives both the exact degree and
leading coefficient of a quadratic-derivative plus linear-multiple step. -/
lemma natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
    (p r : R[X]) (a b c d : R) (hr : r.natDegree ≤ p.natDegree)
    (htop : (b * (p.natDegree : R) + d) * p.leadingCoeff ≠ 0) :
    let q := (C a * X + C b * X ^ 2) * p.derivative +
      (C c + C d * X) * p + r
    q.natDegree = p.natDegree + 1 ∧
      q.leadingCoeff = (b * (p.natDegree : R) + d) * p.leadingCoeff := by
  dsimp only
  have hle := natDegree_quadratic_derivative_add_linear_mul_add_le p r a b c d hr
  have hcoeff :=
    coeff_quadratic_derivative_add_linear_mul_add_natDegree_succ p r a b c d hr
  have hcoeff_ne :
      ((C a * X + C b * X ^ 2) * p.derivative +
        (C c + C d * X) * p + r).coeff (p.natDegree + 1) ≠ 0 := by
    rw [hcoeff]
    exact htop
  have hdegree := natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff_ne
  refine ⟨hdegree, ?_⟩
  rw [← coeff_natDegree, hdegree, hcoeff]

/-- Iterating noncancelling quadratic-derivative steps raises the degree once
per step and multiplies the leading coefficient by the prospective top factors. -/
theorem natDegree_and_leadingCoeff_quadratic_derivative_recurrence
    (P r : ℕ → R[X]) (a b c d : ℕ → R)
    (hrec : ∀ n, P (n + 1) =
      (C (a n) * X + C (b n) * X ^ 2) * (P n).derivative +
        (C (c n) + C (d n) * X) * P n + r n)
    (hr : ∀ n, (r n).natDegree ≤ (P n).natDegree)
    (htop : ∀ n, (b n * ((P n).natDegree : R) + d n) * (P n).leadingCoeff ≠ 0)
    (n : ℕ) :
    (P n).natDegree = (P 0).natDegree + n ∧
      (P n).leadingCoeff =
        (Finset.range n).prod (fun k =>
          b k * (((P 0).natDegree + k : ℕ) : R) + d k) * (P 0).leadingCoeff := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
        (P n) (r n) (a n) (b n) (c n) (d n) (hr n) (htop n)
      constructor
      · rw [hrec n, hstep.1, ih.1]
        simp [Nat.add_assoc]
      · rw [hrec n, hstep.2, ih.1, Finset.prod_range_succ, ih.2]
        ring

/-- Over a ring without zero divisors, nonzero scalar top factors and a
nonzero seed give the checkable hypotheses needed for exact recurrence degree
and leading-coefficient propagation. -/
theorem natDegree_and_leadingCoeff_quadratic_derivative_recurrence_of_ne_zero
    [NoZeroDivisors R] (P r : ℕ → R[X]) (a b c d : ℕ → R)
    (hrec : ∀ n, P (n + 1) =
      (C (a n) * X + C (b n) * X ^ 2) * (P n).derivative +
        (C (c n) + C (d n) * X) * P n + r n)
    (hP0 : P 0 ≠ 0)
    (hr : ∀ n, (r n).natDegree ≤ (P 0).natDegree + n)
    (hfactor : ∀ n, b n * (((P 0).natDegree + n : ℕ) : R) + d n ≠ 0)
    (n : ℕ) :
    (P n).natDegree = (P 0).natDegree + n ∧
      (P n).leadingCoeff =
        (Finset.range n).prod (fun k =>
          b k * (((P 0).natDegree + k : ℕ) : R) + d k) * (P 0).leadingCoeff := by
  have hseed : (P 0).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hstrong : ∀ n,
      (P n).natDegree = (P 0).natDegree + n ∧
        (P n).leadingCoeff =
          (Finset.range n).prod (fun k =>
            b k * (((P 0).natDegree + k : ℕ) : R) + d k) * (P 0).leadingCoeff ∧
        (P n).leadingCoeff ≠ 0 := by
    intro m
    induction m with
    | zero => exact ⟨rfl, by simp, hseed⟩
    | succ m ih =>
        have hrm : (r m).natDegree ≤ (P m).natDegree := by
          rw [ih.1]
          exact hr m
        have hfactor_m : b m * ((P m).natDegree : R) + d m ≠ 0 := by
          rw [ih.1]
          exact hfactor m
        have htop :
            (b m * ((P m).natDegree : R) + d m) * (P m).leadingCoeff ≠ 0 :=
          mul_ne_zero hfactor_m ih.2.2
        have hstep :=
          natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
            (P m) (r m) (a m) (b m) (c m) (d m) hrm htop
        constructor
        · rw [hrec m, hstep.1, ih.1]
          simp [Nat.add_assoc]
        constructor
        · rw [hrec m, hstep.2, ih.1, Finset.prod_range_succ, ih.2.1]
          ring
        · rw [hrec m, hstep.2]
          exact htop
  exact ⟨(hstrong n).1, (hstrong n).2.1⟩

section AddTorsionFree

variable [IsAddTorsionFree R]

/-- The next coefficient of the derivative is `(n - 1)` times the next
coefficient of the original polynomial, for degree `n ≥ 2`. -/
lemma nextCoeff_derivative_of_two_le_natDegree (p : R[X])
    (htwo : 2 ≤ p.natDegree) :
    p.derivative.nextCoeff = (p.natDegree - 1 : R) * p.nextCoeff := by
  have hpder_deg : p.derivative.natDegree = p.natDegree - 1 :=
    p.natDegree_derivative
  rw [Polynomial.nextCoeff_of_natDegree_pos, hpder_deg]
  · rw [Polynomial.nextCoeff_of_natDegree_pos (by lia)]
    rw [coeff_derivative]
    have hidx : p.natDegree - 1 - 1 + 1 = p.natDegree - 1 := by lia
    have hcast : ((p.natDegree - 1 - 1 : ℕ) : R) + 1 =
        (p.natDegree - 1 : R) := by
      rw [Nat.cast_sub (by show 1 ≤ p.natDegree - 1; lia),
        Nat.cast_sub (by show 1 ≤ p.natDegree; lia)]
      ring
    grind
  · grind

variable {S : Type*} [Field S] [LinearOrder S] [IsStrictOrderedRing S]

/-- A nonresonant first-order Euler equation inherits the degree bound of its
remainder.  The coarse bound rules out the homogeneous solution of degree
`a`. -/
theorem natDegree_le_of_C_mul_eq_X_add_C_mul_derivative_add
    (p q : S[X]) (a b d N : ℕ)
    (hp : p ≠ 0) (hcoarse : p.natDegree ≤ N) (hN : N < a)
    (hq : q.natDegree ≤ d)
    (hrec : C (a : S) * p = (X + C (b : S)) * p.derivative + q) :
    p.natDegree ≤ d := by
  by_contra hdegree
  have hdlt : d < p.natDegree := by lia
  let k := p.natDegree
  let j := k - 1
  have hkpos : 0 < k := by dsimp [k]; lia
  have hkj : k = j + 1 := by dsimp [j]; lia
  have hqzero : q.coeff (j + 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [← hkj]
    exact lt_of_le_of_lt hq (by simpa [k] using hdlt)
  have hnext : p.coeff (j + 2) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    change k < j + 2
    lia
  have htop : p.coeff k ≠ 0 := by
    change p.leadingCoeff ≠ 0
    exact leadingCoeff_ne_zero.mpr hp
  rw [show (X + C (b : S)) * p.derivative =
      X * p.derivative + C (b : S) * p.derivative by ring] at hrec
  have hcoeff := congrArg (fun r : S[X] => r.coeff (j + 1)) hrec
  rw [coeff_C_mul, coeff_add, coeff_add, coeff_X_mul, coeff_C_mul,
    coeff_derivative, coeff_derivative, hnext, hqzero] at hcoeff
  simp only [add_zero] at hcoeff
  have hfactor : ((a : S) - k) * p.coeff k = 0 := by
    rw [hkj]
    push_cast
    linarith
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · have hklt : k < a := lt_of_le_of_lt hcoarse hN
    have hkltS : (k : S) < (a : S) := by exact_mod_cast hklt
    exact (ne_of_gt (sub_pos.mpr hkltS)) hzero
  · exact htop hzero

end AddTorsionFree

end Polynomial
