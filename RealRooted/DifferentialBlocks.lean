import RealRooted.LiebSokalOperator

/-!
# Differential operators on disjoint variable blocks

Constant-coefficient differential actions compose under multiplication and
factor across disjoint finite variable blocks.
-/

open BigOperators

namespace RealRooted

noncomputable section

private theorem pderiv_comm
    {R sigma : Type*} [CommSemiring R] (i j : sigma)
    (P : MvPolynomial sigma R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      simp only [MvPolynomial.pderiv_monomial]
      by_cases hij : i = j
      · subst j
        rfl
      · have hji : j ≠ i := Ne.symm hij
        have hsub :
            (d - Finsupp.single j 1) - Finsupp.single i 1 =
              (d - Finsupp.single i 1) - Finsupp.single j 1 := by
          ext k
          by_cases hki : k = i <;> by_cases hkj : k = j <;>
            simp_all
        rw [hsub]
        congr 1
        simp [hij, hji]
        ring
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]

private theorem pderiv_iteratedPDerivAt_comm
    {R sigma : Type*} [CommSemiring R] (i j : sigma) (n : ℕ)
    (P : MvPolynomial sigma R) :
    MvPolynomial.pderiv i (iteratedPDerivAt j n P) =
      iteratedPDerivAt j n (MvPolynomial.pderiv i P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPDerivAt]
      rw [pderiv_comm, ih]

private theorem iteratedPDerivAt_comm
    {R sigma : Type*} [CommSemiring R] (i j : sigma) (m n : ℕ)
    (P : MvPolynomial sigma R) :
    iteratedPDerivAt i m (iteratedPDerivAt j n P) =
      iteratedPDerivAt j n (iteratedPDerivAt i m P) := by
  induction m generalizing P with
  | zero => rfl
  | succ m ih =>
      simp only [iteratedPDerivAt]
      rw [ih, pderiv_iteratedPDerivAt_comm]

private theorem iteratedPDerivAt_add_nat
    {R sigma : Type*} [CommSemiring R] (i : sigma) (m n : ℕ)
    (P : MvPolynomial sigma R) :
    iteratedPDerivAt i (m + n) P =
      iteratedPDerivAt i m (iteratedPDerivAt i n P) := by
  induction m with
  | zero => simp only [Nat.zero_add, iteratedPDerivAt]
  | succ m ih =>
      simp only [Nat.succ_add, iteratedPDerivAt]
      rw [ih]

private theorem applyMonomialDifferentialAlong_pderiv_comm
    {R sigma : Type*} [CommSemiring R]
    (l : List sigma) (d : sigma →₀ ℕ) (i : sigma)
    (P : MvPolynomial sigma R) :
    applyMonomialDifferentialAlong l d (MvPolynomial.pderiv i P) =
      MvPolynomial.pderiv i (applyMonomialDifferentialAlong l d P) := by
  induction l generalizing P with
  | nil => rfl
  | cons j l ih =>
      change applyMonomialDifferentialAlong l d
          (iteratedPDerivAt j (d j) (MvPolynomial.pderiv i P)) = _
      rw [← pderiv_iteratedPDerivAt_comm i j (d j) P, ih]
      rfl

private theorem applyMonomialDifferentialAlong_iterated_comm
    {R sigma : Type*} [CommSemiring R]
    (l : List sigma) (d : sigma →₀ ℕ) (i : sigma) (n : ℕ)
    (P : MvPolynomial sigma R) :
    applyMonomialDifferentialAlong l d (iteratedPDerivAt i n P) =
      iteratedPDerivAt i n (applyMonomialDifferentialAlong l d P) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPDerivAt]
      rw [applyMonomialDifferentialAlong_pderiv_comm, ih]

private theorem applyMonomialDifferentialAlong_add
    {R sigma : Type*} [CommSemiring R]
    (l : List sigma) (d e : sigma →₀ ℕ)
    (P : MvPolynomial sigma R) :
    applyMonomialDifferentialAlong l (d + e) P =
      applyMonomialDifferentialAlong l d
        (applyMonomialDifferentialAlong l e P) := by
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      change applyMonomialDifferentialAlong l (d + e)
          (iteratedPDerivAt i ((d + e) i) P) = _
      rw [Finsupp.add_apply, iteratedPDerivAt_add_nat, ih]
      change applyMonomialDifferentialAlong l d
          (applyMonomialDifferentialAlong l e
            (iteratedPDerivAt i (d i) (iteratedPDerivAt i (e i) P))) = _
      rw [applyMonomialDifferentialAlong_iterated_comm]
      rfl

/-- Differential monomials compose by adding their exponent vectors. -/
theorem applyMonomialDifferential_comp
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (d e : sigma →₀ ℕ) (P : MvPolynomial sigma R) :
    applyMonomialDifferential (d + e) P =
      applyMonomialDifferential d (applyMonomialDifferential e P) := by
  exact applyMonomialDifferentialAlong_add
    (differentialVariableOrder sigma) d e P

private theorem finsupp_totalDegree_add
    {sigma : Type*} (d e : sigma →₀ ℕ) :
    (d + e).sum (fun _ n ↦ n) =
      d.sum (fun _ n ↦ n) + e.sum (fun _ n ↦ n) := by
  classical
  apply Finsupp.sum_add_index' <;> simp

private theorem applyNegDifferential_monomial_mul_monomial
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (d e : sigma →₀ ℕ) (c a : R) (G : MvPolynomial sigma R) :
    applyNegDifferential
        (MvPolynomial.monomial d c * MvPolynomial.monomial e a) G =
      applyNegDifferential (MvPolynomial.monomial d c)
        (applyNegDifferential (MvPolynomial.monomial e a) G) := by
  rw [MvPolynomial.monomial_mul, applyNegDifferential_monomial,
    applyNegDifferential_monomial, applyNegDifferential_monomial,
    finsupp_totalDegree_add, pow_add,
    applyMonomialDifferential_comp,
    applyMonomialDifferential_C_mul]
  simp only [map_mul]
  ring

/-- Multiplication of symbols is composition of their constant-coefficient
differential actions. -/
theorem applyNegDifferential_mul
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (F H G : MvPolynomial sigma R) :
    applyNegDifferential (F * H) G =
      applyNegDifferential F (applyNegDifferential H G) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
      induction H using MvPolynomial.induction_on' with
      | monomial e a =>
          exact applyNegDifferential_monomial_mul_monomial d e c a G
      | add H K hH hK =>
          rw [mul_add, applyNegDifferential_add_left,
            applyNegDifferential_add_left, applyNegDifferential_add_right,
            hH, hK]
  | add F K hF hK =>
      rw [add_mul, applyNegDifferential_add_left,
        applyNegDifferential_add_left, hF, hK]

private theorem applyMonomialDifferential_single_nat
    {R sigma : Type*} [CommSemiring R] [Fintype sigma]
    (i : sigma) (n : ℕ) (P : MvPolynomial sigma R) :
    applyMonomialDifferential (Finsupp.single i n) P =
      iteratedPDerivAt i n P := by
  induction n generalizing P with
  | zero =>
      rw [Finsupp.single_zero, applyMonomialDifferential_zero]
      rfl
  | succ n ih =>
      have hs : Finsupp.single i (n + 1) =
          Finsupp.single i n + Finsupp.single i 1 := by
        ext j
        by_cases hji : j = i <;> simp [hji]
      rw [hs, applyMonomialDifferential_comp,
        applyMonomialDifferential_single, ih]
      change iteratedPDerivAt i n (iteratedPDerivAt i 1 P) =
        iteratedPDerivAt i 1 (iteratedPDerivAt i n P)
      exact iteratedPDerivAt_comm i i n 1 P

private theorem iteratedPDerivAt_rename
    {R sigma tau : Type*} [CommSemiring R]
    (f : sigma → tau) (hf : Function.Injective f)
    (i : sigma) (n : ℕ) (P : MvPolynomial sigma R) :
    iteratedPDerivAt (f i) n (MvPolynomial.rename f P) =
      MvPolynomial.rename f (iteratedPDerivAt i n P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPDerivAt, ih]
      rw [MvPolynomial.pderiv_rename hf]

private theorem iteratedPDerivAt_inr_mul_rename
    {R sigma tau : Type*} [CommRing R]
    (j : tau) (n : ℕ) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) :
    iteratedPDerivAt (Sum.inr j) n
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl G *
        MvPolynomial.rename Sum.inr (iteratedPDerivAt j n K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPDerivAt, ih, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_eq_zero_of_notMem_vars
          (MvPolynomial.inr_notMem_vars_rename_inl j G),
        MvPolynomial.pderiv_rename Sum.inr_injective]
      simp

private theorem applyMonomialDifferential_mapDomain_inr_mul_rename
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (d : tau →₀ ℕ) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) :
    applyMonomialDifferential (d.mapDomain Sum.inr)
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl G *
        MvPolynomial.rename Sum.inr (applyMonomialDifferential d K) := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i n d hi hn ih =>
      rw [Finsupp.mapDomain_add, applyMonomialDifferential_comp,
        Finsupp.mapDomain_single, applyMonomialDifferential_single_nat,
        ih, iteratedPDerivAt_inr_mul_rename,
        ← applyMonomialDifferential_single_nat,
        ← applyMonomialDifferential_comp]

private theorem totalDegree_mapDomain
    {sigma tau : Type*} (f : sigma → tau) (hf : Function.Injective f)
    (d : sigma →₀ ℕ) :
    (d.mapDomain f).sum (fun _ n ↦ n) = d.sum (fun _ n ↦ n) := by
  exact Finsupp.sum_mapDomain_index_inj hf

private theorem applyNegDifferential_rename_inr_mul_rename
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (H : MvPolynomial tau R) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) :
    applyNegDifferential (MvPolynomial.rename Sum.inr H)
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl G *
        MvPolynomial.rename Sum.inr (applyNegDifferential H K) := by
  induction H using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.rename_monomial,
        applyNegDifferential_monomial,
        totalDegree_mapDomain Sum.inr Sum.inr_injective,
        applyMonomialDifferential_mapDomain_inr_mul_rename,
        applyNegDifferential_monomial, map_mul, map_mul]
      rw [MvPolynomial.rename_C]
      have hC :
          (MvPolynomial.C ((-1 : R) ^ (d.sum fun _ n => n)) *
              MvPolynomial.C c :
              MvPolynomial (Sum sigma tau) R) =
            MvPolynomial.C (c * (-1 : R) ^ (d.sum fun _ n => n)) := by
        rw [← map_mul]
        congr 1
        ring
      rw [hC]
      simp only [mul_comm, mul_left_comm]
  | add H L hH hL =>
      rw [map_add, applyNegDifferential_add_left, hH, hL,
        applyNegDifferential_add_left, map_add, mul_add]

private theorem iteratedPDerivAt_inl_rename_mul
    {R sigma tau : Type*} [CommRing R]
    (i : sigma) (n : ℕ) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) :
    iteratedPDerivAt (Sum.inl i) n
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl (iteratedPDerivAt i n G) *
        MvPolynomial.rename Sum.inr K := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPDerivAt, ih, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_rename Sum.inl_injective,
        MvPolynomial.pderiv_eq_zero_of_notMem_vars
          (MvPolynomial.inl_notMem_vars_rename_inr i K)]
      simp

private theorem applyMonomialDifferential_mapDomain_inl_rename_mul
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (d : sigma →₀ ℕ) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) :
    applyMonomialDifferential (d.mapDomain Sum.inl)
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl (applyMonomialDifferential d G) *
        MvPolynomial.rename Sum.inr K := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i n d hi hn ih =>
      rw [Finsupp.mapDomain_add, applyMonomialDifferential_comp,
        Finsupp.mapDomain_single, applyMonomialDifferential_single_nat,
        ih, iteratedPDerivAt_inl_rename_mul,
        ← applyMonomialDifferential_single_nat,
        ← applyMonomialDifferential_comp]

private theorem applyNegDifferential_rename_inl_rename_mul
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (F G : MvPolynomial sigma R) (K : MvPolynomial tau R) :
    applyNegDifferential (MvPolynomial.rename Sum.inl F)
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl (applyNegDifferential F G) *
        MvPolynomial.rename Sum.inr K := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.rename_monomial,
        applyNegDifferential_monomial,
        totalDegree_mapDomain Sum.inl Sum.inl_injective,
        applyMonomialDifferential_mapDomain_inl_rename_mul,
        applyNegDifferential_monomial, map_mul, map_mul]
      rw [MvPolynomial.rename_C]
      have hC :
          (MvPolynomial.C ((-1 : R) ^ (d.sum fun _ n => n)) *
              MvPolynomial.C c :
              MvPolynomial (Sum sigma tau) R) =
            MvPolynomial.C (c * (-1 : R) ^ (d.sum fun _ n => n)) := by
        rw [← map_mul]
        congr 1
        ring
      rw [hC]
      simp only [mul_assoc, mul_comm]
  | add F L hF hL =>
      rw [map_add, applyNegDifferential_add_left, hF, hL,
        applyNegDifferential_add_left, map_add, add_mul]

/-- Constant-coefficient differential action factors across disjoint `Sum`
variable blocks. The two blocks may have different finite index types. -/
theorem applyNegDifferential_sumBlockFactorization
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (F G : MvPolynomial sigma R) (H K : MvPolynomial tau R) :
    applyNegDifferential
        (MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr H)
        (MvPolynomial.rename Sum.inl G * MvPolynomial.rename Sum.inr K) =
      MvPolynomial.rename Sum.inl (applyNegDifferential F G) *
        MvPolynomial.rename Sum.inr (applyNegDifferential H K) := by
  rw [applyNegDifferential_mul,
    applyNegDifferential_rename_inr_mul_rename,
    applyNegDifferential_rename_inl_rename_mul]

end

end RealRooted
