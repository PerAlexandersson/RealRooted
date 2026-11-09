module

import Mathlib.Tactic.Ring
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Site-weighted run sums and their transfer-matrix form

For a sequence `u : ℕ → R` with `u 0 = 1` and site weights `z₀, …, z_{N-1}`, the *site-weighted
run sum* is
`Z_N(z) = ∑_{S ⊆ [N]} (∏_{R ∈ Runs(S)} u_{|R|}) ∏_{i ∈ S} z_i`,
where `Runs(S)` are the maximal nonempty intervals of consecutive selected sites.

A subset is encoded by its indicator `s : Fin N → Bool`. The product over runs is computed by
`runWeight`, which reads the selection from the last site to the first and carries the length of
the run being read; the sum is `siteRunSum` (with a pending run of length `k` to the right of
the last site) and `siteWeightedRuns` (no pending run).

When `u k = e₁ᵀ Aᵏ 𝟙` for a square matrix `A`, the run sum is the first coordinate of
`(J + z_{N-1} A) ⋯ (J + z₀ A) 𝟙`, where `J = 𝟙 e₁ᵀ` (`siteWeightedRuns_runKernel`).
The proof is the recursion on the last site together with `J² = J`, `e₁ᵀ J = e₁ᵀ`.
-/

@[expose] public section

open Matrix

namespace RealRooted

section Runs

variable {R : Type*} [CommSemiring R]

/-- The weight `∏_{R ∈ Runs} u_{|R|}` of a selection, read from its last site to its first: the
second argument is the length of the run currently being read. A selected site extends the run;
an unselected site closes it, contributing `u` of its length. (For `u 0 = 1` the empty runs
between and around the maximal runs contribute `1`.) -/
def runWeight (u : ℕ → R) : List Bool → ℕ → R
  | [], k => u k
  | true :: l, k => runWeight u l (k + 1)
  | false :: l, k => u k * runWeight u l 0

/-- The site-weighted run sum over all selections `S ⊆ [N]`, where a run of length `k` is
already pending to the right of the last site, which continues the run containing it. -/
def siteRunSum (u : ℕ → R) (k : ℕ) {N : ℕ} (z : Fin N → R) : R :=
  ∑ s : Fin N → Bool, runWeight u (List.ofFn s).reverse k * ∏ i, if s i then z i else 1

/-- The site-weighted run sum
`Z_N(z) = ∑_{S ⊆ [N]} (∏_{R ∈ Runs(S)} u_{|R|}) ∏_{i ∈ S} z_i`. -/
def siteWeightedRuns (u : ℕ → R) {N : ℕ} (z : Fin N → R) : R :=
  siteRunSum u 0 z

@[simp] lemma siteRunSum_zero (u : ℕ → R) (k : ℕ) (z : Fin 0 → R) : siteRunSum u k z = u k := by
  simp [siteRunSum, runWeight]

/-- Recursion on the last site: it is either selected (extending the pending run) or not
(closing it). -/
theorem siteRunSum_succ (u : ℕ → R) (k : ℕ) {N : ℕ} (z : Fin (N + 1) → R) :
    siteRunSum u k z =
      z (Fin.last N) * siteRunSum u (k + 1) (Fin.init z) + u k * siteRunSum u 0 (Fin.init z) := by
  rw [siteRunSum, ← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  simp only [siteRunSum, Fintype.sum_bool, Fin.snocEquiv_apply]
  simp only [Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
    Fin.prod_univ_castSucc, List.concat_eq_append, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, runWeight, ite_true,
    Bool.false_eq_true, ite_false, Fin.init, mul_one, Finset.mul_sum]
  refine congrArg₂ _ (Finset.sum_congr rfl fun s _ => ?_) (Finset.sum_congr rfl fun s _ => ?_)
  · ring
  · ring

end Runs

/-! ### The transfer matrices -/

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The matrix `J = 𝟙 e₁ᵀ`, so that `(J f)ᵢ = f₀`. -/
def runJ (n : ℕ) (R : Type*) [Zero R] [One R] : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun _ j => if j = 0 then 1 else 0

/-- The transfer vector `(J + z_{N-1} A) ⋯ (J + z₀ A) 𝟙`. -/
def runVector (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (N : ℕ) → (Fin N → R) → Fin (n + 1) → R
  | 0, _ => fun _ => 1
  | N + 1, z => (runJ n R + z (Fin.last N) • A) *ᵥ runVector A N (Fin.init z)

/-- The kernel `u_k = e₁ᵀ Aᵏ 𝟙`, the weight of a run of length `k`. -/
def runKernel (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (k : ℕ) : R :=
  (A ^ k *ᵥ fun _ => 1) 0

@[simp] lemma runKernel_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : runKernel A 0 = 1 := by
  simp [runKernel]

lemma runVector_succ_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (N : ℕ) (z : Fin (N + 1) → R)
    (i : Fin (n + 1)) :
    runVector A (N + 1) z i = runVector A N (Fin.init z) 0 +
      z (Fin.last N) * ∑ j, A i j * runVector A N (Fin.init z) j := by
  simp [runVector, Matrix.mulVec, dotProduct, runJ, add_mul, Finset.sum_add_distrib,
    mul_assoc, Finset.mul_sum]

/-- **Transfer identity.** With `u_k = e₁ᵀ Aᵏ 𝟙`, the run sum with a pending run of length `k`
is `e₁ᵀ Aᵏ (J + z_{N-1} A) ⋯ (J + z₀ A) 𝟙`. -/
theorem siteRunSum_runKernel (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (k : ℕ) {N : ℕ}
    (z : Fin N → R) :
    siteRunSum (runKernel A) k z = ∑ j, (A ^ k) 0 j * runVector A N z j := by
  induction N generalizing k with
  | zero => simp [runKernel, Matrix.mulVec, dotProduct, runVector]
  | succ N ih =>
    rw [siteRunSum_succ, ih, ih]
    have hk : runKernel A k = ∑ i, (A ^ k) 0 i := by simp [runKernel, Matrix.mulVec, dotProduct]
    have h0 : ∑ j, (A ^ 0) 0 j * runVector A N (Fin.init z) j = runVector A N (Fin.init z) 0 := by
      simp [Matrix.one_apply]
    have hmul : ∀ j, (A ^ (k + 1)) 0 j = ∑ i, (A ^ k) 0 i * A i j := fun j => by
      rw [pow_succ, Matrix.mul_apply]
    simp only [runVector_succ_apply, h0, hk, mul_add, Finset.sum_add_distrib, hmul,
      Finset.mul_sum, Finset.sum_mul]
    rw [add_comm]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The kernel commutes with ring homomorphisms. -/
lemma runKernel_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (k : ℕ) :
    runKernel (A.map f) k = f (runKernel A k) := by
  have hpow : (A.map f) ^ k = (A ^ k).map f := (f.mapMatrix.map_pow A k).symm
  simp [runKernel, hpow, Matrix.mulVec, dotProduct, map_sum]

/-- **Transfer identity for the site-weighted run sum.** If `u_k = e₁ᵀ Aᵏ 𝟙` then
`Z_N(z) = e₁ᵀ (J + z_{N-1} A) ⋯ (J + z₀ A) 𝟙`. -/
theorem siteWeightedRuns_runKernel (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {N : ℕ}
    (z : Fin N → R) : siteWeightedRuns (runKernel A) z = runVector A N z 0 := by
  simp [siteWeightedRuns, siteRunSum_runKernel, Matrix.one_apply]

end RealRooted
