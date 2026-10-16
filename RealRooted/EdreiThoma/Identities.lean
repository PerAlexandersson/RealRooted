module

public import RealRooted.EdreiThoma.PFSeries
public import RealRooted.Mathlib.LinearAlgebra.Matrix.DesnanotJacobi

/-!
# Edrei's determinant identities and monotone Padé limits

This file formalizes assertions (i)--(v) in Edrei's proof of the converse
Aissen--Schoenberg--Whitney theorem: the two bordered-determinant recurrences, reciprocal
duality, coefficient nonnegativity, and the monotone limits that produce a summable sequence of
linear factors.

The strict positivity hypothesis on every contiguous Toeplitz minor is Edrei's property (P).
-/

@[expose] public noncomputable section

open Polynomial Filter Topology

namespace RealRooted.EdreiThoma

/-- `a` extended by zero to negative indices. -/
def tc (a : ℕ → ℝ) (k : ℤ) : ℝ := if 0 ≤ k then a k.toNat else 0

/-- Edrei's `A^{(n)}_m = det (a_{m+i-j})_{i,j=0..n-1}` (`A^{(0)}_m = 1`). Note the argument order:
size `n` first, shift `m` second. -/
def A (a : ℕ → ℝ) (n m : ℕ) : ℝ :=
  Matrix.det (Matrix.of fun (i j : Fin n) => tc a ((m : ℤ) + i - j))

/-- Edrei's `Q^{(m,n)}(z) = (1 / A^{(n)}_m) * det` of the `(n+1) × (n+1)` matrix whose first row
is `(1, z, ..., z^n)` and whose rows `i = 1..n` are `(a_{m+i-j})_{j=0..n}`. -/
def Q (a : ℕ → ℝ) (m n : ℕ) : ℝ[X] :=
  C (1 / A a n m) *
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) =>
      if (i : ℕ) = 0 then (X : ℝ[X]) ^ (j : ℕ) else C (tc a ((m : ℤ) + i - j)))

/-- `S^{(m,n)}(z) = Q^{(m,n)}(-z)`. -/
def S (a : ℕ → ℝ) (m n : ℕ) : ℝ[X] := (Q a m n).comp (-X)

/-- `r_{mn} = (A^{(n+1)}_{m+1} / A^{(n+1)}_m) / (A^{(n)}_{m+1} / A^{(n)}_m)`. -/
def rr (a : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (A a (n + 1) (m + 1) / A a (n + 1) m) / (A a n (m + 1) / A a n m)

/-- `γ_{mn} = (A^{(n+2)}_{m+1} / A^{(n+1)}_m) / (A^{(n+1)}_{m+1} / A^{(n)}_m)`. -/
def gam (a : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (A a (n + 2) (m + 1) / A a (n + 1) m) / (A a (n + 1) (m + 1) / A a n m)

/-! ## Desnanot–Jacobi condensation and the bordered determinants -/

section Helpers
open Matrix

/-- The bordered matrix defining `Q`. -/
private def bord (a : ℕ → ℝ) (m n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X] :=
  Matrix.of fun (i j : Fin (n + 1)) =>
    if (i : ℕ) = 0 then (X : ℝ[X]) ^ (j : ℕ) else C (tc a ((m : ℤ) + i - j))

/-- The Toeplitz matrix defining `A`. -/
private def toepM (a : ℕ → ℝ) (n m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun (i j : Fin n) => tc a ((m : ℤ) + i - j)

private lemma A_eq (a : ℕ → ℝ) (n m : ℕ) : A a n m = (toepM a n m).det := rfl

private lemma Q_eq (a : ℕ → ℝ) (m n : ℕ) :
    Q a m n = C (1 / A a n m) * (bord a m n).det := rfl

private lemma det_mapC (M : Matrix (Fin n) (Fin n) ℝ) :
    ((C : ℝ →+* ℝ[X]).mapMatrix M).det = C M.det := (RingHom.map_det _ _).symm

/-- Toeplitz Desnanot–Jacobi. -/
private lemma toep_dodgson (a : ℕ → ℝ) (n m : ℕ) :
    A a (n + 2) (m + 1) * A a n (m + 1) =
      A a (n + 1) (m + 1) * A a (n + 1) (m + 1) - A a (n + 1) (m + 2) * A a (n + 1) m := by
  have h := Matrix.det_mul_det_interior (toepM a (n + 2) (m + 1))
  have e1 : (toepM a (n + 2) (m + 1)).submatrix Fin.succ Fin.succ = toepM a (n + 1) (m + 1) := by
    ext i j; simp [toepM]; congr 1; ring
  have e2 : (toepM a (n + 2) (m + 1)).submatrix Fin.castSucc Fin.castSucc =
      toepM a (n + 1) (m + 1) := by
    ext i j; simp [toepM]
  have e3 : (toepM a (n + 2) (m + 1)).submatrix Fin.succ Fin.castSucc =
      toepM a (n + 1) (m + 2) := by
    ext i j; simp [toepM]; congr 1; ring
  have e4 : (toepM a (n + 2) (m + 1)).submatrix Fin.castSucc Fin.succ = toepM a (n + 1) m := by
    ext i j; simp [toepM]; congr 1; ring
  have e5 : (toepM a (n + 2) (m + 1)).submatrix
      (fun i : Fin n => i.castSucc.succ) (fun i : Fin n => i.castSucc.succ) =
        toepM a n (m + 1) := by
    ext i j; simp [toepM]; congr 1; ring
  rw [e1, e2, e3, e4, e5] at h
  simpa [A_eq] using h

private lemma Ctc_congr (a : ℕ → ℝ) {x y : ℤ} (h : x = y) :
    C (tc a x) = C (tc a y) := by
  rw [h]

/-- closes `tc a x = tc a y` or `C (tc a x) = C (tc a y)` with `x = y` by `ring`. -/
local macro "tc_eq" : tactic => `(tactic| first
  | exact Ctc_congr _ (by grind)
  | exact congrArg (tc _) (by grind))

/-- Identity (a): Dodgson on the bordered matrix of shift `m+1`. -/
private lemma bord_dodgson_a (a : ℕ → ℝ) (m n : ℕ) :
    (bord a (m + 1) (n + 1)).det * C (A a n (m + 1)) =
      C (A a (n + 1) (m + 1)) * (bord a (m + 1) n).det -
      X * C (A a (n + 1) (m + 2)) * (bord a m n).det := by
  have h := Matrix.det_mul_det_interior (bord a (m + 1) (n + 1))
  have e1 : (bord a (m + 1) (n + 1)).submatrix Fin.succ Fin.succ =
      (C : ℝ →+* ℝ[X]).mapMatrix (toepM a (n + 1) (m + 1)) := by
    refine Matrix.ext fun i j => ?_
    simp only [submatrix_apply, RingHom.mapMatrix_apply, map_apply]
    tc_eq
  have e2 : (bord a (m + 1) (n + 1)).submatrix Fin.castSucc Fin.castSucc = bord a (m + 1) n := by
    refine Matrix.ext fun i j => ?_
    simp [bord]
  have e3 : (bord a (m + 1) (n + 1)).submatrix Fin.succ Fin.castSucc =
      (C : ℝ →+* ℝ[X]).mapMatrix (toepM a (n + 1) (m + 2)) := by
    refine Matrix.ext fun i j => ?_
    simp only [submatrix_apply, RingHom.mapMatrix_apply, map_apply]
    tc_eq
  have e4 : (bord a (m + 1) (n + 1)).submatrix Fin.castSucc Fin.succ =
      Matrix.of fun i j => (fun i : Fin (n + 1) => if (i : ℕ) = 0 then (X : ℝ[X]) else 1) i *
        bord a m n i j := by
    refine Matrix.ext fun i j => ?_
    simp only [bord, submatrix_apply, of_apply, Fin.val_castSucc, Fin.val_succ]
    split_ifs
    · ring
    · rw [one_mul]; tc_eq
  have e5 : (bord a (m + 1) (n + 1)).submatrix
      (fun i : Fin n => i.castSucc.succ) (fun i : Fin n => i.castSucc.succ) =
      (C : ℝ →+* ℝ[X]).mapMatrix (toepM a n (m + 1)) := by
    refine Matrix.ext fun i j => ?_
    simp only [submatrix_apply, RingHom.mapMatrix_apply, map_apply]
    tc_eq
  rw [e1, e2, e3, e4, e5, det_mul_column, det_mapC, det_mapC, det_mapC] at h
  have hp : (∏ i : Fin (n + 1), if (i : ℕ) = 0 then (X : ℝ[X]) else 1) = X := by
    rw [Fin.prod_univ_succ]; simp
  rw [hp, ← A_eq, ← A_eq, ← A_eq] at h
  linear_combination h

private lemma det_rot {R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (M.submatrix (finRotate (k + 1)) id).det = (-1) ^ k * M.det := by
  rw [det_permute, sign_finRotate]; simp

private lemma val_finRotate_ne {k : ℕ} {i : Fin (k + 1)} (h : i ≠ Fin.last k) :
    (finRotate (k + 1) i : ℕ) = i + 1 := coe_finRotate_of_ne_last h

/-- Identity (5) at the level of bordered determinants. -/
private lemma bord_dodgson_5 (a : ℕ → ℝ) (m n : ℕ) :
    (bord a m (n + 1)).det * C (A a n (m + 1)) =
      C (A a (n + 1) m) * (bord a (m + 1) n).det -
      X * C (A a (n + 1) (m + 1)) * (bord a m n).det := by
  set R := (bord a m (n + 1)).submatrix (finRotate (n + 2)) id with hR
  have h := Matrix.det_mul_det_interior R
  have hcs : ∀ i : Fin (n + 1), (finRotate (n + 2) i.castSucc : ℕ) = i + 1 := fun i =>
    val_finRotate_ne (by simp [Fin.ext_iff]; lia)
  have f1 : R.submatrix Fin.succ Fin.succ =
      Matrix.of fun i j => (fun i : Fin (n + 1) => if i = Fin.last n then (X : ℝ[X]) else 1) i *
        ((bord a m n).submatrix (finRotate (n + 1)) id) i j := by
    refine Matrix.ext fun i j => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp only [hR, submatrix_apply, id, Fin.succ_last, finRotate_last, bord, of_apply,
        Fin.val_zero, ite_true, Fin.val_succ, pow_succ]
      ring
    · have h1 : (finRotate (n + 2) i.succ : ℕ) = i + 2 := by
        rw [val_finRotate_ne (by simpa using hi)]; simp
      have h2 := val_finRotate_ne hi
      simp only [hR, bord, submatrix_apply, of_apply, id, h1, h2, ite_eq_right hi, Fin.val_succ]
      simp only [show (i : ℕ) + 2 ≠ 0 by lia, show (i : ℕ) + 1 ≠ 0 by lia,
        ite_false, one_mul]
      tc_eq
  have f2 : R.submatrix Fin.castSucc Fin.castSucc =
      (C : ℝ →+* ℝ[X]).mapMatrix (toepM a (n + 1) (m + 1)) := by
    refine Matrix.ext fun i j => ?_
    simp only [hR, bord, submatrix_apply, of_apply, id, hcs, Fin.val_castSucc,
      show (i : ℕ) + 1 ≠ 0 by lia, ite_false, toepM, RingHom.mapMatrix_apply, map_apply]
    tc_eq
  have f3 : R.submatrix Fin.succ Fin.castSucc =
      (bord a (m + 1) n).submatrix (finRotate (n + 1)) id := by
    refine Matrix.ext fun i j => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [hR, bord]
    · have h1 : (finRotate (n + 2) i.succ : ℕ) = i + 2 := by
        rw [val_finRotate_ne (by simpa using hi)]; simp
      have h2 := val_finRotate_ne hi
      simp only [hR, bord, submatrix_apply, of_apply, id, h1, h2, Fin.val_castSucc]
      simp only [show (i : ℕ) + 2 ≠ 0 by lia, show (i : ℕ) + 1 ≠ 0 by lia, ite_false]
      tc_eq
  have f4 : R.submatrix Fin.castSucc Fin.succ =
      (C : ℝ →+* ℝ[X]).mapMatrix (toepM a (n + 1) m) := by
    refine Matrix.ext fun i j => ?_
    simp only [hR, bord, submatrix_apply, of_apply, id, hcs, Fin.val_succ,
      show (i : ℕ) + 1 ≠ 0 by lia, ite_false, toepM, RingHom.mapMatrix_apply, map_apply]
    tc_eq
  have f5 : R.submatrix (fun i : Fin n => i.castSucc.succ) (fun i : Fin n => i.castSucc.succ) =
      (C : ℝ →+* ℝ[X]).mapMatrix (toepM a n (m + 1)) := by
    refine Matrix.ext fun i j => ?_
    have h1 : (finRotate (n + 2) i.castSucc.succ : ℕ) = i + 2 := by
      rw [val_finRotate_ne (by simp [Fin.ext_iff]; lia)]; simp
    simp only [hR, bord, submatrix_apply, of_apply, id, h1, show (i : ℕ) + 2 ≠ 0 by lia,
      ite_false, toepM, RingHom.mapMatrix_apply, map_apply, Fin.val_succ, Fin.val_castSucc]
    tc_eq
  rw [f1, f2, f3, f4, f5, det_mul_column, det_mapC, det_mapC, det_mapC, det_rot, det_rot,
    det_rot] at h
  have hp : (∏ i : Fin (n + 1), if i = Fin.last n then (X : ℝ[X]) else 1) = X := by
    simp
  rw [hp, ← A_eq, ← A_eq, ← A_eq] at h
  have hs : ((-1 : ℝ[X]) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-(-1 : ℝ[X]) ^ n) * h - ((bord a m (n + 1)).det * C (A a n (m + 1)) -
      (C (A a (n + 1) m) * (bord a (m + 1) n).det -
      X * C (A a (n + 1) (m + 1)) * (bord a m n).det)) * hs

end Helpers

/-- Edrei's identity (5) (pure algebra, valid whenever the denominators are nonzero). -/
theorem S_succ_eq {a : ℕ → ℝ} (hA : ∀ n m, A a n m ≠ 0) (m n : ℕ) :
    S a m (n + 1) = S a (m + 1) n + C (rr a m n) * X * S a m n := by
  have key : Q a m (n + 1) = Q a (m + 1) n - C (rr a m n) * X * Q a m n := by
    apply Polynomial.funext; intro x
    have h := congrArg (eval x) (bord_dodgson_5 a m n)
    simp only [eval_mul, eval_sub, eval_C, eval_X] at h
    simp only [Q_eq, eval_mul, eval_sub, eval_C, eval_X, rr]
    have := hA n (m + 1); have := hA (n + 1) m; have := hA n m; have := hA (n + 1) (m + 1)
    field_simp
    linear_combination h
  simp only [S, key, sub_comp, mul_comp, C_comp, X_comp]
  ring

/-- Edrei's identity (6). -/
theorem S_succ_shift_sub_eq {a : ℕ → ℝ} (hA : ∀ n m, A a n m ≠ 0) (m n : ℕ) :
    S a (m + 1) (n + 1) - S a m (n + 1) = - (C (gam a m n) * X * S a m n) := by
  have key : Q a (m + 1) (n + 1) - Q a m (n + 1) = C (gam a m n) * X * Q a m n := by
    apply Polynomial.funext; intro x
    have h5 := congrArg (eval x) (bord_dodgson_5 a m n)
    have ha := congrArg (eval x) (bord_dodgson_a a m n)
    have ht := toep_dodgson a n m
    simp only [eval_mul, eval_sub, eval_C, eval_X] at h5 ha
    simp only [Q_eq, eval_mul, eval_sub, eval_C, eval_X, gam]
    have := hA n (m + 1); have := hA (n + 1) m; have := hA n m; have := hA (n + 1) (m + 1)
    have h0 := hA n (m + 1)
    rw [← eq_div_iff h0] at h5 ha ht
    rw [h5, ha, ht]
    field_simp
    ring
  simp only [S]
  rw [← sub_comp, key]
  simp only [mul_comp, C_comp, X_comp]
  ring

private lemma card_compl_eq {N k : ℕ} {s : Finset (Fin N)} (h : s.card = k) :
    sᶜ.card = N - k := by
  rw [Finset.card_compl, Fintype.card_fin, h]

/-- The leading `N × N` block of the Toeplitz matrix. -/
private def toepMat (a : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => toeplitz a i j

private lemma toepMat_mul {a c : ℕ → ℝ}
    (hconv : ∀ n, ∑ k ∈ Finset.range (n + 1), c k * a (n - k) = if n = 0 then 1 else 0)
    (N : ℕ) : toepMat a N * toepMat c N = 1 := by
  ext i j; simp only [Matrix.mul_apply, toepMat, Matrix.of_apply, Matrix.one_apply]
  rcases lt_or_ge (i : ℕ) j with hij | hij
  · rw [ite_eq_right (by intro e; subst e; exact lt_irrefl _ hij)]
    apply Finset.sum_eq_zero
    intro l _
    simp only [toeplitz_apply]
    split_ifs <;> first | (exfalso; lia) | simp
  · have := Fin.sum_univ_eq_sum_range
      (fun l => toeplitz a i l * toeplitz c l j) N
    rw [this]
    have hsub : Finset.Ico (j : ℕ) (i + 1) ⊆ Finset.range N := by
      intro l hl; simp at hl ⊢; lia
    rw [← Finset.sum_subset hsub (fun l _ hl => by
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hl
      simp only [toeplitz_apply]; split_ifs <;> first | (exfalso; lia) | simp)]
    rw [Finset.sum_Ico_eq_sum_range]
    have h2 : (i : ℕ) + 1 - j = (i - j : ℕ) + 1 := by lia
    rw [h2]
    have h3 : ∀ q ∈ Finset.range ((i - j : ℕ) + 1),
        toeplitz a i (j + q) * toeplitz c (j + q) j = c q * a ((i - j : ℕ) - q) := by
      intro q hq
      simp at hq
      simp only [toeplitz_apply]
      rw [ite_eq_left (by lia), ite_eq_left (by lia)]
      rw [mul_comm]; congr 2 <;> lia
    rw [Finset.sum_congr rfl h3, hconv]
    congr 1
    simp only [Fin.ext_iff, eq_iff_iff]
    lia

private lemma toepMat_det {a : ℕ → ℝ} (h0 : a 0 = 1) (N : ℕ) : (toepMat a N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [toepMat, toeplitz, h0]
  · intro i j hij
    simp only [toepMat, Matrix.of_apply, toeplitz]
    rw [ite_eq_right]
    have : i < j := hij
    rw [Fin.lt_def] at this; lia

/-- sign twist of the Toeplitz entries. -/
private lemma tc_alt (b : ℕ → ℝ) (n i j : ℕ) :
    tc (fun k => (-1) ^ k * b k) ((n : ℤ) + i - j) =
      (-1) ^ (n + i) * ((-1) ^ j * tc b ((n : ℤ) + i - j)) := by
  unfold tc
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, ((n : ℤ) + i - j) = k :=
      ⟨_, (Int.toNat_of_nonneg h).symm⟩
    rw [hk, Int.toNat_natCast]
    have hk' : k + j = n + i := by lia
    rw [← hk']
    change (-1) ^ k * b k = _
    have hp : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [pow_add]
    linear_combination (-(-1 : ℝ) ^ k * b k) * hp
  · simp

private lemma toeplitz_eq_tc (a : ℕ → ℝ) (p q : ℕ) :
    toeplitz a p q = tc a ((p : ℤ) - q) := by
  rw [toeplitz_apply]
  unfold tc
  split_ifs <;> congr 1 <;> lia

private lemma sq_prod_neg_one {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ s, (-1 : ℝ) ^ f i) * (∏ i ∈ s, (-1 : ℝ) ^ f i) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- Duality (Edrei's Observation I with `a 0 = 1`): if `b` are the coefficients of `1 / f(-z)`
(`∑_{k ≤ n} a_k (-1)^{n-k} b_{n-k} = δ_{n0}`), then `A^{(n)}_m(a) = A^{(m)}_n(b)`. -/
theorem A_eq_swap_of_inverse {a b : ℕ → ℝ} (h0 : a 0 = 1)
    (hb : ∀ n, ∑ k ∈ Finset.range (n + 1), a k * ((-1) ^ (n - k) * b (n - k)) =
      if n = 0 then 1 else 0) (n m : ℕ) :
    A a n m = A b m n := by
  set c : ℕ → ℝ := fun k => (-1) ^ k * b k with hc
  set N := m + n with hN
  have hmul : toepMat a N * toepMat c N = 1 :=
    mul_eq_one_comm.1 (toepMat_mul (a := c) (c := a) hb N)
  set s : Finset (Fin N) := Finset.univ.image (fun i : Fin m => (⟨n + i, by lia⟩ : Fin N))
    with hsdef
  set t : Finset (Fin N) := Finset.univ.image (fun i : Fin m => (⟨i, by lia⟩ : Fin N))
    with htdef
  have inj_s : Function.Injective (fun i : Fin m => (⟨n + i, by lia⟩ : Fin N)) := by
    intro i j h
    exact Fin.ext <| by simpa using congrArg Fin.val h
  have inj_t : Function.Injective (fun i : Fin m => (⟨i, by lia⟩ : Fin N)) := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin N => x.val) h)
  have hs : s.card = m := by rw [hsdef, Finset.card_image_of_injective _ inj_s]; simp
  have ht : t.card = m := by rw [htdef, Finset.card_image_of_injective _ inj_t]; simp
  have es : ⇑(s.orderEmbOfFin hs) = fun i : Fin m => (⟨n + i, by lia⟩ : Fin N) :=
    (Finset.orderEmbOfFin_unique hs (fun i => by simp [hsdef])
      (by intro i j h; simp only [Fin.lt_def] at h ⊢; lia)).symm
  have et : ⇑(t.orderEmbOfFin ht) = fun i : Fin m => (⟨i, by lia⟩ : Fin N) :=
    (Finset.orderEmbOfFin_unique ht (fun i => by simp [htdef])
      (by intro i j h; simp only [Fin.lt_def] at h ⊢; lia)).symm
  have hnm : N - m = n := by lia
  have esc : ⇑(sᶜ.orderEmbOfFin (card_compl_eq hs)) =
      fun k : Fin (N - m) => (⟨k, by lia⟩ : Fin N) := by
    refine (Finset.orderEmbOfFin_unique _ (fun k => ?_)
      (by intro i j h; simp only [Fin.lt_def] at h ⊢; lia)).symm
    simp only [hsdef, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi; simp [Fin.ext_iff] at hi; lia
  have etc : ⇑(tᶜ.orderEmbOfFin (card_compl_eq ht)) =
      fun k : Fin (N - m) => (⟨m + k, by lia⟩ : Fin N) := by
    refine (Finset.orderEmbOfFin_unique _ (fun k => ?_)
      (by intro i j h; simp only [Fin.lt_def] at h ⊢; lia)).symm
    simp only [htdef, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi; simp [Fin.ext_iff] at hi; lia
  have J := Matrix.jacobi_minor (toepMat a N) (toepMat c N) hmul hs ht
  rw [toepMat_det h0, mul_one, es, et, esc, etc] at J
  -- the right-hand side is `A a n m`
  have hR : ((toepMat a N).submatrix (fun k : Fin (N - m) => (⟨m + k, by lia⟩ : Fin N))
      (fun k : Fin (N - m) => (⟨k, by lia⟩ : Fin N))).det = A a n m := by
    rw [← Matrix.det_submatrix_equiv_self (finCongr hnm.symm), A_eq]
    congr 1
    ext i j
    simp only [toepMat, toepM, Matrix.submatrix_apply, Matrix.of_apply]
    rw [toeplitz_eq_tc]
    congr 1
  -- the left-hand side
  have hL : (toepMat c N).submatrix (fun i : Fin m => (⟨n + i, by lia⟩ : Fin N))
      (fun i : Fin m => (⟨i, by lia⟩ : Fin N)) =
      Matrix.of fun i j => (fun i : Fin m => (-1 : ℝ) ^ (n + (i : ℕ))) i *
        ((Matrix.of fun i j => (fun j : Fin m => (-1 : ℝ) ^ (j : ℕ)) j *
          toepM b m n i j) i j) := by
    ext i j
    simp only [toepMat, toepM, Matrix.submatrix_apply, Matrix.of_apply, toeplitz_eq_tc]
    rw [show ((n + (i : ℕ) : ℕ) : ℤ) - ((j : ℕ) : ℤ) =
      (n : ℤ) + (i : ℕ) - (j : ℕ) by push_cast; ring]
    exact tc_alt b n i j
  rw [hL, Matrix.det_mul_column, Matrix.det_mul_row, ← A_eq, hR] at J
  have hsum_s : ∑ z ∈ s, (z : ℕ) = ∑ i : Fin m, (n + (i : ℕ)) := by
    rw [hsdef, Finset.sum_image (fun x _ y _ h => inj_s h)]
  have hsum_t : ∑ z ∈ t, (z : ℕ) = ∑ i : Fin m, (i : ℕ) := by
    rw [htdef, Finset.sum_image (fun x _ y _ h => inj_t h)]
  rw [pow_add, hsum_s, hsum_t, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum] at J
  have h1 := sq_prod_neg_one Finset.univ (fun i : Fin m => n + (i : ℕ))
  have h2 := sq_prod_neg_one Finset.univ (fun i : Fin m => (i : ℕ))
  linear_combination -J + A b m n * ((∏ i : Fin m, (-1 : ℝ) ^ (i : ℕ)) *
    (∏ i : Fin m, (-1 : ℝ) ^ (i : ℕ))) * h1 + A b m n * h2

/-- The minor of the Toeplitz matrix with rows `m+1, ..., m+n` and columns `{0..n} \ {j}`. -/
private def minorK (a : ℕ → ℝ) (m n : ℕ) (j : Fin (n + 1)) : ℝ :=
  Matrix.det (Matrix.of fun (i l : Fin n) =>
    tc a ((m : ℤ) + ((i : ℕ) + 1 : ℕ) - (j.succAbove l : ℕ)))

private lemma bord_det_expand (a : ℕ → ℝ) (m n : ℕ) :
    (bord a m n).det =
      ∑ j : Fin (n + 1), C ((-1) ^ (j : ℕ) * minorK a m n j) * X ^ (j : ℕ) := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (bord a m n).submatrix Fin.succ j.succAbove =
      (C : ℝ →+* ℝ[X]).mapMatrix (Matrix.of fun (i l : Fin n) =>
        tc a ((m : ℤ) + ((i : ℕ) + 1 : ℕ) - (j.succAbove l : ℕ))) := by
    refine Matrix.ext fun i l => ?_
    simp [bord]
  rw [e, det_mapC]
  simp only [bord, Matrix.of_apply, Fin.val_zero, ite_true, minorK, map_mul, map_pow, map_neg,
    map_one]
  ring

private lemma S_eq_sum (a : ℕ → ℝ) (m n : ℕ) :
    S a m n = ∑ j : Fin (n + 1), C (1 / A a n m * minorK a m n j) * X ^ (j : ℕ) := by
  rw [S, Q_eq, bord_det_expand, mul_comp, C_comp, Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_comp, C_comp, X_pow_comp]
  rw [neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one]
  have hp : ((-1 : ℝ[X]) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (C (1 / A a n m) * C (minorK a m n j) * X ^ (j : ℕ)) * hp

private lemma minorK_nonneg {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a) (m n : ℕ)
    (j : Fin (n + 1)) :
    0 ≤ minorK a m n j := by
  have := hpf (rows := fun i : Fin n => m + 1 + i)
    (cols := fun l : Fin n => j.succAbove l)
    (fun i i' h => by simp only; lia) (fun l l' h => Fin.strictMono_succAbove j h)
  convert this using 1
  rw [minorK]
  congr 1; refine Matrix.ext fun i l => ?_
  simp only [Matrix.of_apply, Matrix.submatrix_apply]
  rw [toeplitz_eq_tc]
  congr 1
  push_cast
  ring

/-- Assertion (i): for a Pólya frequency sequence with property (P), the coefficients of
`S^{(m,n)}` are nonnegative. -/
theorem coeff_S_nonneg {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    (hP : ∀ n m, 0 < A a n m) (m n k : ℕ) :
    0 ≤ (S a m n).coeff k := by
  rw [S_eq_sum, finsetSum_coeff]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact mul_nonneg (by have := hP n m; positivity) (minorK_nonneg hpf m n j)
  · exact le_rfl

/-! ## Auxiliary facts for the limit theorem -/

private lemma minorK_zero (a : ℕ → ℝ) (m n : ℕ) : minorK a m n 0 = A a n m := by
  rw [minorK, A_eq, toepM]
  congr 1; refine Matrix.ext fun i l => ?_
  simp only [Matrix.of_apply, Fin.succAbove_zero, Fin.val_succ]
  congr 1; push_cast; ring

private lemma coeff_S_zero {a : ℕ → ℝ} (hA : ∀ n m, A a n m ≠ 0) (m n : ℕ) :
    (S a m n).coeff 0 = 1 := by
  rw [S_eq_sum, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [minorK_zero, hA n m]
  · intro j _ hj
    rw [ite_eq_right]
    intro h; exact hj (Fin.ext h.symm)
  · simp

private lemma coeff_S_big (a : ℕ → ℝ) (m n k : ℕ) (hk : n < k) : (S a m n).coeff k = 0 := by
  rw [S_eq_sum, finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul_X_pow, ite_eq_right]
  have := j.isLt; lia

private lemma A_zero_size (a : ℕ → ℝ) (m : ℕ) : A a 0 m = 1 := by
  simp [A]

private lemma A_one_size (a : ℕ → ℝ) (m : ℕ) : A a 1 m = a m := by
  simp [A, Matrix.det_unique, tc]

private lemma A_shift_zero {a : ℕ → ℝ} (h0 : a 0 = 1) (n : ℕ) : A a n 0 = 1 := by
  rw [A, Matrix.det_of_isLowerTriangular]
  · simp [tc, h0]
  · intro i j hij
    have : i < j := hij
    simp only [Matrix.of_apply, tc]
    rw [ite_eq_right]
    rw [Fin.lt_def] at this; lia

private lemma S_size_zero {a : ℕ → ℝ} (m : ℕ) : S a m 0 = 1 := by
  rw [S_eq_sum]; simp [A_zero_size, minorK]

private lemma coeff_CXmul_succ (r : ℝ) (P : ℝ[X]) (k : ℕ) :
    (C r * X * P).coeff (k + 1) = r * P.coeff k := by
  rw [mul_assoc, coeff_C_mul, coeff_X_mul]

private lemma coeff_CXmul_zero (r : ℝ) (P : ℝ[X]) : (C r * X * P).coeff 0 = 0 := by
  rw [mul_assoc, coeff_C_mul]; simp

private lemma coeff1_S_zero_shift {a : ℕ → ℝ} (h0 : a 0 = 1)
    (hA : ∀ n m, A a n m ≠ 0) (n : ℕ) :
    (S a 0 (n + 1)).coeff 1 = a 1 := by
  induction n with
  | zero =>
    have := congrArg (fun p => p.coeff 1) (S_succ_eq hA 0 0)
    simp only [coeff_add, coeff_CXmul_succ, coeff_S_zero hA, coeff_S_big a 1 0 1 one_pos] at this
    rw [this, rr, A_one_size, A_one_size, A_zero_size, A_zero_size, h0]
    simp
  | succ n ih =>
    have h5 := congrArg (fun p => p.coeff 1) (S_succ_eq hA 0 (n + 1))
    have h6 := congrArg (fun p => p.coeff 1) (S_succ_shift_sub_eq hA 0 n)
    simp only [coeff_add, coeff_sub, coeff_neg, coeff_CXmul_succ, coeff_S_zero hA] at h5 h6
    have hrg : rr a 0 (n + 1) = gam a 0 n := by
      simp only [rr, gam, A_shift_zero h0]
    rw [h5, hrg]
    linarith

/-- Assertions (ii)--(v) (monotone limits and `∑ β ≤ a₁`). For a Pólya frequency sequence
with
`a 0 = 1` and property (P):
* the coefficients of `S^{(m,n+1)}` are nonincreasing in `m`, and every `S^{(·,n)}` has a
  coefficientwise limit `Sinf n` (a polynomial), with `Sinf 0 = 1`;
* `∑_m γ_{m n} < ∞`;
* `β_{n+1} := lim_m r_{mn}` exists, is `≥ 0`, and `Sinf (n+1) = (1 + β_{n+1} z) * Sinf n`
  (i.e. `Q^{(∞,n+1)}(z) = (1 - β_{n+1} z) Q^{(∞,n)}(z)`), here `β n` stands for `β_{n+1}`;
* `∑ β ≤ a₁` (so `β` is summable). -/
theorem coeff_S_antitone_and_exists_limit {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) (hP : ∀ n m, 0 < A a n m) :
    (∀ n k m, (S a (m + 1) (n + 1)).coeff k ≤ (S a m (n + 1)).coeff k) ∧
    (∀ n, Summable fun m => gam a m n) ∧
    ∃ (Sinf : ℕ → ℝ[X]) (β : ℕ → ℝ), Sinf 0 = 1 ∧
      (∀ n k, Tendsto (fun m => (S a m n).coeff k) atTop (𝓝 ((Sinf n).coeff k))) ∧
      (∀ n, 0 ≤ β n) ∧ (∀ n, Tendsto (fun m => rr a m n) atTop (𝓝 (β n))) ∧
      (∀ n, Sinf (n + 1) = (1 + C (β n) * X) * Sinf n) ∧
      Summable β ∧ ∑' n, β n ≤ a 1 := by
  have hA : ∀ n m, A a n m ≠ 0 := fun n m => (hP n m).ne'
  have gam_pos : ∀ m n, 0 < gam a m n := by
    intro m n; unfold gam
    have := hP (n + 2) (m + 1); have := hP (n + 1) m; have := hP (n + 1) (m + 1); have := hP n m
    positivity
  have rr_pos : ∀ m n, 0 < rr a m n := by
    intro m n; unfold rr
    have := hP (n + 1) (m + 1); have := hP (n + 1) m; have := hP n (m + 1); have := hP n m
    positivity
  -- coefficientwise form of identity (6)
  have i6 : ∀ m n k, (S a (m + 1) (n + 1)).coeff (k + 1) =
      (S a m (n + 1)).coeff (k + 1) - gam a m n * (S a m n).coeff k := by
    intro m n k
    have := congrArg (fun p => p.coeff (k + 1)) (S_succ_shift_sub_eq hA m n)
    simp only [coeff_sub, coeff_neg, coeff_CXmul_succ] at this
    linarith
  -- coefficientwise form of identity (5)
  have i5 : ∀ m n k, (S a m (n + 1)).coeff (k + 1) =
      (S a (m + 1) n).coeff (k + 1) + rr a m n * (S a m n).coeff k := by
    intro m n k
    have := congrArg (fun p => p.coeff (k + 1)) (S_succ_eq hA m n)
    simpa only [coeff_add, coeff_CXmul_succ] using this
  have i5z : ∀ m n, (S a m (n + 1)).coeff 0 = (S a (m + 1) n).coeff 0 := by
    intro m n
    rw [coeff_S_zero hA, coeff_S_zero hA]
  have mono : ∀ n k m, (S a (m + 1) (n + 1)).coeff k ≤ (S a m (n + 1)).coeff k := by
    intro n k m
    cases k with
    | zero => rw [coeff_S_zero hA, coeff_S_zero hA]
    | succ k =>
      rw [i6]
      exact sub_le_self _ (mul_nonneg (gam_pos m n).le (coeff_S_nonneg hpf hP m n k))
  have anti : ∀ n k, Antitone fun m => (S a m (n + 1)).coeff k :=
    fun n k => antitone_nat_of_succ_le (mono n k)
  have conv : ∀ n k, ∃ L, Tendsto (fun m => (S a m n).coeff k) atTop (𝓝 L) := by
    intro n k
    cases n with
    | zero =>
      exact ⟨(1 : ℝ[X]).coeff k, by simp only [S_size_zero]; exact tendsto_const_nhds⟩
    | succ n =>
      exact ⟨_, tendsto_atTop_ciInf (anti n k)
        ⟨0, by rintro _ ⟨m, rfl⟩; exact coeff_S_nonneg hpf hP m (n + 1) k⟩⟩
  choose L hL using conv
  set Sinf : ℕ → ℝ[X] := fun n => ∑ k ∈ Finset.range (n + 1), C (L n k) * X ^ k with hSinf
  have hT : ∀ n k, Tendsto (fun m => (S a m n).coeff k) atTop (𝓝 ((Sinf n).coeff k)) := by
    intro n k
    simp only [hSinf, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hk
    · exact hL n k
    · have : (fun m => (S a m n).coeff k) = fun _ => 0 := by
        funext m; exact coeff_S_big a m n k (by lia)
      rw [this]; exact tendsto_const_nhds
  have hS0 : Sinf 0 = 1 := by
    ext k
    exact tendsto_nhds_unique (hT 0 k) <| by
      simpa only [S_size_zero] using tendsto_const_nhds
  set β : ℕ → ℝ := fun n => (Sinf (n + 1)).coeff 1 - (Sinf n).coeff 1 with hβdef
  have hβ : ∀ n, Tendsto (fun m => rr a m n) atTop (𝓝 (β n)) := by
    intro n
    have hrr : (fun m => rr a m n) =
        fun m => (S a m (n + 1)).coeff 1 - (S a (m + 1) n).coeff 1 := by
      funext m
      rw [i5 m n 0, coeff_S_zero hA]
      ring
    rw [hrr]
    exact (hT (n + 1) 1).sub ((hT n 1).comp (tendsto_add_atTop_nat 1))
  have hβ0 : ∀ n, 0 ≤ β n := fun n => ge_of_tendsto' (hβ n) (fun m => (rr_pos m n).le)
  have ha1 : 0 ≤ a 1 := hpf.nonneg 1
  have hpart : ∀ N, ∑ n ∈ Finset.range N, β n ≤ a 1 := by
    intro N
    rw [hβdef, Finset.sum_range_sub (fun n => (Sinf n).coeff 1), hS0, coeff_one]
    cases N with
    | zero => simpa [hS0, coeff_one] using ha1
    | succ N =>
      have := (anti N 1).le_of_tendsto (hT (N + 1) 1) 0
      rw [coeff1_S_zero_shift h0 hA] at this
      simpa using this
  refine ⟨mono, ?_, Sinf, β, hS0, hT, hβ0, hβ, ?_, summable_of_sum_range_le hβ0 hpart,
    Real.tsum_le_of_sum_range_le hβ0 hpart⟩
  · intro n
    have hg : ∀ m, gam a m n = (S a m (n + 1)).coeff 1 - (S a (m + 1) (n + 1)).coeff 1 := by
      intro m
      rw [i6 m n 0, coeff_S_zero hA]
      ring
    refine summable_of_sum_range_le (c := (S a 0 (n + 1)).coeff 1) (fun m => (gam_pos m n).le) ?_
    intro M
    rw [Finset.sum_congr rfl (fun m _ => hg m), Finset.sum_range_sub']
    linarith [coeff_S_nonneg hpf hP M (n + 1) 1]
  · intro n
    ext k
    cases k with
    | zero =>
      rw [add_mul, one_mul, coeff_add, coeff_CXmul_zero, add_zero]
      refine tendsto_nhds_unique (hT (n + 1) 0) ?_
      have : (fun m => (S a m (n + 1)).coeff 0) = fun m => (S a (m + 1) n).coeff 0 :=
        funext fun m => i5z m n
      rw [this]
      exact (hT n 0).comp (tendsto_add_atTop_nat 1)
    | succ k =>
      rw [add_mul, one_mul, coeff_add, coeff_CXmul_succ]
      refine tendsto_nhds_unique (hT (n + 1) (k + 1)) ?_
      have : (fun m => (S a m (n + 1)).coeff (k + 1)) =
          fun m => (S a (m + 1) n).coeff (k + 1) + rr a m n * (S a m n).coeff k :=
        funext fun m => i5 m n k
      rw [this]
      exact ((hT n (k + 1)).comp (tendsto_add_atTop_nat 1)).add ((hβ n).mul (hT n k))

end RealRooted.EdreiThoma

