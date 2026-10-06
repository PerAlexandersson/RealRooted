import RealRooted.ShiftLemma
import RealRooted.PosCombo
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Peak polynomial induction framework

This file formalizes the algebraic induction engine behind the real-rootedness
of peak polynomials on Ferrers boards in the Peaks section (`sec:peaks`) of

* P. Alexandersson, A. Jal and M. Quemener,
  *Rook-Eulerian polynomials and permutation ideals*.

A `PeakFamily m` consists of polynomials `D k`, `U k` (`k : Fin m`) with
nonnegative coefficients. We put `A k = D k + U k`, `W k = X * D k + U k`, and
the recursion of the paper produces the next-level family
`D⁺ k = S k = ∑_{j < k} A j` and `U⁺ k = T k = ∑_{j ≥ k} W j`.

The six interlacing conditions (DU), (UU), (AW), reversed (DD), reversed (AA)
and (WW) of Theorem `thm:peak_rr_ferrers` are bundled in
`PeakFamily.Conditions`. All interlacings are zero-aware (`Interl`), matching
the paper's convention "whenever both polynomials are nonzero".

## Main results

* `PeakFamily.IsReachable.isRealRooted_P`: the abstract form of Theorem
  `thm:peak_rr_ferrers`. The total peak polynomial of every family reachable from
  `base` by the recursion is real-rooted as soon as some `A k` is nonzero.
* `PeakFamily.Conditions.next` and `PeakFamily.Conditions.nextBoundary`: the six
  conditions propagate from a family to its next-level family, along a monotone
  map of cut positions or with the extra boundary index.
* `PeakFamily.Conditions.isRealRooted_P`: under the six conditions, the total
  peak polynomial `P = ∑ A k` is real-rooted as soon as some `A k` is nonzero.
* `PeakFamily.Conditions.interl_R_P`: the telescoping Lemma `lem:R_interl_P`.
* `PeakFamily.conditions_base`: the base case of the induction.
* `PeakFamily.Conditions.interl_nextBoundary_A_last_A_castSucc` and its
  companions: the extra boundary index when the width grows from `m` to `m + 1`.

The shift lemma (Lemma `lem:t_minus_1`) is `RealRooted.strictInterl_shift`;
its zero-aware form used here is `interl_add_X_sub_C_one_mul`.

The combinatorial identification of Ferrers-board peak polynomials with this
abstract recursion (Lemma `lem:peakDURecursion`) is not formalized.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.PeakPolynomials

/-! ## Utility lemmas -/

private lemma eval_zero_nonneg {p : ℝ[X]} (hp : HasNonnegCoeffs p) : 0 ≤ p.eval 0 := by
  rw [← coeff_zero_eq_eval_zero]
  exact hp 0

/-- `W = X * D + U` is nonzero when `A = D + U` is nonzero. -/
private lemma X_mul_add_ne_zero {D U : ℝ[X]}
    (hD : HasNonnegCoeffs D) (hU : HasNonnegCoeffs U) (hA : D + U ≠ 0) :
    X * D + U ≠ 0 := by
  rcases eq_or_ne U 0 with rfl | hU0
  · simpa [X_ne_zero] using hA
  · exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hD.X_mul hU hU0

/-- `A = D + U` is nonzero when `W = X * D + U` is nonzero. -/
private lemma add_ne_zero_of_X_mul_add_ne_zero {D U : ℝ[X]}
    (hD : HasNonnegCoeffs D) (hU : HasNonnegCoeffs U) (hW : X * D + U ≠ 0) :
    D + U ≠ 0 := by
  rcases eq_or_ne U 0 with rfl | hU0
  · simpa [X_ne_zero] using hW
  · exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hD hU hU0

/-- Two-term left cone: `h ≪₀ f` and `h ≪₀ g` give `h ≪₀ f + g`. -/
private lemma interl_add_left {f g h : ℝ[X]}
    (hf : Interl h f) (hg : Interl h g)
    (hf_nn : HasNonnegCoeffs f) (hg_nn : HasNonnegCoeffs g) :
    Interl h (f + g) := by
  simpa using Interl.sum_left_of_common_left_of_nonneg [f, g] h
    (by simp [hf, hg]) (by simp [hf_nn, hg_nn])

/-- Two-term right cone: `f ≪₀ h` and `g ≪₀ h` give `f + g ≪₀ h`. -/
private lemma interl_add_right {f g h : ℝ[X]}
    (hf : Interl f h) (hg : Interl g h)
    (hf_nn : HasNonnegCoeffs f) (hg_nn : HasNonnegCoeffs g) :
    Interl (f + g) h := by
  simpa [Fin.sum_univ_two] using Interl.finsetSum_right_of_nonneg Finset.univ ![f, g] h
    (by simp [Fin.forall_fin_two, hf, hg]) (by simp [Fin.forall_fin_two, hf_nn, hg_nn])

/-- If `T = H + K` with `H ≪₀ K` and `T` real-rooted, then `H ≪₀ T`. -/
private lemma interl_left_of_eq_add {H K T : ℝ[X]}
    (hT : T = H + K) (hHK : Interl H K)
    (hH_nn : HasNonnegCoeffs H) (hK_nn : HasNonnegCoeffs K) (hT_splits : T.Splits) :
    Interl H T := by
  rcases eq_or_ne H 0 with rfl | hH
  · exact interl_zero_left T
  rcases eq_or_ne K 0 with rfl | hK
  · rw [add_zero] at hT
    exact hT ▸ Interl.refl fun _ => hT_splits
  have hstrict := hHK.toStrictInterl_of_ne hH hK
  rw [hT]
  exact interl_add_left (Interl.refl fun _ => hstrict.1.2) hHK hH_nn hK_nn

/-- Zero-aware form of the shift lemma `strictInterl_shift` for polynomials with
nonnegative coefficients: if `h ≪₀ f`, `f` is real-rooted and `h(0) ≤ f(0)`, then
`f ≪₀ f + (X - 1) * h`. -/
theorem interl_add_X_sub_C_one_mul {f h : ℝ[X]} (hhf : Interl h f)
    (hf_nn : HasNonnegCoeffs f) (hh_nn : HasNonnegCoeffs h) (hf : f.Splits)
    (heval : h.eval 0 ≤ f.eval 0) :
    Interl f (f + (X - C 1) * h) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact interl_zero_left _
  rcases eq_or_ne h 0 with rfl | hh0
  · simpa using Interl.refl fun _ => hf
  have hs := hhf.toStrictInterl_of_ne hh0 hf0
  exact (strictInterl_shift hf0 hf hh0 hs.1.2
    (roots_nonpos_of_hasNonnegCoeffs hf_nn) (roots_nonpos_of_hasNonnegCoeffs hh_nn)
    (hf_nn.pos_leadingCoeff hf0) (hh_nn.pos_leadingCoeff hh0) hs heval).toInterl

/-! ## Core definitions -/

/-- A peak family: polynomials `D k`, `U k` with nonnegative coefficients. -/
structure PeakFamily (m : ℕ) where
  /-- The refined peak polynomial `D_k`. -/
  D : Fin m → ℝ[X]
  /-- The refined peak polynomial `U_k`. -/
  U : Fin m → ℝ[X]
  hasNonnegCoeffs_D : ∀ k, HasNonnegCoeffs (D k)
  hasNonnegCoeffs_U : ∀ k, HasNonnegCoeffs (U k)

namespace PeakFamily

variable {m : ℕ} (F : PeakFamily m)

/-- `A k = D k + U k`. -/
def A (k : Fin m) : ℝ[X] := F.D k + F.U k
/-- `W k = X * D k + U k`. -/
def W (k : Fin m) : ℝ[X] := X * F.D k + F.U k
/-- The head sum `S k = ∑_{j < k} A j`. -/
def S (k : Fin m) : ℝ[X] := (Finset.univ.filter (· < k)).sum F.A
/-- The tail sum `T k = ∑_{j ≥ k} W j`. -/
def T (k : Fin m) : ℝ[X] := (Finset.univ.filter (k ≤ ·)).sum F.W
/-- The total peak polynomial `P = ∑ A k`. -/
def P : ℝ[X] := Finset.univ.sum F.A

lemma hasNonnegCoeffs_A (k : Fin m) : HasNonnegCoeffs (F.A k) :=
  (F.hasNonnegCoeffs_D k).add (F.hasNonnegCoeffs_U k)
lemma hasNonnegCoeffs_W (k : Fin m) : HasNonnegCoeffs (F.W k) :=
  (F.hasNonnegCoeffs_D k).X_mul.add (F.hasNonnegCoeffs_U k)
lemma hasNonnegCoeffs_S (k : Fin m) : HasNonnegCoeffs (F.S k) :=
  hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_A i)
lemma hasNonnegCoeffs_T (k : Fin m) : HasNonnegCoeffs (F.T k) :=
  hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_W i)
lemma hasNonnegCoeffs_P : HasNonnegCoeffs F.P :=
  hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_A i)

lemma W_sub_A (k : Fin m) : F.W k - F.A k = (X - C 1) * F.D k := by
  simp [W, A]; ring
lemma X_mul_A_sub_W (k : Fin m) : X * F.A k - F.W k = (X - C 1) * F.U k := by
  simp [W, A]; ring

/-! ## The six interlacing conditions -/

/-- The six interlacing conditions (a)--(f) of Theorem `thm:peak_rr_ferrers`,
with zero-based indices. -/
structure Conditions (F : PeakFamily m) : Prop where
  /-- (a) `D_j ≪₀ U_l` for all `j, l`. -/
  interl_D_U : ∀ j l : Fin m, Interl (F.D j) (F.U l)
  /-- (b) `U_j ≪₀ U_l` for `j ≤ l`. -/
  interl_U_U_of_le : ∀ j l : Fin m, j ≤ l → Interl (F.U j) (F.U l)
  /-- (c) `A_j ≪₀ W_l` for all `j, l`. -/
  interl_A_W : ∀ j l : Fin m, Interl (F.A j) (F.W l)
  /-- (d) reversed DD: `D_j ≪₀ D_{j'}` for `j' < j`. -/
  interl_D_D_of_lt : ∀ j j' : Fin m, j' < j → Interl (F.D j) (F.D j')
  /-- (e) reversed AA: `A_j ≪₀ A_{j'}` for `j' < j`. -/
  interl_A_A_of_lt : ∀ j j' : Fin m, j' < j → Interl (F.A j) (F.A j')
  /-- (f) `W_j ≪₀ W_l` for `j ≤ l`. -/
  interl_W_W_of_le : ∀ j l : Fin m, j ≤ l → Interl (F.W j) (F.W l)

/-! ## The next-level family -/

/-- The next-level family along a map `ι` of cut positions:
`D⁺ k = S (ι k)` and `U⁺ k = T (ι k)`. -/
def next (F : PeakFamily m) (m' : ℕ) (ι : Fin m' → Fin m) : PeakFamily m' where
  D k := F.S (ι k)
  U k := F.T (ι k)
  hasNonnegCoeffs_D k := F.hasNonnegCoeffs_S (ι k)
  hasNonnegCoeffs_U k := F.hasNonnegCoeffs_T (ι k)

variable {m' : ℕ} {ι : Fin m' → Fin m}

@[simp] lemma next_D (k : Fin m') : (F.next m' ι).D k = F.S (ι k) := rfl
@[simp] lemma next_U (k : Fin m') : (F.next m' ι).U k = F.T (ι k) := rfl
@[simp] lemma next_A (k : Fin m') :
    (F.next m' ι).A k = F.S (ι k) + F.T (ι k) := by simp [next, A]
@[simp] lemma next_W (k : Fin m') :
    (F.next m' ι).W k = X * F.S (ι k) + F.T (ι k) := by simp [next, W]

/-! ## Boundary-aware next family

For the literal Ferrers-board recursion when the width grows from `m` to `m + 1`,
there is one additional cut position. At that boundary index, the paper has
`D⁺ = P` and `U⁺ = 0`. The family below packages exactly that extra term. -/

/-- `D⁺` of the boundary-aware next family. -/
def boundaryD (F : PeakFamily m) (k : Fin (m + 1)) : ℝ[X] :=
  if hk : (k : ℕ) < m then F.S ⟨k, hk⟩ else F.P

/-- `U⁺` of the boundary-aware next family. -/
def boundaryU (F : PeakFamily m) (k : Fin (m + 1)) : ℝ[X] :=
  if hk : (k : ℕ) < m then F.T ⟨k, hk⟩ else 0

/-- The next-level family when the width grows from `m` to `m + 1`. -/
def nextBoundary (F : PeakFamily m) : PeakFamily (m + 1) where
  D := F.boundaryD
  U := F.boundaryU
  hasNonnegCoeffs_D k := by
    by_cases hk : (k : ℕ) < m
    · simpa [boundaryD, hk] using F.hasNonnegCoeffs_S ⟨k, hk⟩
    · simpa [boundaryD, hk] using F.hasNonnegCoeffs_P
  hasNonnegCoeffs_U k := by
    by_cases hk : (k : ℕ) < m
    · simpa [boundaryU, hk] using F.hasNonnegCoeffs_T ⟨k, hk⟩
    · simpa [boundaryU, hk] using hasNonnegCoeffs_zero

@[simp] lemma nextBoundary_D_castSucc (k : Fin m) :
    (F.nextBoundary).D (Fin.castSucc k) = F.S k := by
  simp [nextBoundary, boundaryD, k.is_lt]

@[simp] lemma nextBoundary_U_castSucc (k : Fin m) :
    (F.nextBoundary).U (Fin.castSucc k) = F.T k := by
  simp [nextBoundary, boundaryU, k.is_lt]

@[simp] lemma nextBoundary_D_last :
    (F.nextBoundary).D (Fin.last m) = F.P := by
  simp [nextBoundary, boundaryD, Fin.last]

@[simp] lemma nextBoundary_U_last :
    (F.nextBoundary).U (Fin.last m) = 0 := by
  simp [nextBoundary, boundaryU, Fin.last]

@[simp] lemma nextBoundary_A_castSucc (k : Fin m) :
    (F.nextBoundary).A (Fin.castSucc k) = F.S k + F.T k := by
  simp [A]

@[simp] lemma nextBoundary_W_castSucc (k : Fin m) :
    (F.nextBoundary).W (Fin.castSucc k) = X * F.S k + F.T k := by
  simp [W]

@[simp] lemma nextBoundary_A_last :
    (F.nextBoundary).A (Fin.last m) = F.P := by
  simp [A]

@[simp] lemma nextBoundary_W_last :
    (F.nextBoundary).W (Fin.last m) = X * F.P := by
  simp [W]

/-! ## Algebraic identities at next level

The key identities expressing next-level differences as (X-1) times sums.
These are pure algebra from the definitions + W_j - A_j = (X-1)D_j. -/

/-- Head sum splitting: Σ_{j<b} f - Σ_{j<a} f = Σ_{a≤j<b} f. -/
private lemma sum_filter_Icc_sub {f : Fin m → ℝ[X]} {a b : Fin m} (hab : a ≤ b) :
    (Finset.univ.filter (· < b)).sum f - (Finset.univ.filter (· < a)).sum f =
    (Finset.univ.filter (fun j => a ≤ j ∧ j < b)).sum f := by
  have hsub : Finset.univ.filter (· < a) ⊆ Finset.univ.filter (· < b) := by
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact lt_of_lt_of_le h hab
  have hEq :
      Finset.univ.filter (· < b) \ Finset.univ.filter (· < a) =
        Finset.univ.filter (fun j => a ≤ j ∧ j < b) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  calc
    (Finset.univ.filter (· < b)).sum f - (Finset.univ.filter (· < a)).sum f
        = ((Finset.univ.filter (· < b) \ Finset.univ.filter (· < a)).sum f +
            (Finset.univ.filter (· < a)).sum f) - (Finset.univ.filter (· < a)).sum f := by
            rw [Finset.sum_sdiff hsub]
    _ = (Finset.univ.filter (· < b) \ Finset.univ.filter (· < a)).sum f := by abel
    _ = (Finset.univ.filter (fun j => a ≤ j ∧ j < b)).sum f := by rw [hEq]

/-- Tail sum splitting: Σ_{j≥a} f - Σ_{j≥b} f = Σ_{a≤j<b} f. -/
private lemma sum_filter_tail_sub {f : Fin m → ℝ[X]} {a b : Fin m} (hab : a ≤ b) :
    (Finset.univ.filter (a ≤ ·)).sum f - (Finset.univ.filter (b ≤ ·)).sum f =
    (Finset.univ.filter (fun j => a ≤ j ∧ j < b)).sum f := by
  have hsub : Finset.univ.filter (b ≤ ·) ⊆ Finset.univ.filter (a ≤ ·) := by
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact le_trans hab h
  have hEq :
      Finset.univ.filter (a ≤ ·) \ Finset.univ.filter (b ≤ ·) =
        Finset.univ.filter (fun j => a ≤ j ∧ j < b) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  calc
    (Finset.univ.filter (a ≤ ·)).sum f - (Finset.univ.filter (b ≤ ·)).sum f
        = ((Finset.univ.filter (a ≤ ·) \ Finset.univ.filter (b ≤ ·)).sum f +
            (Finset.univ.filter (b ≤ ·)).sum f) - (Finset.univ.filter (b ≤ ·)).sum f := by
            rw [Finset.sum_sdiff hsub]
    _ = (Finset.univ.filter (a ≤ ·) \ Finset.univ.filter (b ≤ ·)).sum f := by abel
    _ = (Finset.univ.filter (fun j => a ≤ j ∧ j < b)).sum f := by rw [hEq]

/-- `A⁺_{k'} - A⁺_k = (X - 1) · ∑_{ι k' ≤ j < ι k} D_j` when `ι k' ≤ ι k`.

Derivation: A_{k'}^+ - A_k^+ = (S_{k'} + T_{k'}) - (S_k + T_k)
= (T_{k'} - T_k) - (S_k - S_{k'})
= Σ_{k'≤j<k} W_j - Σ_{k'≤j<k} A_j = Σ (W_j - A_j) = Σ (X-1)D_j. -/
lemma next_A_sub_next_A (k k' : Fin m') (hkk' : ι k' ≤ ι k) :
    (F.next m' ι).A k' - (F.next m' ι).A k =
    (X - C 1) * (Finset.univ.filter (fun j => ι k' ≤ j ∧ j < ι k)).sum F.D := by
  simp only [next_A, S, T]
  have hT := sum_filter_tail_sub (f := F.W) hkk'
  have hS := sum_filter_Icc_sub (f := F.A) hkk'
  have hWmA :
      (Finset.univ.filter (fun j => ι k' ≤ j ∧ j < ι k)).sum F.W -
      (Finset.univ.filter (fun j => ι k' ≤ j ∧ j < ι k)).sum F.A =
      (X - C 1) * (Finset.univ.filter (fun j => ι k' ≤ j ∧ j < ι k)).sum F.D :=
    (Finset.sum_sub_distrib F.W F.A).symm |>.trans
      ((Finset.sum_congr rfl (fun j _ => F.W_sub_A j)).trans
        (Finset.mul_sum _ F.D (X - C 1)).symm)
  have rearr :
      (Finset.univ.filter (· < ι k')).sum F.A +
        (Finset.univ.filter (ι k' ≤ ·)).sum F.W -
      ((Finset.univ.filter (· < ι k)).sum F.A +
        (Finset.univ.filter (ι k ≤ ·)).sum F.W) =
      ((Finset.univ.filter (ι k' ≤ ·)).sum F.W -
        (Finset.univ.filter (ι k ≤ ·)).sum F.W) -
      ((Finset.univ.filter (· < ι k)).sum F.A -
        (Finset.univ.filter (· < ι k')).sum F.A) := by ring
  rw [rearr, hT, hS]
  exact hWmA

/-- `W⁺_l - W⁺_k = (X - 1) · ∑_{ι k ≤ j < ι l} U_j` when `ι k ≤ ι l`.

Derivation: W_l^+ - W_k^+ = (X·S_l + T_l) - (X·S_k + T_k)
= X·(S_l - S_k) + (T_l - T_k)
= X·Σ_{k≤j<l} A_j - Σ_{k≤j<l} W_j = Σ (X·A_j - W_j) = Σ (X-1)U_j. -/
lemma next_W_sub_next_W (k l : Fin m') (hkl : ι k ≤ ι l) :
    (F.next m' ι).W l - (F.next m' ι).W k =
    (X - C 1) * (Finset.univ.filter (fun j => ι k ≤ j ∧ j < ι l)).sum F.U := by
  simp only [next_W, S, T]
  have hS := sum_filter_Icc_sub (f := F.A) hkl
  have hT := sum_filter_tail_sub (f := F.W) hkl
  have hXAmW :
      X * (Finset.univ.filter (fun j => ι k ≤ j ∧ j < ι l)).sum F.A -
      (Finset.univ.filter (fun j => ι k ≤ j ∧ j < ι l)).sum F.W =
      (X - C 1) * (Finset.univ.filter (fun j => ι k ≤ j ∧ j < ι l)).sum F.U := by
    have h1 : X * (Finset.univ.filter (fun j => ι k ≤ j ∧ j < ι l)).sum F.A =
        (Finset.univ.filter (fun j => ι k ≤ j ∧ j < ι l)).sum (fun j => X * F.A j) :=
      Finset.mul_sum _ F.A X
    rw [h1]
    exact (Finset.sum_sub_distrib (fun j => X * F.A j) F.W).symm |>.trans
      ((Finset.sum_congr rfl (fun j _ => F.X_mul_A_sub_W j)).trans
        (Finset.mul_sum _ F.U (X - C 1)).symm)
  have rearr :
      (X * (Finset.univ.filter (· < ι l)).sum F.A +
        (Finset.univ.filter (ι l ≤ ·)).sum F.W) -
      (X * (Finset.univ.filter (· < ι k)).sum F.A +
        (Finset.univ.filter (ι k ≤ ·)).sum F.W) =
      X * ((Finset.univ.filter (· < ι l)).sum F.A -
        (Finset.univ.filter (· < ι k)).sum F.A) -
      ((Finset.univ.filter (ι k ≤ ·)).sum F.W -
        (Finset.univ.filter (ι l ≤ ·)).sum F.W) := by ring
  rw [rearr, hS, hT]
  exact hXAmW

/-- The key observation of the paper: `W⁺_l - A⁺_k = (X - 1) · H` for some `H` with
nonnegative coefficients. -/
lemma exists_next_W_sub_next_A_eq_mul (k l : Fin m') :
    ∃ H : ℝ[X],
      (F.next m' ι).W l - (F.next m' ι).A k = (X - C 1) * H ∧
      HasNonnegCoeffs H := by
  rcases le_or_gt (ι k) (ι l) with hkl | hlk
  · -- Case k ≤ l: W_l^+ - A_k^+ = (W_l^+ - W_k^+) + (W_k^+ - A_k^+)
    let band := Finset.univ.filter (fun j : Fin m => ι k ≤ j ∧ j < ι l)
    refine ⟨F.S (ι k) + band.sum F.U, ?_, (F.hasNonnegCoeffs_S _).add
      (hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i))⟩
    have hWW := F.next_W_sub_next_W (ι := ι) k l hkl
    have hWA : (F.next m' ι).W k - (F.next m' ι).A k =
        (X - C 1) * F.S (ι k) := by
      have := (F.next m' ι).W_sub_A k; simp only [next_D] at this; exact this
    have hsplit : (F.next m' ι).W l - (F.next m' ι).A k =
        ((F.next m' ι).W l - (F.next m' ι).W k) +
        ((F.next m' ι).W k - (F.next m' ι).A k) := by ring
    rw [hsplit, hWW, hWA, ← mul_add, add_comm]
  · -- Case k > l: W_l^+ - A_k^+ = (W_l^+ - A_l^+) + (A_l^+ - A_k^+)
    let band := Finset.univ.filter (fun j : Fin m => ι l ≤ j ∧ j < ι k)
    refine ⟨F.S (ι l) + band.sum F.D, ?_, (F.hasNonnegCoeffs_S _).add
      (hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i))⟩
    have hAA := F.next_A_sub_next_A (ι := ι) k l (le_of_lt hlk)
    have hWA : (F.next m' ι).W l - (F.next m' ι).A l =
        (X - C 1) * F.S (ι l) := by
      have := (F.next m' ι).W_sub_A l; simp only [next_D] at this; exact this
    have hsplit : (F.next m' ι).W l - (F.next m' ι).A k =
        ((F.next m' ι).W l - (F.next m' ι).A l) +
        ((F.next m' ι).A l - (F.next m' ι).A k) := by ring
    rw [hsplit, hAA, hWA, ← mul_add, add_comm]

private lemma sum_filter_Icc_eq_add {f : Fin m → ℝ[X]} {a b : Fin m} (hab : a ≤ b) :
    (Finset.univ.filter (· < b)).sum f =
      (Finset.univ.filter (· < a)).sum f +
      (Finset.univ.filter (fun j => a ≤ j ∧ j < b)).sum f := by
  have h := sum_filter_Icc_sub (f := f) hab
  linear_combination h

private lemma sum_filter_tail_eq_add {f : Fin m → ℝ[X]} {a b : Fin m} (hab : a ≤ b) :
    (Finset.univ.filter (a ≤ ·)).sum f =
      (Finset.univ.filter (fun j => a ≤ j ∧ j < b)).sum f +
      (Finset.univ.filter (b ≤ ·)).sum f := by
  have h := sum_filter_tail_sub (f := f) hab
  linear_combination h

private lemma sum_A_eq_sum_D_add_sum_U (s : Finset (Fin m)) :
    s.sum F.A = s.sum F.D + s.sum F.U :=
  Finset.sum_add_distrib

private lemma sum_W_eq_sum_X_mul_D_add_sum_U (s : Finset (Fin m)) :
    s.sum F.W = s.sum (fun i => X * F.D i) + s.sum F.U :=
  Finset.sum_add_distrib

private lemma S_add_sum_le_A (s : Fin m) :
    F.S s + (Finset.univ.filter (s ≤ ·)).sum F.A = F.P := by
  simpa [P, S, not_lt] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i < s) F.A)

/-- Head sum enlargement: `S_b ≪₀ S_a` when `S_a` is real-rooted and each extra
summand `f_i` (`a ≤ i < b`) satisfies `f_i ≪₀ S_a`. -/
private lemma interl_larger_head_sum {f : Fin m → ℝ[X]} {a b : Fin m} (hab : a ≤ b)
    (hself : ((Finset.univ.filter (· < a)).sum f).Splits)
    (hextra : ∀ i : Fin m, a ≤ i → i < b →
      Interl (f i) ((Finset.univ.filter (· < a)).sum f))
    (hnn : ∀ i : Fin m, HasNonnegCoeffs (f i)) :
    Interl ((Finset.univ.filter (· < b)).sum f) ((Finset.univ.filter (· < a)).sum f) := by
  rw [sum_filter_Icc_eq_add hab]
  refine interl_add_right (Interl.refl fun _ => hself) ?_
    (hasNonnegCoeffs_finsetSum _ _ (fun i _ => hnn i))
    (hasNonnegCoeffs_finsetSum _ _ (fun i _ => hnn i))
  exact Interl.finsetSum_right_of_nonneg _ f _ (fun i hi => by
    obtain ⟨hai, hib⟩ := (Finset.mem_filter.mp hi).2
    exact hextra i hai hib) (fun i _ => hnn i)

/-- Tail sum enlargement: `T_a ≪₀ T_b` when `T_b` is real-rooted and each extra
summand `f_i` (`a ≤ i < b`) satisfies `f_i ≪₀ T_b`. -/
private lemma interl_larger_tail_sum {f : Fin m → ℝ[X]} {a b : Fin m} (hab : a ≤ b)
    (hself : ((Finset.univ.filter (b ≤ ·)).sum f).Splits)
    (hextra : ∀ i : Fin m, a ≤ i → i < b →
      Interl (f i) ((Finset.univ.filter (b ≤ ·)).sum f))
    (hnn : ∀ i : Fin m, HasNonnegCoeffs (f i)) :
    Interl ((Finset.univ.filter (a ≤ ·)).sum f) ((Finset.univ.filter (b ≤ ·)).sum f) := by
  rw [sum_filter_tail_eq_add hab, add_comm]
  refine interl_add_right (Interl.refl fun _ => hself) ?_
    (hasNonnegCoeffs_finsetSum _ _ (fun i _ => hnn i))
    (hasNonnegCoeffs_finsetSum _ _ (fun i _ => hnn i))
  exact Interl.finsetSum_right_of_nonneg _ f _ (fun i hi => by
    obtain ⟨hai, hib⟩ := (Finset.mem_filter.mp hi).2
    exact hextra i hai hib) (fun i _ => hnn i)

/-! ## Telescoping and boundary definitions -/

/-- The telescoping polynomial `R = ∑_{s ≤ bound} ∑_{j ≥ s} D_j` of
Lemma `lem:R_interl_P`. -/
def R (bound : Fin m) : ℝ[X] :=
  (Finset.univ.filter (· ≤ bound)).sum
    (fun s => (Finset.univ.filter (s ≤ ·)).sum F.D)

lemma nextBoundary_A_castSucc_eq (k : Fin m) :
    (F.nextBoundary).A (Fin.castSucc k) =
      F.P + (X - C 1) * ((Finset.univ.filter (k ≤ ·)).sum F.D) := by
  rw [nextBoundary_A_castSucc, ← F.S_add_sum_le_A k, F.sum_A_eq_sum_D_add_sum_U, T,
    F.sum_W_eq_sum_X_mul_D_add_sum_U, ← Finset.mul_sum, C_1]
  ring

/-! ## Consequences of the six conditions -/

variable {F}

namespace Conditions

lemma interl_U_X_mul_D (hC : F.Conditions) (i k : Fin m) :
    Interl (F.U i) (X * F.D k) :=
  interl_mul_X_of_interl (hC.interl_D_U k i) (F.hasNonnegCoeffs_D k) (F.hasNonnegCoeffs_U i)

lemma interl_U_W_of_lt (hC : F.Conditions) {i k : Fin m} (hik : i < k) :
    Interl (F.U i) (F.W k) :=
  interl_add_left (hC.interl_U_X_mul_D i k) (hC.interl_U_U_of_le i k hik.le)
    (F.hasNonnegCoeffs_D k).X_mul (F.hasNonnegCoeffs_U k)

lemma interl_A_U_of_lt (hC : F.Conditions) {i k : Fin m} (hik : i < k) :
    Interl (F.A i) (F.U k) :=
  interl_add_right (hC.interl_D_U i k) (hC.interl_U_U_of_le i k hik.le)
    (F.hasNonnegCoeffs_D i) (F.hasNonnegCoeffs_U i)

lemma interl_A_X_mul_D_of_lt (hC : F.Conditions) {i k : Fin m} (hik : i < k) :
    Interl (F.A i) (X * F.D k) :=
  interl_add_right
    (interl_mul_X_of_interl (hC.interl_D_D_of_lt k i hik) (F.hasNonnegCoeffs_D k)
      (F.hasNonnegCoeffs_D i))
    (hC.interl_U_X_mul_D i k) (F.hasNonnegCoeffs_D i) (F.hasNonnegCoeffs_U i)

lemma interl_D_W_of_lt (hC : F.Conditions) {i k : Fin m} (hik : i < k) :
    Interl (F.D i) (F.W k) :=
  interl_add_left
    (interl_mul_X_of_interl (hC.interl_D_D_of_lt k i hik) (F.hasNonnegCoeffs_D k)
      (F.hasNonnegCoeffs_D i))
    (hC.interl_D_U i k) (F.hasNonnegCoeffs_D k).X_mul (F.hasNonnegCoeffs_U k)

lemma interl_P_W (hC : F.Conditions) (l : Fin m) : Interl F.P (F.W l) :=
  Interl.finsetSum_right_of_nonneg Finset.univ F.A (F.W l)
    (fun i _ => hC.interl_A_W i l) (fun i _ => F.hasNonnegCoeffs_A i)

lemma interl_P_T (hC : F.Conditions) (l : Fin m) : Interl F.P (F.T l) :=
  Interl.finsetSum_left_of_nonneg F.P _ F.W (fun i _ => hC.interl_P_W i)
    (fun i _ => F.hasNonnegCoeffs_W i)

/-! ### Real-rootedness of partial sums

The paper treats `S_k`, `T_k`, `A⁺_k` and `W⁺_k` as real-rooted without comment.
Here each of them is shown to split by finding a nonzero polynomial in proper
position with it. -/

/-- Each head sum `S_k` is real-rooted (or zero). -/
theorem splits_S (hC : F.Conditions) (k : Fin m) : (F.S k).Splits := by
  rcases eq_or_ne (F.S k) 0 with hS | hS
  · rw [hS]; exact Splits.zero
  obtain ⟨i, -, hAi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hSW : Interl (F.S k) (F.W i) :=
    Interl.finsetSum_right_of_nonneg _ F.A (F.W i)
      (fun j _ => hC.interl_A_W j i) (fun j _ => F.hasNonnegCoeffs_A j)
  exact (hSW.toStrictInterl_of_ne hS
    (X_mul_add_ne_zero (F.hasNonnegCoeffs_D i) (F.hasNonnegCoeffs_U i) hAi)).1.2

/-- Each tail sum `T_k` is real-rooted (or zero). -/
theorem splits_T (hC : F.Conditions) (k : Fin m) : (F.T k).Splits := by
  rcases eq_or_ne (F.T k) 0 with hT | hT
  · rw [hT]; exact Splits.zero
  obtain ⟨i, -, hWi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  have hAT : Interl (F.A i) (F.T k) :=
    Interl.finsetSum_left_of_nonneg (F.A i) _ F.W
      (fun j _ => hC.interl_A_W i j) (fun j _ => F.hasNonnegCoeffs_W j)
  exact (hAT.toStrictInterl_of_ne
    (add_ne_zero_of_X_mul_add_ne_zero (F.hasNonnegCoeffs_D i) (F.hasNonnegCoeffs_U i) hWi)
    hT).2.1.2

/-- The total peak polynomial `P` is real-rooted when some `A_k` is nonzero. -/
theorem isRealRooted_P (hC : F.Conditions) (hne : ∃ k : Fin m, F.A k ≠ 0) :
    F.P ≠ 0 ∧ F.P.Splits := by
  obtain ⟨k, hk⟩ := hne
  have hP : F.P ≠ 0 := by
    rw [P, ← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_comm]
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      (hasNonnegCoeffs_finsetSum _ _ fun i _ => F.hasNonnegCoeffs_A i)
      (F.hasNonnegCoeffs_A k) hk
  exact (hC.interl_P_W k).toStrictInterl_of_ne hP
    (X_mul_add_ne_zero (F.hasNonnegCoeffs_D k) (F.hasNonnegCoeffs_U k) hk) |>.1

/-- The total peak polynomial `P` is real-rooted (or zero). -/
theorem splits_P (hC : F.Conditions) : F.P.Splits := by
  rcases eq_or_ne F.P 0 with hP | hP
  · rw [hP]; exact Splits.zero
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  exact (hC.isRealRooted_P ⟨k, hk⟩).2

lemma interl_P_S (hC : F.Conditions) (s : Fin m) : Interl F.P (F.S s) := by
  have htail : Interl ((Finset.univ.filter (s ≤ ·)).sum F.A) (F.S s) := by
    refine Interl.finsetSum_right_of_nonneg _ F.A (F.S s) (fun i hi => ?_)
      (fun i _ => F.hasNonnegCoeffs_A i)
    refine Interl.finsetSum_left_of_nonneg (F.A i) _ F.A (fun r hr => ?_)
      (fun r _ => F.hasNonnegCoeffs_A r)
    exact hC.interl_A_A_of_lt i r
      (lt_of_lt_of_le (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hi).2)
  rw [← F.S_add_sum_le_A s]
  exact interl_add_right (Interl.refl fun _ => hC.splits_S s) htail (F.hasNonnegCoeffs_S s)
    (hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_A i))

/-! ## Propagation of conditions

Each condition at λ+ is proved from the conditions at λ.
The proofs use the right cone, left cone, Wagner 3, and shift lemma. -/

/-- **(a) DU at λ+**: `S_k ≪₀ T_l`.
AW → left cone (`A_j ≪₀ T_l`) → right cone (`S_k ≪₀ T_l`). -/
theorem interl_next_D_U (hC : F.Conditions) (j l : Fin m') :
    Interl ((F.next m' ι).D j) ((F.next m' ι).U l) :=
  show Interl (F.S (ι j)) (F.T (ι l)) from Interl.finsetSum_right_of_nonneg _ F.A (F.T (ι l))
    (fun i _ => Interl.finsetSum_left_of_nonneg (F.A i) _ F.W
      (fun j' _ => hC.interl_A_W i j') (fun j' _ => F.hasNonnegCoeffs_W j'))
    (fun i _ => F.hasNonnegCoeffs_A i)

/-- Each next-level `A⁺_j = S + T` is real-rooted (or zero). -/
theorem splits_next_A (hC : F.Conditions) (j : Fin m') :
    ((F.next m' ι).A j).Splits := by
  rw [next_A]
  rcases eq_or_ne (F.S (ι j)) 0 with hS0 | hS
  · simpa [hS0] using hC.splits_T (ι j)
  rcases eq_or_ne (F.S (ι j) + F.T (ι j)) 0 with h0 | h0
  · rw [h0]; exact Splits.zero
  have hST : Interl (F.S (ι j)) (F.S (ι j) + F.T (ι j)) :=
    interl_add_left (Interl.refl fun _ => hC.splits_S _) (hC.interl_next_D_U (ι := ι) j j)
      (F.hasNonnegCoeffs_S _) (F.hasNonnegCoeffs_T _)
  exact (hST.toStrictInterl_of_ne hS h0).2.1.2

/-- Each next-level `W⁺_j = X * S + T` is real-rooted (or zero). -/
theorem splits_next_W (hC : F.Conditions) (j : Fin m') :
    ((F.next m' ι).W j).Splits := by
  rw [next_W]
  rcases eq_or_ne (F.T (ι j)) 0 with hT0 | hT
  · rw [hT0, add_zero]
    exact Splits.X.mul (hC.splits_S _)
  rcases eq_or_ne (X * F.S (ι j) + F.T (ι j)) 0 with h0 | h0
  · rw [h0]; exact Splits.zero
  have hDU : Interl (F.S (ι j)) (F.T (ι j)) := hC.interl_next_D_U (ι := ι) j j
  have hTW : Interl (F.T (ι j)) (X * F.S (ι j) + F.T (ι j)) :=
    interl_add_left
      (interl_mul_X_of_interl hDU (F.hasNonnegCoeffs_S _) (F.hasNonnegCoeffs_T _))
      (Interl.refl fun _ => hC.splits_T _) (F.hasNonnegCoeffs_S _).X_mul
      (F.hasNonnegCoeffs_T _)
  exact (hTW.toStrictInterl_of_ne hT h0).2.1.2

/-- **(b) UU at λ+**: `T_j ≪₀ T_l` for `j ≤ l`.
`T_j = T_l + extra W`'s; each extra `W_i ≪₀ T_l` by left cone from WW.
Right cone: `T_j ≪₀ T_l`. -/
theorem interl_next_U_U_of_le (hC : F.Conditions) (hι : Monotone ι) (j l : Fin m')
    (hjl : j ≤ l) :
    Interl ((F.next m' ι).U j) ((F.next m' ι).U l) :=
  interl_larger_tail_sum (hι hjl) (hC.splits_T (ι l))
    (fun i _ hib => Interl.finsetSum_left_of_nonneg (F.W i) _ F.W
      (fun j' hj' => hC.interl_W_W_of_le i j'
        (le_of_lt (lt_of_lt_of_le hib (Finset.mem_filter.mp hj').2)))
      (fun j' _ => F.hasNonnegCoeffs_W j'))
    F.hasNonnegCoeffs_W

/-- **(c) AW at λ+**: `A⁺_j ≪₀ W⁺_l`.
The key step: `W⁺_l = A⁺_j + (X - 1) · H` and the shift lemma reduces the claim to
`H ≪₀ A⁺_j`, proved separately for `ι j ≤ ι l` and `ι l < ι j`. -/
theorem interl_next_A_W (hC : F.Conditions) (j l : Fin m') :
    Interl ((F.next m' ι).A j) ((F.next m' ι).W l) := by
  have hDU_next : ∀ j l : Fin m', Interl (F.S (ι j)) (F.T (ι l)) :=
    fun j l => hC.interl_next_D_U j l
  rcases le_or_gt (ι j) (ι l) with hjl | hlj
  · let band := Finset.univ.filter (fun i : Fin m => ι j ≤ i ∧ i < ι l)
    let bandXD : ℝ[X] := band.sum (fun i => X * F.D i)
    let H : ℝ[X] := F.S (ι j) + band.sum F.U
    let K : ℝ[X] := bandXD + F.T (ι l)
    have hT_eq : F.T (ι j) = band.sum F.W + F.T (ι l) := by
      simpa [T, band] using sum_filter_tail_eq_add (f := F.W) hjl
    have hbandW : band.sum F.W = bandXD + band.sum F.U :=
      F.sum_W_eq_sum_X_mul_D_add_sum_U band
    have hA_eq : (F.next m' ι).A j = H + K := by
      simp [next_A, H, K, hT_eq, hbandW]
      ring
    have hWA : (F.next m' ι).W j - (F.next m' ι).A j =
        (X - C 1) * F.S (ι j) := by
      simpa [next_D] using (F.next m' ι).W_sub_A j
    have hdiff : (F.next m' ι).W l - (F.next m' ι).A j = (X - C 1) * H := by
      have hWW := F.next_W_sub_next_W (ι := ι) j l hjl
      have hsplit : (F.next m' ι).W l - (F.next m' ι).A j =
          ((F.next m' ι).W l - (F.next m' ι).W j) +
          ((F.next m' ι).W j - (F.next m' ι).A j) := by
        ring
      rw [hsplit, hWW, hWA, ← mul_add]
      simp [band, H, add_comm]
    have hW_eq : (F.next m' ι).W l =
        (F.next m' ι).A j + (X - C 1) * H := by
      linear_combination hdiff
    have hbandXD_nn : HasNonnegCoeffs bandXD :=
      hasNonnegCoeffs_finsetSum _ _ (fun i _ => (F.hasNonnegCoeffs_D i).X_mul)
    have hbandU_nn : HasNonnegCoeffs (band.sum F.U) :=
      hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i)
    have hH_nn : HasNonnegCoeffs H := (F.hasNonnegCoeffs_S (ι j)).add hbandU_nn
    have hK_nn : HasNonnegCoeffs K := hbandXD_nn.add (F.hasNonnegCoeffs_T (ι l))
    have hS_bandXD : Interl (F.S (ι j)) bandXD := by
      refine Interl.finsetSum_right_of_nonneg _ F.A bandXD (fun i hi => ?_)
        (fun i _ => F.hasNonnegCoeffs_A i)
      refine Interl.finsetSum_left_of_nonneg (F.A i) band (fun r => X * F.D r)
        (fun r hr => ?_) (fun r _ => (F.hasNonnegCoeffs_D r).X_mul)
      exact hC.interl_A_X_mul_D_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hr).2.1)
    have hbandU_bandXD : Interl (band.sum F.U) bandXD :=
      Interl.finsetSum_right_of_nonneg band F.U bandXD
        (fun i _ => Interl.finsetSum_left_of_nonneg (F.U i) band (fun r => X * F.D r)
          (fun r _ => hC.interl_U_X_mul_D i r) (fun r _ => (F.hasNonnegCoeffs_D r).X_mul))
        (fun i _ => F.hasNonnegCoeffs_U i)
    have hbandU_Tl : Interl (band.sum F.U) (F.T (ι l)) := by
      refine Interl.finsetSum_right_of_nonneg band F.U (F.T (ι l)) (fun i hi => ?_)
        (fun i _ => F.hasNonnegCoeffs_U i)
      refine Interl.finsetSum_left_of_nonneg (F.U i) _ F.W (fun r hr => ?_)
        (fun r _ => F.hasNonnegCoeffs_W r)
      exact hC.interl_U_W_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2.2 (Finset.mem_filter.mp hr).2)
    have hHK : Interl H K :=
      interl_add_right
        (interl_add_left hS_bandXD (hDU_next j l) hbandXD_nn (F.hasNonnegCoeffs_T (ι l)))
        (interl_add_left hbandU_bandXD hbandU_Tl hbandXD_nn (F.hasNonnegCoeffs_T (ι l)))
        (F.hasNonnegCoeffs_S (ι j)) hbandU_nn
    have hH_interl : Interl H ((F.next m' ι).A j) :=
      interl_left_of_eq_add hA_eq hHK hH_nn hK_nn (hC.splits_next_A j)
    have hbound : H.eval 0 ≤ ((F.next m' ι).A j).eval 0 := by
      have := eval_zero_nonneg ((F.next m' ι).hasNonnegCoeffs_W l)
      rw [hW_eq] at this
      simp [eval_add, eval_mul, eval_sub, eval_X] at this ⊢
      linarith
    rw [hW_eq]
    exact interl_add_X_sub_C_one_mul hH_interl ((F.next m' ι).hasNonnegCoeffs_A j) hH_nn
      (hC.splits_next_A j) hbound
  · let band := Finset.univ.filter (fun i : Fin m => ι l ≤ i ∧ i < ι j)
    let H : ℝ[X] := F.S (ι l) + band.sum F.D
    let K : ℝ[X] := band.sum F.U + F.T (ι j)
    have hS_eq : F.S (ι j) = F.S (ι l) + band.sum F.A := by
      simpa [S, band] using sum_filter_Icc_eq_add (f := F.A) (le_of_lt hlj)
    have hA_band : band.sum F.A = band.sum F.D + band.sum F.U :=
      F.sum_A_eq_sum_D_add_sum_U band
    have hA_eq : (F.next m' ι).A j = H + K := by
      simp [next_A, H, K, hS_eq, hA_band]
      ring
    have hAA := F.next_A_sub_next_A (ι := ι) j l (le_of_lt hlj)
    have hWA : (F.next m' ι).W l - (F.next m' ι).A l =
        (X - C 1) * F.S (ι l) := by
      simpa [next_D] using (F.next m' ι).W_sub_A l
    have hdiff : (F.next m' ι).W l - (F.next m' ι).A j = (X - C 1) * H := by
      have hsplit : (F.next m' ι).W l - (F.next m' ι).A j =
          ((F.next m' ι).W l - (F.next m' ι).A l) +
          ((F.next m' ι).A l - (F.next m' ι).A j) := by
        ring
      rw [hsplit, hWA, hAA, ← mul_add]
    have hW_eq : (F.next m' ι).W l =
        (F.next m' ι).A j + (X - C 1) * H := by
      linear_combination hdiff
    have hbandD_nn : HasNonnegCoeffs (band.sum F.D) :=
      hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i)
    have hbandU_nn : HasNonnegCoeffs (band.sum F.U) :=
      hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i)
    have hH_nn : HasNonnegCoeffs H := (F.hasNonnegCoeffs_S (ι l)).add hbandD_nn
    have hK_nn : HasNonnegCoeffs K := hbandU_nn.add (F.hasNonnegCoeffs_T (ι j))
    have hS_bandU : Interl (F.S (ι l)) (band.sum F.U) := by
      refine Interl.finsetSum_right_of_nonneg _ F.A (band.sum F.U) (fun i hi => ?_)
        (fun i _ => F.hasNonnegCoeffs_A i)
      refine Interl.finsetSum_left_of_nonneg (F.A i) band F.U (fun r hr => ?_)
        (fun r _ => F.hasNonnegCoeffs_U r)
      exact hC.interl_A_U_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hr).2.1)
    have hbandD_bandU : Interl (band.sum F.D) (band.sum F.U) :=
      Interl.finsetSum_right_of_nonneg band F.D (band.sum F.U)
        (fun i _ => Interl.finsetSum_left_of_nonneg (F.D i) band F.U
          (fun r _ => hC.interl_D_U i r) (fun r _ => F.hasNonnegCoeffs_U r))
        (fun i _ => F.hasNonnegCoeffs_D i)
    have hbandD_Tj : Interl (band.sum F.D) (F.T (ι j)) := by
      refine Interl.finsetSum_right_of_nonneg band F.D (F.T (ι j)) (fun i hi => ?_)
        (fun i _ => F.hasNonnegCoeffs_D i)
      refine Interl.finsetSum_left_of_nonneg (F.D i) _ F.W (fun r hr => ?_)
        (fun r _ => F.hasNonnegCoeffs_W r)
      exact hC.interl_D_W_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2.2 (Finset.mem_filter.mp hr).2)
    have hHK : Interl H K :=
      interl_add_right
        (interl_add_left hS_bandU (hDU_next l j) hbandU_nn (F.hasNonnegCoeffs_T (ι j)))
        (interl_add_left hbandD_bandU hbandD_Tj hbandU_nn (F.hasNonnegCoeffs_T (ι j)))
        (F.hasNonnegCoeffs_S (ι l)) hbandD_nn
    have hH_interl : Interl H ((F.next m' ι).A j) :=
      interl_left_of_eq_add hA_eq hHK hH_nn hK_nn (hC.splits_next_A j)
    have hbound : H.eval 0 ≤ ((F.next m' ι).A j).eval 0 := by
      have := eval_zero_nonneg ((F.next m' ι).hasNonnegCoeffs_W l)
      rw [hW_eq] at this
      simp [eval_add, eval_mul, eval_sub, eval_X] at this ⊢
      linarith
    rw [hW_eq]
    exact interl_add_X_sub_C_one_mul hH_interl ((F.next m' ι).hasNonnegCoeffs_A j) hH_nn
      (hC.splits_next_A j) hbound

/-- **(d) revDD at λ+**: `S_k ≪₀ S_{k'}` for `k' < k`.
AA_rev → left cone (`A_j ≪₀ S_{k'}`) → right cone (`S_k ≪₀ S_{k'}`). -/
theorem interl_next_D_D_of_lt (hC : F.Conditions) (hι : Monotone ι) (j j' : Fin m')
    (hjj' : j' < j) :
    Interl ((F.next m' ι).D j) ((F.next m' ι).D j') :=
  interl_larger_head_sum (hι hjj'.le) (hC.splits_S (ι j'))
    (fun i hi _ => Interl.finsetSum_left_of_nonneg (F.A i) _ F.A
      (fun i' hi' => hC.interl_A_A_of_lt i i' (lt_of_lt_of_le (Finset.mem_filter.mp hi').2 hi))
      (fun i' _ => F.hasNonnegCoeffs_A i'))
    F.hasNonnegCoeffs_A

/-- **(e) revAA at λ+**: `A⁺_k ≪₀ A⁺_{k'}` for `k' < k`.
Shift lemma: `A⁺_{k'} = A⁺_k + (X - 1) · ∑ D_j`, and `∑ D_j ≪₀ A⁺_k` because each
`D_j` interlaces all parts of `A⁺_k` (via DU, DD_rev and Wagner 3). -/
theorem interl_next_A_A_of_lt (hC : F.Conditions) (hι : Monotone ι) (j j' : Fin m')
    (hjj' : j' < j) :
    Interl ((F.next m' ι).A j) ((F.next m' ι).A j') := by
  let band := Finset.univ.filter (fun i : Fin m => ι j' ≤ i ∧ i < ι j)
  let H := band.sum F.D
  let bandU := band.sum F.U
  let K : ℝ[X] := F.S (ι j') + bandU + F.T (ι j)
  have hident := F.next_A_sub_next_A (ι := ι) j j' (hι hjj'.le)
  have hS_eq : F.S (ι j) = F.S (ι j') + band.sum F.A := by
    simpa [S, band] using sum_filter_Icc_eq_add (f := F.A) (hι hjj'.le)
  have hA_band : band.sum F.A = H + bandU := F.sum_A_eq_sum_D_add_sum_U band
  have hAj_eq : (F.next m' ι).A j = H + K := by
    simp [next_A, K, hS_eq, hA_band]
    ring
  have hH_nn : HasNonnegCoeffs H :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i)
  have hH_interl : Interl H ((F.next m' ι).A j) := by
    have hDi_T : ∀ i ∈ band, Interl (F.D i) (F.T (ι j)) := by
      intro i hi
      obtain ⟨_, hilt⟩ := (Finset.mem_filter.mp hi).2
      exact Interl.finsetSum_left_of_nonneg (F.D i) _ F.W (fun i' hi' => by
        have hi'ge := (Finset.mem_filter.mp hi').2
        exact interl_add_left
          (interl_mul_X_of_interl (hC.interl_D_D_of_lt i' i (lt_of_lt_of_le hilt hi'ge))
            (F.hasNonnegCoeffs_D i') (F.hasNonnegCoeffs_D i))
          (hC.interl_D_U i i') (F.hasNonnegCoeffs_D i').X_mul (F.hasNonnegCoeffs_U i'))
        (fun i' _ => F.hasNonnegCoeffs_W i')
    have hDi_S : ∀ i ∈ band, Interl (F.D i) (F.S (ι j')) := by
      intro i hi
      obtain ⟨hige, _⟩ := (Finset.mem_filter.mp hi).2
      exact Interl.finsetSum_left_of_nonneg (F.D i) _ F.A (fun i' hi' =>
        interl_add_left
          (hC.interl_D_D_of_lt i i' (lt_of_lt_of_le (Finset.mem_filter.mp hi').2 hige))
          (hC.interl_D_U i i') (F.hasNonnegCoeffs_D i') (F.hasNonnegCoeffs_U i'))
        (fun i' _ => F.hasNonnegCoeffs_A i')
    have hH_T := Interl.finsetSum_right_of_nonneg _ F.D (F.T (ι j))
      (fun i hi => hDi_T i hi) (fun i _ => F.hasNonnegCoeffs_D i)
    have hH_S := Interl.finsetSum_right_of_nonneg _ F.D (F.S (ι j'))
      (fun i hi => hDi_S i hi) (fun i _ => F.hasNonnegCoeffs_D i)
    have hH_bandU : Interl H bandU :=
      Interl.finsetSum_right_of_nonneg _ F.D (band.sum F.U)
        (fun i _ => Interl.finsetSum_left_of_nonneg (F.D i) _ F.U
          (fun i' _ => hC.interl_D_U i i') (fun i' _ => F.hasNonnegCoeffs_U i'))
        (fun i _ => F.hasNonnegCoeffs_D i)
    have hbandU_nn : HasNonnegCoeffs bandU :=
      hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i)
    have hSU_nn : HasNonnegCoeffs (F.S (ι j') + bandU) :=
      (F.hasNonnegCoeffs_S (ι j')).add hbandU_nn
    have hK_nn : HasNonnegCoeffs K := hSU_nn.add (F.hasNonnegCoeffs_T (ι j))
    have hHK : Interl H K :=
      interl_add_left (interl_add_left hH_S hH_bandU (F.hasNonnegCoeffs_S (ι j')) hbandU_nn)
        hH_T hSU_nn (F.hasNonnegCoeffs_T (ι j))
    exact interl_left_of_eq_add hAj_eq hHK hH_nn hK_nn (hC.splits_next_A j)
  have hA_eq : (F.next m' ι).A j' = (F.next m' ι).A j + (X - C 1) * H := by
    linear_combination hident
  have hbound : H.eval 0 ≤ ((F.next m' ι).A j).eval 0 := by
    have h1 := eval_zero_nonneg ((F.next m' ι).hasNonnegCoeffs_A j')
    rw [hA_eq, eval_add, eval_mul, eval_sub, eval_X, eval_C] at h1
    linarith
  rw [hA_eq]
  exact interl_add_X_sub_C_one_mul hH_interl ((F.next m' ι).hasNonnegCoeffs_A j) hH_nn
    (hC.splits_next_A j) hbound

/-- **(f) WW at λ+**: `W⁺_k ≪₀ W⁺_l` for `k ≤ l`.
Shift lemma: `W⁺_l = W⁺_k + (X - 1) · ∑ U_j`, and `∑ U_j ≪₀ W⁺_k` because each
`U_j` interlaces `T_l` and `X · Ξ` (via DU, Wagner 3 and UU). -/
theorem interl_next_W_W_of_le (hC : F.Conditions) (hι : Monotone ι) (j l : Fin m')
    (hjl : j ≤ l) :
    Interl ((F.next m' ι).W j) ((F.next m' ι).W l) := by
  let band := Finset.univ.filter (fun i : Fin m => ι j ≤ i ∧ i < ι l)
  have hident := F.next_W_sub_next_W (ι := ι) j l (hι hjl)
  let H := band.sum F.U
  let Xi : ℝ[X] := F.S (ι j) + band.sum F.D
  let K : ℝ[X] := X * Xi + F.T (ι l)
  have hT_eq : F.T (ι j) = band.sum F.W + F.T (ι l) := by
    simpa [T, band] using sum_filter_tail_eq_add (f := F.W) (hι hjl)
  have hbandW : band.sum F.W = band.sum (fun i => X * F.D i) + H :=
    F.sum_W_eq_sum_X_mul_D_add_sum_U band
  have hX_Xi : X * Xi = X * F.S (ι j) + band.sum (fun i => X * F.D i) := by
    simp [Xi, mul_add, Finset.mul_sum]
  have hWj_eq : (F.next m' ι).W j = H + K := by
    simp [next_W, K, hT_eq, hbandW, hX_Xi]
    ring
  have hH_nn : HasNonnegCoeffs H :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i)
  have hH_interl : Interl H ((F.next m' ι).W j) := by
    have hS_H : Interl (F.S (ι j)) H := by
      refine Interl.finsetSum_right_of_nonneg _ F.A H (fun i hi => ?_)
        (fun i _ => F.hasNonnegCoeffs_A i)
      refine Interl.finsetSum_left_of_nonneg (F.A i) band F.U (fun r hr => ?_)
        (fun r _ => F.hasNonnegCoeffs_U r)
      exact hC.interl_A_U_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hr).2.1)
    have hbandD_H : Interl (band.sum F.D) H :=
      Interl.finsetSum_right_of_nonneg band F.D H
        (fun i _ => Interl.finsetSum_left_of_nonneg (F.D i) band F.U
          (fun r _ => hC.interl_D_U i r) (fun r _ => F.hasNonnegCoeffs_U r))
        (fun i _ => F.hasNonnegCoeffs_D i)
    have hbandD_nn : HasNonnegCoeffs (band.sum F.D) :=
      hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i)
    have hXi_H : Interl Xi H :=
      interl_add_right hS_H hbandD_H (F.hasNonnegCoeffs_S (ι j)) hbandD_nn
    have hXi_nn : HasNonnegCoeffs Xi := (F.hasNonnegCoeffs_S (ι j)).add hbandD_nn
    have hH_Tl : Interl H (F.T (ι l)) := by
      refine Interl.finsetSum_right_of_nonneg band F.U (F.T (ι l)) (fun i hi => ?_)
        (fun i _ => F.hasNonnegCoeffs_U i)
      refine Interl.finsetSum_left_of_nonneg (F.U i) _ F.W (fun r hr => ?_)
        (fun r _ => F.hasNonnegCoeffs_W r)
      exact hC.interl_U_W_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2.2 (Finset.mem_filter.mp hr).2)
    have hK_nn : HasNonnegCoeffs K := hXi_nn.X_mul.add (F.hasNonnegCoeffs_T (ι l))
    have hHK : Interl H K :=
      interl_add_left (interl_mul_X_of_interl hXi_H hXi_nn hH_nn) hH_Tl hXi_nn.X_mul
        (F.hasNonnegCoeffs_T (ι l))
    exact interl_left_of_eq_add hWj_eq hHK hH_nn hK_nn (hC.splits_next_W j)
  have hW_eq : (F.next m' ι).W l = (F.next m' ι).W j + (X - C 1) * H := by
    linear_combination hident
  have hbound : H.eval 0 ≤ ((F.next m' ι).W j).eval 0 := by
    have h1 := eval_zero_nonneg ((F.next m' ι).hasNonnegCoeffs_W l)
    rw [hW_eq, eval_add, eval_mul, eval_sub, eval_X, eval_C] at h1
    linarith
  rw [hW_eq]
  exact interl_add_X_sub_C_one_mul hH_interl ((F.next m' ι).hasNonnegCoeffs_W j) hH_nn
    (hC.splits_next_W j) hbound

/-! ## Main propagation theorem -/

/-- **Induction step of Theorem `thm:peak_rr_ferrers`**: if `F` satisfies the
six conditions, then so does its next-level family along any monotone `ι`. -/
theorem next (hC : F.Conditions) (hι : Monotone ι) : (F.next m' ι).Conditions where
  interl_D_U := hC.interl_next_D_U
  interl_U_U_of_le := hC.interl_next_U_U_of_le hι
  interl_A_W := hC.interl_next_A_W
  interl_D_D_of_lt := hC.interl_next_D_D_of_lt hι
  interl_A_A_of_lt := hC.interl_next_A_A_of_lt hι
  interl_W_W_of_le := hC.interl_next_W_W_of_le hι

/-! ## Telescoping: `R ≪₀ P` (Lemma `lem:R_interl_P`) -/

/-- Each inner sum `∑_{j ≥ s} D_j` satisfies `∑_{j ≥ s} D_j ≪₀ P`. -/
theorem interl_sum_D_P (hC : F.Conditions) (s : Fin m) :
    Interl ((Finset.univ.filter (s ≤ ·)).sum F.D) F.P := by
  let H : ℝ[X] := (Finset.univ.filter (s ≤ ·)).sum F.D
  let Utail : ℝ[X] := (Finset.univ.filter (s ≤ ·)).sum F.U
  let K : ℝ[X] := F.S s + Utail
  have htailA : (Finset.univ.filter (s ≤ ·)).sum F.A = H + Utail :=
    F.sum_A_eq_sum_D_add_sum_U _
  have hP_eq : F.P = H + K := by
    rw [← F.S_add_sum_le_A s, htailA]
    ring
  have hH_nn : HasNonnegCoeffs H :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i)
  have hUtail_nn : HasNonnegCoeffs Utail :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i)
  have hH_S : Interl H (F.S s) :=
    Interl.finsetSum_right_of_nonneg _ F.D (F.S s)
      (fun i hi => Interl.finsetSum_left_of_nonneg (F.D i) _ F.A
        (fun r hr => interl_add_left
          (hC.interl_D_D_of_lt i r
            (lt_of_lt_of_le (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hi).2))
          (hC.interl_D_U i r) (F.hasNonnegCoeffs_D r) (F.hasNonnegCoeffs_U r))
        (fun r _ => F.hasNonnegCoeffs_A r))
      (fun i _ => F.hasNonnegCoeffs_D i)
  have hH_Utail : Interl H Utail :=
    Interl.finsetSum_right_of_nonneg _ F.D Utail
      (fun i _ => Interl.finsetSum_left_of_nonneg (F.D i) _ F.U
        (fun r _ => hC.interl_D_U i r) (fun r _ => F.hasNonnegCoeffs_U r))
      (fun i _ => F.hasNonnegCoeffs_D i)
  exact interl_left_of_eq_add hP_eq
    (interl_add_left hH_S hH_Utail (F.hasNonnegCoeffs_S s) hUtail_nn) hH_nn
    ((F.hasNonnegCoeffs_S s).add hUtail_nn) hC.splits_P

/-- The telescoping lemma `lem:R_interl_P`: `R ≪₀ P`. -/
theorem interl_R_P (hC : F.Conditions) (bound : Fin m) : Interl (F.R bound) F.P :=
  Interl.finsetSum_right_of_nonneg _ _ F.P
    (fun s _ => hC.interl_sum_D_P s)
    (fun _ _ => hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i))

/-! ## Boundary interlacings for the `m + 1` step -/

lemma interl_nextBoundary_D_last_D_castSucc (hC : F.Conditions) (k : Fin m) :
    Interl ((F.nextBoundary).D (Fin.last m)) ((F.nextBoundary).D (Fin.castSucc k)) := by
  simpa using hC.interl_P_S k

lemma interl_nextBoundary_D_last_U_castSucc (hC : F.Conditions) (k : Fin m) :
    Interl ((F.nextBoundary).D (Fin.last m)) ((F.nextBoundary).U (Fin.castSucc k)) := by
  simpa using hC.interl_P_T k

lemma interl_nextBoundary_A_last_W_last (hC : F.Conditions) :
    Interl ((F.nextBoundary).A (Fin.last m)) ((F.nextBoundary).W (Fin.last m)) := by
  simpa using interl_mul_X_of_interl (Interl.refl fun _ => hC.splits_P)
    F.hasNonnegCoeffs_P F.hasNonnegCoeffs_P

lemma interl_nextBoundary_A_last_A_castSucc (hC : F.Conditions) (k : Fin m) :
    Interl ((F.nextBoundary).A (Fin.last m)) ((F.nextBoundary).A (Fin.castSucc k)) := by
  let H : ℝ[X] := (Finset.univ.filter (k ≤ ·)).sum F.D
  let Utail : ℝ[X] := (Finset.univ.filter (k ≤ ·)).sum F.U
  have hH_nn : HasNonnegCoeffs H :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i)
  have hP_eq : F.P = H + (F.S k + Utail) := by
    rw [← F.S_add_sum_le_A k, F.sum_A_eq_sum_D_add_sum_U]
    ring
  have hK_nn : HasNonnegCoeffs (F.S k + Utail) :=
    (F.hasNonnegCoeffs_S k).add (hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i))
  have hbound : H.eval 0 ≤ F.P.eval 0 := by
    have hK0 := eval_zero_nonneg hK_nn
    rw [hP_eq, eval_add]
    linarith
  rw [nextBoundary_A_last, F.nextBoundary_A_castSucc_eq k]
  exact interl_add_X_sub_C_one_mul (hC.interl_sum_D_P k) F.hasNonnegCoeffs_P hH_nn
    hC.splits_P hbound

/-- The boundary `A⁺_{m+1} = P` interlaces every old-position `W⁺_k = X * S_k + T_k`.
We write `W⁺_k = P + (X - 1) * H` with `H = S_k + ∑_{j ≥ k} D_j` and apply the shift
lemma to `H ≪₀ P`. -/
lemma interl_nextBoundary_A_last_W_castSucc (hC : F.Conditions) (k : Fin m) :
    Interl ((F.nextBoundary).A (Fin.last m)) ((F.nextBoundary).W (Fin.castSucc k)) := by
  let tailD : ℝ[X] := (Finset.univ.filter (k ≤ ·)).sum F.D
  let tailU : ℝ[X] := (Finset.univ.filter (k ≤ ·)).sum F.U
  let H : ℝ[X] := F.S k + tailD
  have htailD_nn : HasNonnegCoeffs tailD :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_D i)
  have htailU_nn : HasNonnegCoeffs tailU :=
    hasNonnegCoeffs_finsetSum _ _ (fun i _ => F.hasNonnegCoeffs_U i)
  have hH_nn : HasNonnegCoeffs H := (F.hasNonnegCoeffs_S k).add htailD_nn
  have hP_eq : F.P = H + tailU := by
    rw [← F.S_add_sum_le_A k, F.sum_A_eq_sum_D_add_sum_U]
    ring
  have hW_eq : X * F.S k + F.T k = F.P + (X - C 1) * H := by
    rw [hP_eq, T, F.sum_W_eq_sum_X_mul_D_add_sum_U, ← Finset.mul_sum, C_1]
    ring
  have hS_tailU : Interl (F.S k) tailU :=
    Interl.finsetSum_pairwise_of_nonneg _ _ F.A F.U
      (fun i hi r hr => hC.interl_A_U_of_lt
        (lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hr).2))
      (fun i _ => F.hasNonnegCoeffs_A i) (fun r _ => F.hasNonnegCoeffs_U r)
  have htailD_tailU : Interl tailD tailU :=
    Interl.finsetSum_pairwise_of_nonneg _ _ F.D F.U (fun i _ r _ => hC.interl_D_U i r)
      (fun i _ => F.hasNonnegCoeffs_D i) (fun r _ => F.hasNonnegCoeffs_U r)
  have hH_P : Interl H F.P :=
    interl_left_of_eq_add hP_eq
      (interl_add_right hS_tailU htailD_tailU (F.hasNonnegCoeffs_S k) htailD_nn)
      hH_nn htailU_nn hC.splits_P
  have hbound : H.eval 0 ≤ F.P.eval 0 := by
    have h0 := eval_zero_nonneg htailU_nn
    rw [hP_eq, eval_add (p := H)]
    linarith
  rw [nextBoundary_A_last, nextBoundary_W_castSucc, hW_eq]
  exact interl_add_X_sub_C_one_mul hH_P F.hasNonnegCoeffs_P hH_nn hC.splits_P hbound

/-- **Boundary induction step**: if `F` satisfies the six conditions, then so does the
boundary-aware next family `F.nextBoundary`, whose extra top index carries
`D⁺_{m+1} = P` and `U⁺_{m+1} = 0`. -/
theorem nextBoundary (hC : F.Conditions) : (F.nextBoundary).Conditions := by
  have hN := hC.next (ι := id) monotone_id
  have hXP : Interl (X * F.P) (X * F.P) :=
    Interl.refl fun _ => Splits.X.mul hC.splits_P
  have hAW_last (k : Fin m) :
      Interl ((F.nextBoundary).A k.castSucc) ((F.nextBoundary).W (Fin.last m)) := by
    simpa using interl_mul_X_of_interl (hC.interl_nextBoundary_A_last_A_castSucc k)
      ((F.nextBoundary).hasNonnegCoeffs_A _) ((F.nextBoundary).hasNonnegCoeffs_A k.castSucc)
  have hWW_last (k : Fin m) :
      Interl ((F.nextBoundary).W k.castSucc) ((F.nextBoundary).W (Fin.last m)) := by
    simpa using interl_mul_X_of_interl (hC.interl_nextBoundary_A_last_W_castSucc k)
      ((F.nextBoundary).hasNonnegCoeffs_A _) ((F.nextBoundary).hasNonnegCoeffs_W k.castSucc)
  refine ⟨fun j l => ?_, fun j l hjl => ?_, fun j l => ?_, fun j j' hjj' => ?_,
    fun j j' hjj' => ?_, fun j l hjl => ?_⟩
  · induction j using Fin.lastCases with
    | last =>
      induction l using Fin.lastCases with
      | last => simpa using interl_zero_right F.P
      | cast l => exact hC.interl_nextBoundary_D_last_U_castSucc l
    | cast j =>
      induction l using Fin.lastCases with
      | last => simpa using interl_zero_right (F.S j)
      | cast l => simpa using hN.interl_D_U j l
  · induction l using Fin.lastCases with
    | last => simpa using interl_zero_right ((F.nextBoundary).U j)
    | cast l =>
      induction j using Fin.lastCases with
      | last => exact absurd hjl (Fin.castSucc_lt_last l).not_ge
      | cast j => simpa using hN.interl_U_U_of_le j l (by simpa using hjl)
  · induction j using Fin.lastCases with
    | last =>
      induction l using Fin.lastCases with
      | last => exact hC.interl_nextBoundary_A_last_W_last
      | cast l => exact hC.interl_nextBoundary_A_last_W_castSucc l
    | cast j =>
      induction l using Fin.lastCases with
      | last => exact hAW_last j
      | cast l => simpa using hN.interl_A_W j l
  · induction j' using Fin.lastCases with
    | last => exact absurd hjj' (not_lt.mpr (Fin.le_last j))
    | cast j' =>
      induction j using Fin.lastCases with
      | last => exact hC.interl_nextBoundary_D_last_D_castSucc j'
      | cast j => simpa using hN.interl_D_D_of_lt j j' (by simpa using hjj')
  · induction j' using Fin.lastCases with
    | last => exact absurd hjj' (not_lt.mpr (Fin.le_last j))
    | cast j' =>
      induction j using Fin.lastCases with
      | last => exact hC.interl_nextBoundary_A_last_A_castSucc j'
      | cast j => simpa using hN.interl_A_A_of_lt j j' (by simpa using hjj')
  · induction l using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using hXP
      | cast j => exact hWW_last j
    | cast l =>
      induction j using Fin.lastCases with
      | last => exact absurd hjl (Fin.castSucc_lt_last l).not_ge
      | cast j => simpa using hN.interl_W_W_of_le j l (by simpa using hjl)

end Conditions

/-! ## Base case -/

/-- The base case `λ = (1)`: `m = 1`, `D_0 = 0`, `U_0 = 1`. -/
def base : PeakFamily 1 where
  D _ := 0
  U _ := 1
  hasNonnegCoeffs_D _ := hasNonnegCoeffs_zero
  hasNonnegCoeffs_U _ := hasNonnegCoeffs_one

private lemma base_U (k : Fin 1) : base.U k = 1 := rfl

private lemma base_A (k : Fin 1) : base.A k = 1 := by
  simp [A, base]

private lemma base_W (k : Fin 1) : base.W k = 1 := by
  simp [W, base]

/-- The base case satisfies all six conditions. -/
theorem conditions_base : base.Conditions where
  interl_D_U _ _ := interl_zero_left _
  interl_U_U_of_le j l _ := by rw [base_U j, base_U l]; exact Interl.refl fun _ => Splits.one
  interl_A_W j l := by rw [base_A j, base_W l]; exact Interl.refl fun _ => Splits.one
  interl_D_D_of_lt j j' h := by simp [Subsingleton.elim j' j] at h
  interl_A_A_of_lt j j' h := by simp [Subsingleton.elim j' j] at h
  interl_W_W_of_le j l _ := by rw [base_W j, base_W l]; exact Interl.refl fun _ => Splits.one

/-! ## Full induction over Ferrers boards

A Ferrers board `λ = (λ_1, ..., λ_n)` with `λ_i ≥ i` produces a sequence of peak
families `F_1, ..., F_n` with `F_1 = base` and `F_{i+1}` obtained from `F_i` by
`next` (old cut positions) or `nextBoundary` (when the width grows from `m` to
`m + 1`, with `D⁺_{m+1} = P` and `U⁺_{m+1} = 0`). We call the families produced
this way *reachable*. The remaining gap to a theorem about Ferrers boards is
combinatorial: one still has to encode boards and permutation sets and prove that
their recursion agrees with this abstract `PeakFamily` recursion. -/

/-- The peak families reachable from `base` by the recursion steps `next` (along a
monotone map of cut positions) and `nextBoundary`. -/
inductive IsReachable : {m : ℕ} → PeakFamily m → Prop
  | base : IsReachable base
  | next {m m' : ℕ} {F : PeakFamily m} {ι : Fin m' → Fin m} :
      IsReachable F → Monotone ι → IsReachable (F.next m' ι)
  | nextBoundary {m : ℕ} {F : PeakFamily m} : IsReachable F → IsReachable F.nextBoundary

/-- Every reachable peak family satisfies the six interlacing conditions. -/
theorem IsReachable.conditions (hF : F.IsReachable) : F.Conditions := by
  induction hF with
  | base => exact conditions_base
  | next _ hι ih => exact ih.next hι
  | nextBoundary _ ih => exact ih.nextBoundary

/-- **Abstract form of Theorem `thm:peak_rr_ferrers`**: the total peak
polynomial `P = ∑ A_k` of a reachable peak family is real-rooted whenever some
`A_k` is nonzero. -/
theorem IsReachable.isRealRooted_P (hF : F.IsReachable) (hne : ∃ k : Fin m, F.A k ≠ 0) :
    F.P ≠ 0 ∧ F.P.Splits :=
  hF.conditions.isRealRooted_P hne

end PeakFamily

end RealRooted.Applications.PeakPolynomials
