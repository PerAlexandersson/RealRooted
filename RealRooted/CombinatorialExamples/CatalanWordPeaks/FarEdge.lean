/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
import RealRooted.CombinatorialExamples.CatalanWordPeaks.RootSelection
import RealRooted.LaguerreSamuelson
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

/-!
# Farthest-root signs from three translated coefficients

Vieta and the existing Samuelson moment identities replace the custom root
factorization and Newton induction. No new interlacing relation is introduced.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.FarEdge

open Polynomial Finset

private theorem shifted_factorization {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots) :
    P.comp (X + 1) = C P.leadingCoeff * ∏ i, (X + C (1 + r i)) := by
  have hc : P.roots.card = P.natDegree := by
    rw [← hroots, Multiset.coe_card, List.length_ofFn, hdeg]
  have hs := splits_iff_card_roots.mpr hc
  apply Polynomial.funext
  intro t
  simp only [eval_comp, eval_add, eval_X, eval_one, eval_mul, eval_C, eval_prod]
  rw [eval_eq_root_product hs hroots]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The two upper coefficients of the translated polynomial measure the sum
and the sum of squares of the translated root moduli. -/
private theorem shifted_top_two {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots) (hm : 2 ≤ m) :
    let Q := P.comp (X + 1)
    Q.coeff (m-1) = P.leadingCoeff * (∑ i, (1 + r i)) ∧
    2 * Q.coeff (m-2) = P.leadingCoeff *
      ((∑ i, (1 + r i))^2 - ∑ i, (1 + r i)^2) := by
  classical
  dsimp only
  let v : Multiset ℝ := Finset.univ.val.map (fun i : Fin m => 1 + r i)
  have hc : v.card = m := by simp [v]
  have hva : v.sum = ∑ i, (1 + r i) := rfl
  have hvb : (v.map (fun b => b^2)).sum = ∑ i, (1 + r i)^2 := by
    simp only [v, Multiset.map_map]; rfl
  have hf : (∏ i, (X + C (1 + r i))) = (v.map (fun a => X + C a)).prod := by
    simp only [v, Multiset.map_map]; rfl
  rw [shifted_factorization hdeg hroots, hf, coeff_C_mul, coeff_C_mul]
  rw [Multiset.prod_X_add_C_coeff v (show m-1 ≤ v.card by lia),
      Multiset.prod_X_add_C_coeff v (show m-2 ≤ v.card by lia)]
  rw [hc, show m-(m-1)=1 by lia, show m-(m-2)=2 by lia, RealRooted.Samuelson.esymm_one, hva]
  constructor
  · rfl
  · have hs := RealRooted.Samuelson.sum_map_sq_eq v
    rw [hva, hvb] at hs
    rw [show (∑ i, (1 + r i))^2 - ∑ i, (1 + r i)^2 = 2*v.esymm 2 by linarith only [hs]]
    ring

/-- Two coefficient bounds separate the largest root from every competitor. -/
private theorem far_root_bounds {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots)
    (hpos : ∀ i, 0 < r i) (hm : 2 ≤ m) (lead : 0 < P.leadingCoeff)
    {U c : ℝ} (hU : 0 < U)
    (hu : (P.comp (X + 1)).coeff (m - 1) = P.leadingCoeff * U)
    (hc : 2 * (P.comp (X + 1)).coeff (m - 2) < P.leadingCoeff * (c * U ^ 2))
    (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (1 - c) * U < 1 + r l ∧ 1 + r l ≤ U ∧
    ∀ i, i ≠ l → 1 + r i < c * U := by
  classical
  obtain ⟨hs, hsq⟩ := shifted_top_two hdeg hroots hm
  let y := fun i : Fin m => 1+r i
  have hy (i : Fin m) : 0 ≤ y i := by dsimp [y]; linarith [hpos i]
  have hsum : ∑ i, y i = U := (mul_left_cancel₀ lead.ne' (hs.symm.trans hu))
  change 2 * _ = P.leadingCoeff * ((∑ i, y i)^2 - ∑ i, y i ^ 2) at hsq
  rw [hsum] at hsq
  have hsq' : U^2 - ∑ i, y i^2 < c * U^2 :=
    (mul_lt_mul_iff_right₀ lead).mp (hsq.symm.trans_lt hc)
  have hmax : ∑ i, y i^2 ≤ y l * U := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [sq]
    exact mul_le_mul_of_nonneg_right (show y i ≤ y l from add_le_add le_rfl (last i)) (hy i)
  have hL : (1-c)*U < y l := by
    apply (mul_lt_mul_iff_left₀ hU).mp
    nlinarith only [hsq', hmax]
  have hle : y l ≤ U := by
    rw [← hsum]; exact Finset.single_le_sum (fun i _ => hy i) (Finset.mem_univ l)
  refine ⟨hL, hle, ?_⟩
  intro i hi
  have hlo := Finset.sum_erase_add Finset.univ y (Finset.mem_univ l)
  have hi' : i ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have bound : y i ≤ ∑ j ∈ Finset.univ.erase l, y j :=
    Finset.single_le_sum (fun j _ => hy j) hi'
  rw [hsum] at hlo
  change y i < c*U
  nlinarith only [hL, hlo, bound]

private theorem eval_at_neg_eq_product {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots) (x : ℝ) :
    P.eval (-x) = P.leadingCoeff * ∏ i, (r i - x) := by
  have hv := congrArg (fun f : ℝ[X] => f.eval (-x-1)) (shifted_factorization hdeg hroots)
  simp only [eval_comp, eval_add, eval_X, eval_one, sub_add_cancel, eval_mul, eval_C,
    eval_prod] at hv
  convert hv using 2
  apply Finset.prod_congr rfl
  intro i _
  ring

private theorem reflection_product {m : ℕ} (r : Fin m → ℝ) (x : ℝ) :
    (-1 : ℝ) ^ m * (∏ i, (r i - x)) = ∏ i, (x - r i) := by
  calc
    _ = (∏ _ : Fin m, (-1 : ℝ)) * (∏ i, (r i-x)) := by simp
    _ = ∏ i, ((-1 : ℝ) * (r i-x)) := Finset.prod_mul_distrib.symm
    _ = _ := by apply Finset.prod_congr rfl; intro i _; ring

private theorem eval_outside_all {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots)
    (lead : 0 < P.leadingCoeff) {x : ℝ}
    (hout : ∀ i, r i < x) : 0 < (-1 : ℝ) ^ m * P.eval (-x) := by
  rw [eval_at_neg_eq_product hdeg hroots, mul_left_comm, reflection_product]
  exact mul_pos lead (Finset.prod_pos fun i _ => sub_pos.mpr (hout i))

private theorem eval_inside_last {m : ℕ} {P : ℝ[X]} {r : Fin (m + 1) → ℝ}
    (hdeg : P.natDegree = m + 1)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots)
    (lead : 0 < P.leadingCoeff) {x : ℝ}
    (hlo : ∀ i : Fin m, r i.castSucc < x) (hhi : x < r (Fin.last m)) :
    0 < (-1 : ℝ) ^ m * P.eval (-x) := by
  rw [eval_at_neg_eq_product hdeg hroots, Fin.prod_univ_castSucc, mul_left_comm]
  rw [← mul_assoc ((-1 : ℝ)^m), reflection_product (fun i : Fin m => r i.castSucc) x]
  exact mul_pos lead (mul_pos (Finset.prod_pos fun i _ => sub_pos.mpr (hlo i)) (sub_pos.mpr hhi))

private theorem shifted_leading {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots) :
    (P.comp (X + 1)).coeff m = P.leadingCoeff := by
  classical
  rw [shifted_factorization hdeg hroots, coeff_C_mul, Finset.prod_X_add_C_coeff _ _
    (show m ≤ (Finset.univ : Finset (Fin m)).card by simp)]
  simp

private def oddFirst (x : ℝ) : ℝ := x*(x+1)*(x+4)*(x+5)/12
private def oddSecond (x : ℝ) : ℝ :=
  (x-1)*x*(x+1)*(x+2)*(x+5)*(x+6)*(x+7)*(x+8)/2880
private def evenLead (x : ℝ) : ℝ := (x+1)*(x+4)/2
private def evenFirst (x : ℝ) : ℝ :=
  x*(x+1)*(x+2)*(x+5)*(x+6)*(x+7)/144
private def evenSecond (x : ℝ) : ℝ :=
  (x-1)*x*(x+1)*(x+2)*(x+3)*(x+6)*(x+7)*(x+8)*(x+9)*(x+10)/86400

private theorem odd_spread {x : ℝ} (hx : 74 ≤ x) :
    50 * oddSecond x < 3 * (oddFirst x) ^ 2 := by
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le hx
  unfold oddSecond oddFirst
  apply sub_pos.mp
  ring_nf
  positivity

private theorem even_spread {x : ℝ} (hx : 74 ≤ x) :
    50 * evenSecond x * evenLead x < 7 * (evenFirst x) ^ 2 := by
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le hx
  unfold evenSecond evenFirst evenLead
  apply sub_pos.mp
  ring_nf
  positivity

/-- The neighboring odd-row sums are between four and six times the
translated even-row sum. -/
private theorem neighboring_scales {x : ℝ} (hx : 74 ≤ x) :
    let E := evenFirst x / evenLead x
    4*E < oddFirst x ∧ oddFirst x < 6*E ∧
    4*E < oddFirst (x+1) ∧ oddFirst (x+1) < 6*E := by
  dsimp only
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le hx
  have h : 0 < evenLead (74+u) := by unfold evenLead; positivity
  simp only [← mul_div_assoc, div_lt_iff₀ h, lt_div_iff₀ h]
  unfold oddFirst evenFirst evenLead
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply sub_pos.mp <;> ring_nf <;> positivity

/-- The three highest coefficients after translating the variable by one. -/
private structure ShiftedTop (P : ℝ[X]) (m : ℕ) (L A B : ℝ) : Prop where
  top : (P.comp (X+1)).coeff m = L
  first : (P.comp (X+1)).coeff (m-1) = A
  second : (P.comp (X+1)).coeff (m-2) = B

private theorem bounds_of_top {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots)
    (hpos : ∀ i, 0 < r i) (hm : 2 ≤ m)
    {L A B c : ℝ} (top : ShiftedTop P m L A B) (hL : 0 < L) (hA : 0 < A)
    (spread : 50 * B * L < c * A ^ 2) (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (1 - c / 25) * (A / L) < 1 + r l ∧ 1 + r l ≤ A / L ∧
    ∀ i, i ≠ l → 1 + r i < (c / 25) * (A / L) := by
  have lc := (shifted_leading hdeg hroots).symm.trans top.top
  apply far_root_bounds hdeg hroots hpos hm (by rwa [lc]) (div_pos hA hL) _ _ l last
  · rw [top.first, lc]
    field_simp
  · rw [top.second, lc]
    have hx : B < c*A^2 / (50*L) := (lt_div_iff₀ (by positivity)).mpr (by linarith only [spread])
    calc 2*B < 2*(c*A^2 / (50*L)) := by linarith only [hx]
         _ = _ := by field_simp; ring

private theorem odd_bounds {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots)
    (hpos : ∀ i, 0 < r i) (hm : 74 ≤ m)
    (top : ShiftedTop P m 1 (oddFirst m) (oddSecond m))
    (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (22 / 25 : ℝ) * oddFirst m < 1 + r l ∧ 1 + r l ≤ oddFirst m ∧
    ∀ i, i ≠ l → 1 + r i < (3 / 25 : ℝ) * oddFirst m := by
  have hx : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hp : 0 < oddFirst m := by unfold oddFirst; positivity
  have hspread := odd_spread hx
  simpa only [div_one, show 1-(3:ℝ)/25=22/25 by norm_num] using
    bounds_of_top hdeg hroots hpos (by lia) top (by norm_num) hp ((by simpa using hspread) :
      50*oddSecond m*1 < 3*(oddFirst m)^2) l last

private theorem even_bounds {m : ℕ} {P : ℝ[X]} {r : Fin m → ℝ}
    (hdeg : P.natDegree = m)
    (hroots : (↑(List.ofFn (fun i => -r i)) : Multiset ℝ) = P.roots)
    (hpos : ∀ i, 0 < r i) (hm : 74 ≤ m)
    (top : ShiftedTop P m (evenLead m) (evenFirst m) (evenSecond m))
    (l : Fin m) (last : ∀ i, r i ≤ r l) :
    (18 / 25 : ℝ) * (evenFirst m / evenLead m) < 1 + r l ∧
    1 + r l ≤ evenFirst m / evenLead m ∧
    ∀ i, i ≠ l → 1 + r i < (7 / 25 : ℝ) * (evenFirst m / evenLead m) := by
  have hx : (74 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hp : 0 < evenFirst m := by unfold evenFirst; positivity
  have hl : 0 < evenLead m := by unfold evenLead; positivity
  simpa only [show 1-(7:ℝ)/25=18/25 by norm_num] using
    bounds_of_top hdeg hroots hpos (by lia) top hl hp (even_spread hx) l last

private theorem odd_to_even_sign {m : ℕ} (hm : 74 ≤ m) {O E : ℝ[X]}
    {o e : Fin m → ℝ} (hdo : O.natDegree = m) (hde : E.natDegree = m)
    (ho : (↑(List.ofFn (fun i => -o i)) : Multiset ℝ) = O.roots)
    (he : (↑(List.ofFn (fun i => -e i)) : Multiset ℝ) = E.roots)
    (hop : ∀ i, 0 < o i) (hep : ∀ i, 0 < e i) (hom : StrictMono o) (hem : StrictMono e)
    (to' : ShiftedTop O m 1 (oddFirst m) (oddSecond m))
    (te : ShiftedTop E m (evenLead m) (evenFirst m) (evenSecond m))
    (l : Fin m) (last : ∀ i, i ≤ l) : 0 < (-1 : ℝ) ^ m * E.eval (-o l) := by
  have topO := odd_bounds hdo ho hop hm to' l (fun i => hom.monotone (last i))
  have topE := even_bounds hde he hep hm te l (fun i => hem.monotone (last i))
  have scales := neighboring_scales (x := (m : ℝ)) (by exact_mod_cast hm)
  have hEL : 0 < evenLead m := by unfold evenLead; positivity
  apply eval_outside_all hde he (by rwa [(shifted_leading hde he).symm.trans te.top])
  intro i
  have hroot : e i ≤ e l := hem.monotone (last i)
  linarith only [hroot, hep l, topO.1, topE.2.1, scales.1]

private theorem even_to_odd_sign {m : ℕ} (hm : 74 ≤ m) {E O : ℝ[X]}
    {e : Fin m → ℝ} {o : Fin (m + 1) → ℝ} (hde : E.natDegree = m) (hdo : O.natDegree = m + 1)
    (he : (↑(List.ofFn (fun i => -e i)) : Multiset ℝ) = E.roots)
    (ho : (↑(List.ofFn (fun i => -o i)) : Multiset ℝ) = O.roots)
    (hep : ∀ i, 0 < e i) (hop : ∀ i, 0 < o i) (hem : StrictMono e) (hom : StrictMono o)
    (te : ShiftedTop E m (evenLead m) (evenFirst m) (evenSecond m))
    (to' : ShiftedTop O (m + 1) 1 (oddFirst (m + 1)) (oddSecond (m + 1)))
    (l : Fin m) (last : ∀ i, i ≤ l) : 0 < (-1 : ℝ) ^ m * O.eval (-e l) := by
  have topE := even_bounds hde he hep hm te l (fun i => hem.monotone (last i))
  have to2 : ShiftedTop O (m+1) 1 (oddFirst ((m+1 : ℕ) : ℝ))
      (oddSecond ((m+1 : ℕ) : ℝ)) := by simpa only [Nat.cast_add, Nat.cast_one] using to'
  have topO := odd_bounds hdo ho hop (by lia : 74 ≤ m+1) to2 (Fin.last m)
    (fun i => hom.monotone (Fin.le_last i))
  simp only [Nat.cast_add, Nat.cast_one] at topO
  have scales := neighboring_scales (x := (m : ℝ)) (by exact_mod_cast hm)
  apply eval_inside_last hdo ho (by rw [← shifted_leading hdo ho, to'.top]; norm_num)
  · intro i
    have h := topO.2.2 i.castSucc (Fin.castSucc_ne_last i)
    linarith only [h, topE.1, scales.2.2.2]
  · linarith only [hep l, topO.1, topE.2.1, scales.2.2.1]

private theorem odd_top (m : ℕ) (hm : 2 ≤ m) :
    ShiftedTop (polynomial (2 * m + 1)) m 1 (oddFirst m) (oddSecond m) :=
  ⟨TopCoefficients.coeff_odd_top m, TopCoefficients.coeff_odd_next m (by lia),
    TopCoefficients.coeff_odd_next_two m hm⟩

private theorem even_top (m : ℕ) (hm : 2 ≤ m) :
    ShiftedTop (polynomial (2 * m + 2)) m (evenLead m) (evenFirst m) (evenSecond m) :=
  ⟨TopCoefficients.coeff_even_top m, TopCoefficients.coeff_even_next m (by lia),
    TopCoefficients.coeff_even_next_two m hm⟩

/-- The next row has the strict opposite-derivative sign at the old farthest root. -/
theorem farthest_root_sign (n : ℕ) (hn : 150 ≤ n) :
    ∀ (old : Fin (rowDegree n) → ℝ) (new : Fin (rowDegree (n + 1)) → ℝ),
    StrictMono old → StrictMono new → (∀ i, 0 < old i) → (∀ i, 0 < new i) →
    (↑(List.ofFn (fun i => -old i)) : Multiset ℝ) = (polynomial n).roots →
    (↑(List.ofFn (fun i => -new i)) : Multiset ℝ) = (polynomial (n + 1)).roots →
    ∀ i : Fin (rowDegree n), i.val + 1 = rowDegree n →
      0 < (-1 : ℝ) ^ (i.val + 1) * (polynomial (n + 1)).eval (-old i) := by
  obtain ⟨m, hm, heq⟩ : ∃ m : ℕ, 74 ≤ m ∧ (n = 2*m+1 ∨ n = 2*m+2) := by
    by_cases hnodd : n % 2 = 1
    · exact ⟨(n-1)/2, by lia, Or.inl (by lia)⟩
    · exact ⟨(n-2)/2, by lia, Or.inr (by lia)⟩
  rcases heq with rfl | rfl
  · have hdO : rowDegree (2*m+1) = m := by unfold rowDegree; lia
    have hdE : rowDegree (2*m+2) = m := by unfold rowDegree; lia
    rw [show 2*m+1+1 = 2*m+2 by lia, hdO, hdE]
    intro old new hom hem hop hep ho he i hi
    rw [hi]
    exact odd_to_even_sign hm ((natDegree_polynomial (2*m+1)).trans hdO)
      ((natDegree_polynomial (2*m+2)).trans hdE) ho he hop hep hom hem
      (odd_top m (by lia)) (even_top m (by lia)) i
      (fun j => by have := j.isLt; change j.val ≤ i.val; lia)
  · have hdE : rowDegree (2*m+2) = m := by unfold rowDegree; lia
    have hdO : rowDegree (2*(m+1)+1) = m+1 := by unfold rowDegree; lia
    rw [show 2*m+2+1 = 2*(m+1)+1 by lia, hdE, hdO]
    intro old new hom hem hop hep ho he i hi
    rw [hi]
    exact even_to_odd_sign hm ((natDegree_polynomial (2*m+2)).trans hdE)
      ((natDegree_polynomial (2*(m+1)+1)).trans hdO) ho he hop hep hom hem
      (even_top m (by lia)) (by simpa using odd_top (m+1) (by lia)) i
      (fun j => by have := j.isLt; change j.val ≤ i.val; lia)

end RealRooted.CatalanWordPeaks.FarEdge
