import RealRooted.MaWang

open Polynomial

noncomputable section

namespace RealRooted

/-- Polynomial-weighted sum `∑ bᵢ gᵢ` for a finite list of pairs `(bᵢ, gᵢ)`. -/
def polynomialWeightedSum : List (ℝ[X] × ℝ[X]) → ℝ[X]
  | [] => 0
  | (b, g) :: l => b * g + polynomialWeightedSum l

@[simp] lemma polynomialWeightedSum_nil :
    polynomialWeightedSum [] = 0 := rfl

@[simp] lemma polynomialWeightedSum_cons (b g : ℝ[X]) (l : List (ℝ[X] × ℝ[X])) :
    polynomialWeightedSum ((b, g) :: l) = b * g + polynomialWeightedSum l := rfl

/-- At a root of the common right-hand polynomial `f`, a polynomial-weighted sum
of terms `bᵢ gᵢ` has nonpositive sign relative to any fixed interlacer `g₀`, as
soon as each `gᵢ` has the same right-hand target `f` and each coefficient
polynomial evaluates nonpositively there. -/
lemma polynomialWeightedSum_eval_mul_eval_nonpos_of_common_right
    {f g₀ : ℝ[X]}
    (hg₀f : Prec g₀ f)
    (hg₀_pos : HasPosLeadingCoeff g₀) :
    ∀ {l : List (ℝ[X] × ℝ[X])},
      (∀ bg ∈ l, Prec bg.2 f) →
      (∀ bg ∈ l, HasPosLeadingCoeff bg.2) →
      (∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0) →
      ∀ r : ℝ, f.IsRoot r →
        (polynomialWeightedSum l).eval r * g₀.eval r ≤ 0
  | [], _, _, _, r, hr => by
      simp
  | (b, g) :: l, hprec, hpos, hcoeff, r, hr => by
      have hgf : Prec g f := hprec (b, g) (by simp)
      have hg_pos : HasPosLeadingCoeff g := hpos (b, g) (by simp)
      have hb_nonpos : b.eval r ≤ 0 := hcoeff (b, g) (by simp) r hr
      have hgg_nonneg : 0 ≤ g.eval r * g₀.eval r :=
        eval_mul_eval_nonneg_of_prec_right hgf hg₀f hg_pos hg₀_pos hr
      have hterm_nonpos : (b * g).eval r * g₀.eval r ≤ 0 := by
        calc
          (b * g).eval r * g₀.eval r
              = b.eval r * (g.eval r * g₀.eval r) := by
                  simp [Polynomial.eval_mul]
                  ring
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb_nonpos hgg_nonneg
      have htail_prec : ∀ bg ∈ l, Prec bg.2 f := by
        grind
      have htail_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2 := by
        grind
      have htail_coeff :
          ∀ bg ∈ l, ∀ x : ℝ, f.IsRoot x → bg.1.eval x ≤ 0 := by
        grind
      have htail_nonpos :
          (polynomialWeightedSum l).eval r * g₀.eval r ≤ 0 :=
        polynomialWeightedSum_eval_mul_eval_nonpos_of_common_right
          hg₀f hg₀_pos htail_prec htail_pos htail_coeff r hr
      have hsum :
          (polynomialWeightedSum ((b, g) :: l)).eval r * g₀.eval r
            = (b * g).eval r * g₀.eval r
                + (polynomialWeightedSum l).eval r * g₀.eval r := by
        simp [polynomialWeightedSum_cons, Polynomial.eval_add]
        grind
      grind

/-- If the distinguished head term is strictly negative at roots of `f`, while
the remaining terms are only nonpositive there, then the whole weighted sum has
strictly opposite sign from that distinguished interlacer. -/
lemma polynomialWeightedSum_cons_eval_mul_eval_neg_of_common_right
    {f g : ℝ[X]} {b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Prec g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0)
    (hl_prec : ∀ bg ∈ l, Prec bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0) :
    ∀ r : ℝ, f.IsRoot r →
      (polynomialWeightedSum ((b, g) :: l)).eval r * g.eval r < 0 := by
  intro r hr
  have hg_eval_ne : g.eval r ≠ 0 := by
    simp_all
  have hhead_neg : (b * g).eval r * g.eval r < 0 := by
    have hsq_pos : 0 < (g.eval r) ^ 2 := sq_pos_iff.mpr hg_eval_ne
    calc
      (b * g).eval r * g.eval r = b.eval r * (g.eval r) ^ 2 := by
        simp [Polynomial.eval_mul]
        ring
      _ < 0 := mul_neg_of_neg_of_pos (hb_neg r hr) hsq_pos
  have htail_nonpos :
      (polynomialWeightedSum l).eval r * g.eval r ≤ 0 :=
    polynomialWeightedSum_eval_mul_eval_nonpos_of_common_right
      hgf hg_pos hl_prec hl_pos hl_nonpos r hr
  have hsum :
      (polynomialWeightedSum ((b, g) :: l)).eval r * g.eval r
        = (b * g).eval r * g.eval r
            + (polynomialWeightedSum l).eval r * g.eval r := by
    simp [polynomialWeightedSum_cons, Polynomial.eval_add]
    grind
  grind

/-- Strict finite-family Liu--Wang theorem in the same-degree case. One
distinguished interlacer `g` supplies the orientation, while the remaining
interlacers contribute additional nonpositive endpoint mass. -/
theorem prec_generalizedLiuWang_strict_same
    {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg : (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  refine prec_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg ?_
  intro r hr
  have hf_eval : f.eval r = 0 := by
    simp_all
  have hl_prec : ∀ bg ∈ l, Prec bg.2 f := by
    intro bg hmem
    exact (hl_inter bg hmem).toPrec
  have hsum_sign :
      (polynomialWeightedSum ((b, g) :: l)).eval r * g.eval r < 0 :=
    polynomialWeightedSum_cons_eval_mul_eval_neg_of_common_right
      hgf.toPrec hg_pos hno hb_neg hl_prec hl_pos hl_nonpos r hr
  simp_all

/-- Strict finite-family Liu--Wang theorem in the differ-by-1 case. -/
theorem prec_generalizedLiuWang_strict_succ
    {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg : (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  refine prec_of_interlaces_eval_mul_neg_succ hgf hg_pos hF_pos hdeg ?_
  intro r hr
  have hf_eval : f.eval r = 0 := by
    simp_all
  have hl_prec : ∀ bg ∈ l, Prec bg.2 f := by
    intro bg hmem
    exact (hl_inter bg hmem).toPrec
  have hsum_sign :
      (polynomialWeightedSum ((b, g) :: l)).eval r * g.eval r < 0 :=
    polynomialWeightedSum_cons_eval_mul_eval_neg_of_common_right
      hgf.toPrec hg_pos hno hb_neg hl_prec hl_pos hl_nonpos r hr
  simp_all

/-- Degree-bounded strict finite-family Liu--Wang theorem. This is the first
reusable multi-interlacer version: one distinguished head term is strictly
negative at roots of `f`, while the remaining terms are allowed to be merely
nonpositive there. -/
theorem prec_generalizedLiuWang_strict
    {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  have hcases :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree ∨
        (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree = f.natDegree + 1 := by
    lia
  rcases hcases with hsame | hsucc
  · exact
      prec_generalizedLiuWang_strict_same
        hgf hg_pos hl_inter hl_pos hl_nonpos hF_pos hsame hno hb_neg
  · exact
      prec_generalizedLiuWang_strict_succ
        hgf hg_pos hl_inter hl_pos hl_nonpos hF_pos hsucc hno hb_neg

/-- Weak generalized Liu--Wang theorem in the no-common-roots regime.

One distinguished interlacer `g` is used to orient the endpoint sign data. The
head coefficient `b` is only assumed nonpositive at roots of `f`; strictness is
recovered by subtracting `C δ * g` and then letting `δ → 0⁺`. -/
theorem prec_generalizedLiuWang_of_no_common
    {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hl_inter : ∀ bg ∈ l, Interlaces bg.2 f)
    (hl_pos : ∀ bg ∈ l, HasPosLeadingCoeff bg.2)
    (hl_nonpos : ∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)))
    (hdeg_lo : f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree)
    (hdeg_hi :
      (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l)) := by
  let F : ℝ[X] := a * f + polynomialWeightedSum ((b, g) :: l)
  have hF_rr : (F ≠ 0 ∧ F.Splits) := by
    apply isRealRooted_of_interlaces_sub_C_mul_of_forall_pos hgf
    · lia
    · lia
    · intro δ hδ
      have hFδ_eq :
          a * f + polynomialWeightedSum (((b - C δ), g) :: l) = F - C δ * g := by
        simp [F, polynomialWeightedSum_cons]
        ring
      have hFδ_pos :
          HasPosLeadingCoeff (a * f + polynomialWeightedSum (((b - C δ), g) :: l)) := by
        rw [hFδ_eq]
        exact
          hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound
            hgf hdeg_lo hF_pos δ
      have hFδ_natdeg :
          (a * f + polynomialWeightedSum (((b - C δ), g) :: l)).natDegree = F.natDegree := by
        rw [hFδ_eq]
        exact natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo δ
      have hFδ_lo :
          f.natDegree ≤ (a * f + polynomialWeightedSum (((b - C δ), g) :: l)).natDegree := by
        lia
      have hFδ_hi :
          (a * f + polynomialWeightedSum (((b - C δ), g) :: l)).natDegree ≤ f.natDegree + 1 := by
        lia
      have hbδ_neg : ∀ r, f.IsRoot r → (b - C δ).eval r < 0 := by
        intro r hr
        have hb_le : b.eval r ≤ 0 := hb_nonpos r hr
        simp
        linarith
      have hprecδ :
          Prec f (a * f + polynomialWeightedSum (((b - C δ), g) :: l)) :=
        prec_generalizedLiuWang_strict hgf hg_pos hl_inter hl_pos hl_nonpos
          hFδ_pos hFδ_lo hFδ_hi hno hbδ_neg
      have hrrδ : ((a * f + ((b - C δ) * g + polynomialWeightedSum l)) ≠ 0 ∧
        (a * f + ((b - C δ) * g + polynomialWeightedSum l)).Splits) := by
        simpa [polynomialWeightedSum_cons] using hprecδ.2.1
      simp_all
  have hroot_nonpos :
      ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by
      simp_all
    have hprec_all : ∀ bg ∈ ((b, g) :: l), Prec bg.2 f := by
      intro bg hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact hgf.toPrec
      · exact (hl_inter bg hmem').toPrec
    have hpos_all : ∀ bg ∈ ((b, g) :: l), HasPosLeadingCoeff bg.2 := by
      grind
    have hcoeff_all :
        ∀ bg ∈ ((b, g) :: l), ∀ x : ℝ, f.IsRoot x → bg.1.eval x ≤ 0 := by
      grind
    calc
      F.eval r * g.eval r
          = (polynomialWeightedSum ((b, g) :: l)).eval r * g.eval r := by
              simp [F, Polynomial.eval_add, Polynomial.eval_mul, hf_eval]
      _ ≤ 0 :=
        polynomialWeightedSum_eval_mul_eval_nonpos_of_common_right
          hgf.toPrec hg_pos hprec_all hpos_all hcoeff_all r hr
  simpa [F] using
    prec_of_interlaces_eval_mul_nonpos_of_no_common
      hgf hg_pos hF_rr hF_pos hdeg_lo hdeg_hi hno hroot_nonpos

/-- Finite-sum Liu--Wang criterion in the weak-sign, no-common-roots regime.

The strict theorem above is already formalized. This statement packages the
weak-sign version where every coefficient is only assumed nonpositive at roots
of `f`, with a distinguished head interlacer `g` and no common root between
`f` and `g`. -/
def generalizedLiuWangCriterionStatement : Prop :=
  ∀ {f g a b : ℝ[X]} {l : List (ℝ[X] × ℝ[X])},
    Interlaces g f →
    HasPosLeadingCoeff g →
    (∀ bg ∈ l, Interlaces bg.2 f) →
    (∀ bg ∈ l, HasPosLeadingCoeff bg.2) →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    (∀ r, f.IsRoot r → b.eval r ≤ 0) →
    (∀ bg ∈ l, ∀ r : ℝ, f.IsRoot r → bg.1.eval r ≤ 0) →
    HasPosLeadingCoeff (a * f + polynomialWeightedSum ((b, g) :: l)) →
    f.natDegree ≤ (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree →
    (a * f + polynomialWeightedSum ((b, g) :: l)).natDegree ≤ f.natDegree + 1 →
    Prec f (a * f + polynomialWeightedSum ((b, g) :: l))

theorem generalizedLiuWangCriterion :
    generalizedLiuWangCriterionStatement := by
  intro f g a b l hgf hg_pos hl_inter hl_pos hno hb_nonpos hl_nonpos hF_pos hdeg_lo hdeg_hi
  exact prec_generalizedLiuWang_of_no_common
    hgf hg_pos hl_inter hl_pos hl_nonpos hF_pos hdeg_lo hdeg_hi hno hb_nonpos

end RealRooted
