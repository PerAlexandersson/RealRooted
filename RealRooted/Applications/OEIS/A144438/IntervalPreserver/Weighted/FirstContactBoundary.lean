import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.FirstContactMinimal

/-!
# Boundary calculus at a weighted first contact

We turn local nonnegativity on a coordinate interval into the one-sided
derivative conditions required by the scalar first-contact lemma.
-/

open Filter Polynomial Set Topology

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Fermat's rule on a nondegenerate closed interval, including both
one-sided endpoint inequalities. -/
theorem hasDerivAt_sign_conditions_of_isLocalMinOn_Icc
    {q : ℝ → ℝ} {g m M a : ℝ} (hmM : m < M)
    (hlocal : IsLocalMinOn q (Icc m M) a)
    (hderiv : HasDerivAt q g a) :
    (a = m → 0 ≤ g) ∧ (a = M → g ≤ 0) ∧
      (m < a → a < M → g = 0) := by
  have tangentLower : (1 : ℝ) ∈ posTangentConeAt (Icc m M) m := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hmM)] with t ht
    rcases ht with ⟨ht0, ht1⟩
    simp only [smul_eq_mul, mul_one]
    constructor <;> linarith
  have tangentUpper : (-1 : ℝ) ∈ posTangentConeAt (Icc m M) M := by
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hmM)] with t ht
    rcases ht with ⟨ht0, ht1⟩
    simp only [smul_eq_mul, mul_neg, mul_one]
    constructor <;> linarith
  constructor
  · intro ha
    subst a
    have hnonneg := hlocal.hasFDerivWithinAt_nonneg
      hderiv.hasFDerivAt.hasFDerivWithinAt tangentLower
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hnonneg
  constructor
  · intro ha
    subst a
    have hnonneg := hlocal.hasFDerivWithinAt_nonneg
      hderiv.hasFDerivAt.hasFDerivWithinAt tangentUpper
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul,
      Left.nonneg_neg_iff] using hnonneg
  · intro hma haM
    exact (hlocal.isLocalMin (Icc_mem_nhds hma haM)).hasDerivAt_eq_zero hderiv

theorem weightedDecoExpandingBox_update
    {n : ℕ} {t : ℝ} {a : Fin n → ℝ}
    (hbox : weightedDecoExpandingBox t a) (j : Fin n) {c : ℝ}
    (hc : c ∈ Icc ((1 - t) / 2) ((1 + t) / 2)) :
    weightedDecoExpandingBox t (Function.update a j c) := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa only [Function.update_self] using ⟨hc.1, hc.2⟩
  · simpa only [Function.update_of_ne hij] using hbox i

theorem weightedDecoParameterCube_of_expandingBox
    {n : ℕ} {t : ℝ} {a : Fin n → ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hbox : weightedDecoExpandingBox t a) :
    a ∈ weightedDecoParameterCube n := by
  intro i hi
  have hai := hbox i
  rcases ht with ⟨ht0, ht1⟩
  rcases hai with ⟨hai0, hai1⟩
  constructor <;> linarith

/-- Coordinatewise one-sided derivative conditions at an earliest weighted
bad contact. -/
theorem weightedDeco_minimal_badContact_coordinate_signs
    {w : ℝ} {n : ℕ} (hn : n ≠ 0)
    {z : ℝ × ((Fin n → ℝ) × ℝ)}
    (hz : z ∈ weightedDecoBadContactSet w n)
    (hzmin : ∀ y ∈ weightedDecoBadContactSet w n, z.1 ≤ y.1)
    (htpos : 0 < z.1)
    (hsplits : ∀ b ∈ weightedDecoParameterCube n,
      (weightedDecoParameterImage w Finset.univ b).Splits)
    (hsimple : ∀ b ∈ weightedDecoParameterCube n,
      HasSimpleRoots (weightedDecoParameterImage w Finset.univ b))
    (hrootsNeg : ∀ b ∈ weightedDecoParameterCube n, ∀ r,
      (weightedDecoParameterImage w Finset.univ b).IsRoot r → r < 0) :
    let m := (1 - z.1) / 2
    let M := (1 + z.1) / 2
    let a := z.2.1
    let r := z.2.2
    let G := fun j : Fin n =>
      ((weightedDecoParameterImage w (Finset.univ.erase j) a).eval r /
          (weightedDecoParameterImage w Finset.univ a).derivative.eval r) *
        (-(1 + r + a j) / r -
          (weightedDecoParameterCompanion w Finset.univ a).derivative.eval r /
            (weightedDecoParameterImage w Finset.univ a).derivative.eval r)
    (∀ j, a j = m → 0 ≤ G j) ∧
      (∀ j, a j = M → G j ≤ 0) ∧
      (∀ j, m < a j → a j < M → G j = 0) := by
  dsimp only
  rcases hz with ⟨ht, hbox, hroot, hbad⟩
  let a := z.2.1
  let r := z.2.2
  let m := (1 - z.1) / 2
  let M := (1 + z.1) / 2
  let p := weightedDecoParameterImage w Finset.univ a
  let h := weightedDecoParameterCompanion w Finset.univ a
  have haCube : a ∈ weightedDecoParameterCube n :=
    weightedDecoParameterCube_of_expandingBox ht hbox
  have hsimpleA : HasSimpleRoots p := hsimple a haCube
  have hrneg : r < 0 := hrootsNeg a haCube r hroot
  have hsignZero : weightedDecoResidueSign w n a r = 0 :=
    weightedDeco_minimal_badContact_residueSign_eq_zero hn
      ⟨ht, hbox, hroot, hbad⟩ hzmin htpos hsplits
  have hd : p.derivative.eval r ≠ 0 := hsimpleA.eval_derivative_ne_zero hroot
  have hcontact : h.eval r = 0 := by
    unfold weightedDecoResidueSign at hsignZero
    exact (mul_eq_zero.mp hsignZero).resolve_right hd
  have hmM : m < M := by
    dsimp only [m, M]
    linarith
  have hcoordinate (j : Fin n) :
      let Gj :=
        ((weightedDecoParameterImage w (Finset.univ.erase j) a).eval r /
            p.derivative.eval r) *
          (-(1 + r + a j) / r - h.derivative.eval r / p.derivative.eval r)
      (a j = m → 0 ≤ Gj) ∧ (a j = M → Gj ≤ 0) ∧
        (m < a j → a j < M → Gj = 0) := by
    dsimp only
    have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
    obtain ⟨ρ, hρbase, hρroot, hρderiv⟩ :=
      exists_hasDerivAt_weightedDecoParameterResidueAt_contact_factor
        hj hroot hrneg hsimpleA hcontact
    let q : ℝ → ℝ := fun c =>
      (weightedDecoParameterCompanionAt w Finset.univ a j c).eval (ρ c) /
        (weightedDecoParameterImageAt w Finset.univ a j c).derivative.eval (ρ c)
    have hqbase : q (a j) = 0 := by
      dsimp only [q]
      rw [hρbase, weightedDecoParameterCompanionAt_self w hj,
        weightedDecoParameterImageAt_self w hj]
      rw [hcontact, zero_div]
    have hqnonneg : ∀ᶠ c in nhdsWithin (a j) (Icc m M), 0 ≤ q c := by
      have hρroot' : ∀ᶠ c in nhdsWithin (a j) (Icc m M),
          (weightedDecoParameterImageAt w Finset.univ a j c).IsRoot (ρ c) :=
        hρroot.filter_mono inf_le_left
      filter_upwards [hρroot', self_mem_nhdsWithin] with c hcroot hc
      let b := Function.update a j c
      have hbbox : weightedDecoExpandingBox z.1 b :=
        weightedDecoExpandingBox_update hbox j hc
      have hbCube : b ∈ weightedDecoParameterCube n :=
        weightedDecoParameterCube_of_expandingBox ht hbbox
      have hrActual : (weightedDecoParameterImage w Finset.univ b).IsRoot (ρ c) := by
        rw [weightedDecoParameterImage_update hj]
        exact hcroot
      have hsign : 0 ≤ weightedDecoResidueSign w n b (ρ c) :=
        weightedDeco_residueSign_nonneg_in_minimal_box hn
          ⟨ht, hbox, hroot, hbad⟩ hzmin htpos hsplits hbbox hrActual
      have hdc :
          (weightedDecoParameterImage w Finset.univ b).derivative.eval (ρ c) ≠ 0 :=
        (hsimple b hbCube).eval_derivative_ne_zero hrActual
      dsimp only [q]
      rw [← weightedDecoParameterCompanion_update hj c,
        ← weightedDecoParameterImage_update hj c]
      unfold weightedDecoResidueSign at hsign
      rw [show
          (weightedDecoParameterCompanion w Finset.univ b).eval (ρ c) /
              (weightedDecoParameterImage w Finset.univ b).derivative.eval (ρ c) =
            ((weightedDecoParameterCompanion w Finset.univ b).eval (ρ c) *
                (weightedDecoParameterImage w Finset.univ b).derivative.eval (ρ c)) /
              ((weightedDecoParameterImage w Finset.univ b).derivative.eval (ρ c)) ^ 2 by
        field_simp [hdc]
        ]
      exact div_nonneg hsign (sq_nonneg _)
    have hlocal : IsLocalMinOn q (Icc m M) (a j) := by
      change ∀ᶠ c in nhdsWithin (a j) (Icc m M), q (a j) ≤ q c
      simpa only [hqbase, zero_le] using hqnonneg
    exact hasDerivAt_sign_conditions_of_isLocalMinOn_Icc hmM hlocal hρderiv
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact (hcoordinate j).1
  · intro j
    exact (hcoordinate j).2.1
  · intro j
    exact (hcoordinate j).2.2

/-- If the deletion-to-full root residues are positive, an earliest bad
contact lies on the diagonal. -/
theorem weightedDeco_minimal_badContact_coordinates_eq
    {w : ℝ} {n : ℕ} (hn : n ≠ 0)
    {z : ℝ × ((Fin n → ℝ) × ℝ)}
    (hz : z ∈ weightedDecoBadContactSet w n)
    (hzmin : ∀ y ∈ weightedDecoBadContactSet w n, z.1 ≤ y.1)
    (htpos : 0 < z.1)
    (hsplits : ∀ b ∈ weightedDecoParameterCube n,
      (weightedDecoParameterImage w Finset.univ b).Splits)
    (hsimple : ∀ b ∈ weightedDecoParameterCube n,
      HasSimpleRoots (weightedDecoParameterImage w Finset.univ b))
    (hrootsNeg : ∀ b ∈ weightedDecoParameterCube n, ∀ r,
      (weightedDecoParameterImage w Finset.univ b).IsRoot r → r < 0)
    (halpha : ∀ j : Fin n,
      0 < (weightedDecoParameterImage w (Finset.univ.erase j) z.2.1).eval z.2.2 /
        (weightedDecoParameterImage w Finset.univ z.2.1).derivative.eval z.2.2) :
    ∀ i j, z.2.1 i = z.2.1 j := by
  rcases hz with ⟨ht, hbox, hroot, hbad⟩
  have hsigns := weightedDeco_minimal_badContact_coordinate_signs hn
    ⟨ht, hbox, hroot, hbad⟩ hzmin htpos hsplits hsimple hrootsNeg
  let a := z.2.1
  let r := z.2.2
  let m := (1 - z.1) / 2
  let M := (1 + z.1) / 2
  let d := (weightedDecoParameterImage w Finset.univ a).derivative.eval r
  let α := fun j : Fin n =>
    (weightedDecoParameterImage w (Finset.univ.erase j) a).eval r / d
  let μ := (weightedDecoParameterCompanion w Finset.univ a).derivative.eval r / d
  let g := fun j : Fin n => α j * (-(1 + r + a j) / r - μ)
  apply weightedDeco_box_first_contact_coordinates_eq a α g m M r μ
  · exact hrootsNeg a (weightedDecoParameterCube_of_expandingBox ht hbox) r hroot
  · exact halpha
  · intro i
    rfl
  · exact fun i => (hbox i).1
  · exact fun i => (hbox i).2
  · exact hsigns.1
  · exact hsigns.2.1
  · exact hsigns.2.2

end RealRooted.Applications.OEIS
