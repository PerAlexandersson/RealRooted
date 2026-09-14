import RealRooted.Applications.OEIS.A144438.DecorationOrbit
import RealRooted.Combinatorics.ComparisonBottom

/-!
# Comparison-bottom support of eligible decorations

For an eligible chronological `(0, 2)` pair, the larger final label is never
a comparison bottom of the normalized inverse word. The smaller label may or
may not be a comparison bottom; this dichotomy partitions eligible starts into
active and inactive ones and isolates the support fixed by every decoration.
-/

namespace RealRooted.Applications.OEIS.DecoNormalizedCode

/-- The smaller final label attached to an eligible chronological pair. -/
def leftLabel (h : Nat) (j : Fin h) : Nat := h - (j.1 + 1)

/-- The larger final label attached to an eligible chronological pair. -/
def rightLabel (h : Nat) (j : Fin h) : Nat := h - j.1

/-- The right endpoint of an eligible swap is never a normalized comparison
bottom. -/
theorem Eligible.rightLabel_not_mem_comparisonBottomSupport {h : Nat}
    {c : DecoNormalizedCode h} {j : Fin h} (hj : c.Eligible j) :
    rightLabel h j ∉ MinimumInsertionWord.comparisonBottomSupport
      c.toDecoCode.inverseWord := by
  rcases hj with ⟨hjLower, hjBound, hjZero, hjTwo⟩
  have hprefixLength : j.1 ≤ h := by lia
  have hprefixNonempty : c.toDecoCode.inverseWordPrefix j.1 ≠ [] := by
    intro hnil
    have hlength := c.toDecoCode.length_inverseWordPrefix hprefixLength
    rw [hnil] at hlength
    simp only [List.length_nil] at hlength
    lia
  obtain ⟨a, w, hpref⟩ := List.exists_cons_of_ne_nil hprefixNonempty
  have hprefLength : (a :: w).length = j.1 := by
    rw [← hpref]
    exact c.toDecoCode.length_inverseWordPrefix hprefixLength
  have hprefixPos : MinimumInsertionWord.IsPositive (a :: w) := by
    rw [← hpref]
    exact c.toDecoCode.inverseWordPrefix_isPositive j.1
  let localWord := MinimumInsertionWord.step 2
    (MinimumInsertionWord.step 0 (a :: w))
  let suffix := c.toDecoCode.entryList.drop (j.1 + 2)
  have hinnerLength :
      (MinimumInsertionWord.step 0 (a :: w)).length = j.1 + 1 := by
    rw [MinimumInsertionWord.length_step (by simp)]
    rw [hprefLength]
  have hlocalLength : localWord.length = j.1 + 2 := by
    dsimp [localWord]
    rw [MinimumInsertionWord.length_step (by rw [hinnerLength]; lia),
      hinnerLength]
  have hlocalPos : MinimumInsertionWord.IsPositive localWord := by
    exact MinimumInsertionWord.isPositive_step 2
      (MinimumInsertionWord.step 0 (a :: w))
  have hsuffixValid : MinimumInsertionWord.ValidFrom localWord.length suffix := by
    have hdrop := c.toDecoCode.validFrom_entryList.drop
      (k := j.1 + 2) (by simp [DecoCode.length_entryList]; lia)
    rw [hlocalLength]
    simpa [suffix] using hdrop
  have hsuffixLength : suffix.length = h - (j.1 + 2) := by
    simp [suffix, DecoCode.length_entryList]
  intro hmem
  rw [DecoCode.inverseWord_eq_decodeFrom_take_pair_drop
    c.toDecoCode j.1 hjBound, hjZero, hjTwo, hpref] at hmem
  have hright : h - j.1 = 2 + suffix.length := by
    rw [hsuffixLength]
    lia
  change h - j.1 ∈ _ at hmem
  rw [hright] at hmem
  change 2 + suffix.length ∈
    MinimumInsertionWord.comparisonBottomSupport
      (MinimumInsertionWord.decodeFrom localWord suffix) at hmem
  have htwo :=
    MinimumInsertionWord.add_length_mem_comparisonBottomSupport_decodeFrom_imp
      hlocalPos hsuffixValid (x := 2) (by decide) hmem
  have hone := MinimumInsertionWord.succ_mem_comparisonBottomSupport_step_imp
    (MinimumInsertionWord.isPositive_step 0 (a :: w))
    (r := 2) (x := 1) (by rw [hinnerLength]; lia) (by decide) htwo
  exact MinimumInsertionWord.one_not_mem_comparisonBottomSupport_step_zero
    hprefixPos hone

/-- Distinct eligible starts have distinct left labels. -/
def leftLabelEmbedding {h : Nat} (c : DecoNormalizedCode h) :
    EligibleStart c ↪ Nat where
  toFun j := leftLabel h j.1
  inj' := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact (finalSwap_support_disjoint i.2 j.2 hne).1 hij

/-- The decoration selecting every eligible start. -/
noncomputable def Decoration.full {h : Nat} (c : DecoNormalizedCode h) :
    Decoration c where
  starts := c.eligibleStarts
  starts_subset := fun _ hj => hj

/-- Every eligible start, bundled with its proof. -/
noncomputable def allEligibleStarts {h : Nat} (c : DecoNormalizedCode h) :
    Finset (EligibleStart c) := (Decoration.full c).eligibleFinset

@[simp] theorem mem_allEligibleStarts {h : Nat} (c : DecoNormalizedCode h)
    (j : EligibleStart c) : j ∈ c.allEligibleStarts := by
  rw [allEligibleStarts, Decoration.mem_eligibleFinset]
  exact mem_eligibleStarts.mpr j.2

/-- Eligible starts whose left label is an actual normalized comparison
bottom. -/
noncomputable def activeEligibleStarts {h : Nat} (c : DecoNormalizedCode h) :
    Finset (EligibleStart c) :=
  c.allEligibleStarts.filter fun j =>
    leftLabel h j.1 ∈ MinimumInsertionWord.comparisonBottomSupport
      c.toDecoCode.inverseWord

/-- Eligible starts whose swap fixes the normalized comparison-bottom
support. -/
noncomputable def inactiveEligibleStarts {h : Nat} (c : DecoNormalizedCode h) :
    Finset (EligibleStart c) :=
  c.allEligibleStarts \ c.activeEligibleStarts

@[simp] theorem mem_activeEligibleStarts {h : Nat}
    (c : DecoNormalizedCode h) (j : EligibleStart c) :
    j ∈ c.activeEligibleStarts ↔
      leftLabel h j.1 ∈ MinimumInsertionWord.comparisonBottomSupport
        c.toDecoCode.inverseWord := by
  simp [activeEligibleStarts]

@[simp] theorem mem_inactiveEligibleStarts {h : Nat}
    (c : DecoNormalizedCode h) (j : EligibleStart c) :
    j ∈ c.inactiveEligibleStarts ↔
      leftLabel h j.1 ∉ MinimumInsertionWord.comparisonBottomSupport
        c.toDecoCode.inverseWord := by
  simp [inactiveEligibleStarts]

/-- The support pattern at an active eligible start is left-only. -/
theorem active_support_pattern {h : Nat} (c : DecoNormalizedCode h)
    {j : EligibleStart c} (hj : j ∈ c.activeEligibleStarts) :
    leftLabel h j.1 ∈ MinimumInsertionWord.comparisonBottomSupport
        c.toDecoCode.inverseWord ∧
      rightLabel h j.1 ∉ MinimumInsertionWord.comparisonBottomSupport
        c.toDecoCode.inverseWord :=
  ⟨(mem_activeEligibleStarts c j).mp hj,
    j.2.rightLabel_not_mem_comparisonBottomSupport⟩

/-- The support pattern at an inactive eligible start contains neither
endpoint. -/
theorem inactive_support_pattern {h : Nat} (c : DecoNormalizedCode h)
    {j : EligibleStart c} (hj : j ∈ c.inactiveEligibleStarts) :
    leftLabel h j.1 ∉ MinimumInsertionWord.comparisonBottomSupport
        c.toDecoCode.inverseWord ∧
      rightLabel h j.1 ∉ MinimumInsertionWord.comparisonBottomSupport
        c.toDecoCode.inverseWord :=
  ⟨(mem_inactiveEligibleStarts c j).mp hj,
    j.2.rightLabel_not_mem_comparisonBottomSupport⟩

/-- All endpoint labels belonging to eligible starts. -/
noncomputable def eligibleEndpointSupport {h : Nat}
    (c : DecoNormalizedCode h) : Finset Nat :=
  c.allEligibleStarts.biUnion fun j => {leftLabel h j.1, rightLabel h j.1}

/-- Comparison bottoms untouched by every eligible swap. -/
noncomputable def fixedBottomSupport {h : Nat}
    (c : DecoNormalizedCode h) : Finset Nat :=
  MinimumInsertionWord.comparisonBottomSupport c.toDecoCode.inverseWord \
    c.eligibleEndpointSupport

/-- The normalized comparison-bottom support is the union of its fixed part
and the left labels of the active eligible starts. -/
theorem comparisonBottomSupport_eq_fixed_union_active {h : Nat}
    (c : DecoNormalizedCode h) :
    MinimumInsertionWord.comparisonBottomSupport c.toDecoCode.inverseWord =
      c.fixedBottomSupport ∪
        c.activeEligibleStarts.map c.leftLabelEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hendpoint : x ∈ c.eligibleEndpointSupport
    · rw [eligibleEndpointSupport, Finset.mem_biUnion] at hendpoint
      obtain ⟨j, hj, hxj⟩ := hendpoint
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxj
      rw [Finset.mem_union]
      right
      rw [Finset.mem_map]
      rcases hxj with hleft | hright
      · have hactive : j ∈ c.activeEligibleStarts := by
          rw [mem_activeEligibleStarts]
          simpa [← hleft] using hx
        exact ⟨j, hactive, by simpa [leftLabelEmbedding] using hleft.symm⟩
      · exact
          (j.2.rightLabel_not_mem_comparisonBottomSupport (hright ▸ hx)).elim
    · rw [Finset.mem_union]
      left
      exact Finset.mem_sdiff.mpr ⟨hx, hendpoint⟩
  · rw [Finset.mem_union]
    rintro (hfixed | hactive)
    · exact (Finset.mem_sdiff.mp hfixed).1
    · rw [Finset.mem_map] at hactive
      obtain ⟨j, hj, hjx⟩ := hactive
      have hleft := (mem_activeEligibleStarts c j).mp hj
      rw [← hjx]
      simpa [leftLabelEmbedding] using hleft

end RealRooted.Applications.OEIS.DecoNormalizedCode
