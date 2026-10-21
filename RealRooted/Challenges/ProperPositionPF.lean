import RealRooted.MultiplierSequence.ProperPositionPF

/-!
# PF multipliers and proper position

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "pf-multiplier-proper-position"
formalized = "2026-10-11"
references = [
  "BorceaBranden2009I",
  "BorceaBranden2010",
  "Branden2015",
]

[[theorems]]
name = "RealRooted.IsFinitePFMultiplierSequence.interl_diagonalOperator"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Finite PF multipliers preserve directed interlacing"
headline = true

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Nonpositive adjacent multipliers reverse strict interlacing"

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_of_ratio_nonneg"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Nonnegative ratio preserves strict orientation"

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_reverse_of_ratio_nonpos"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Nonpositive ratio reverses strict orientation"

[[theorems]]
name = "RealRooted.IsFiniteMultiplierSequence.strictInterl_diagonalOperator_both_of_ratio_eq_zero"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Zero ratio gives both strict orientations"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.strictInterl_weightedSum_left_of_pos"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Positive multipliers preserve common-left weighted sums"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.strictInterl_weightedSum_right_of_pos"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Positive multipliers preserve common-right weighted sums"

[[theorems]]
name = "RealRooted.IsInterlacingSeq0NonnegRealRooted.diagonalOperator_of_finitePF"
module = "RealRooted.MultiplierSequence.ProperPositionPF"
label = "Finite PF multipliers preserve ordered PF lists"
-->

<!-- realrooted-catalog-content -->
# PF multipliers and proper position

For a finite PF multiplier sequence on a degree box, we prove that its diagonal
operator preserves zero-aware directed interlacing of two PF polynomials in
that box.  This conclusion permits degree drops and zero outputs: it requires
neither nonzero top multipliers nor nonzero images.

For a finite multiplier sequence and a strictly interlacing pair, we also
record orientation criteria in the equal-degree case.  A nonpositive product
of the top adjacent multipliers reverses the strict orientation.  Equivalently,
a nonnegative adjacent ratio preserves the forward orientation, a nonpositive
ratio yields the reverse orientation, and a zero ratio yields both conclusions,
provided the indicated top multipliers are nonzero.

For a strictly positive multiplier sequence, we transport strict interlacing
through nontrivial nonnegative weighted sums of a common-left or common-right
family with positive leading coefficients.  Finally, a finite PF multiplier
sequence maps a bounded-degree `IsInterlacingSeq0NonnegRealRooted` list to a
list with the same zero-aware interlacing, nonnegative-coefficient, and
nonzero splitness properties.

## References

See [@BorceaBranden2009I; @BorceaBranden2010; @Branden2015].
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.ProperPositionPF

end RealRooted.Challenges.ProperPositionPF
