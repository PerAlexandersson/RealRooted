/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortTailCheck
public meta import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortTailCheck

/-!
# Checked low-cutoff tail certificates

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

certify_short_cutoff checked3 3 18
certify_short_cutoff checked4 4 23
certify_short_cutoff checked5 5 24
certify_short_cutoff checked6 6 25
certify_short_cutoff checked7 7 25
certify_short_cutoff checked8 8 27
certify_short_cutoff checked9 9 27
certify_short_cutoff checked10 10 29
certify_short_cutoff checked11 11 29
certify_short_cutoff checked12 12 31

/-- Every short cutoff has both checked prefix margins and a tail anchor. -/
theorem exists_shortCertificates {k : ℕ} (hk : 3 ≤ k) (hk12 : k ≤ 12) :
    ∃ H ≤ 31, shortTailCertificate k H = true ∧ shortPrefixCertificate k H = true := by
  interval_cases k
  · exact ⟨18, by decide, checked3, checked3_prefix⟩
  · exact ⟨23, by decide, checked4, checked4_prefix⟩
  · exact ⟨24, by decide, checked5, checked5_prefix⟩
  · exact ⟨25, by decide, checked6, checked6_prefix⟩
  · exact ⟨25, by decide, checked7, checked7_prefix⟩
  · exact ⟨27, by decide, checked8, checked8_prefix⟩
  · exact ⟨27, by decide, checked9, checked9_prefix⟩
  · exact ⟨29, by decide, checked10, checked10_prefix⟩
  · exact ⟨29, by decide, checked11, checked11_prefix⟩
  · exact ⟨31, by decide, checked12, checked12_prefix⟩

/-- Every short cutoff has a checked anchor at rank at most thirty-one. -/
theorem exists_shortTailCertificate {k : ℕ} (hk : 3 ≤ k) (hk12 : k ≤ 12) :
    ∃ H ≤ 31, shortTailCertificate k H = true := by
  obtain ⟨H, hH, hc, _⟩ := exists_shortCertificates hk hk12
  exact ⟨H, hH, hc⟩

end RealRooted.LongCycleDescents.Structural
