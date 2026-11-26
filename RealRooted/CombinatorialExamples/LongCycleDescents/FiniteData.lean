/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Certificates
public import RealRooted.CombinatorialExamples.LongCycleDescents.Cycles
import Mathlib.Tactic

/-!
# Data-free coefficient checks through size seventeen

The only numerical inputs are dyadic interval endpoints from the source. Every
coefficient is recomputed in the kernel by the proved compressed necklace algorithm.
Each cutoff is a separate small kernel reduction; a single reduction of the
universal cutoff quantifier retains too much intermediate arithmetic.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Finite

open Necklace

/-- A common negative quotient grid at size 3. -/
private def nodes3 : Array Necklace.Dyadic :=
#[
  ⟨-1, 0⟩
]

private theorem checked3_3 : descentMesh 3 3 nodes3 = true := by
  decide +kernel

private theorem checked3 (k : Fin (3-2)) :
    descentMesh 3 (k.val + 3) nodes3 = true := by
  fin_cases k
  · exact checked3_3

/-- A common negative quotient grid at size 4. -/
private def nodes4 : Array Necklace.Dyadic :=
#[
  ⟨-11640527, 22⟩,
  ⟨-6045151, 24⟩
]

private theorem checked4_3 : descentMesh 4 3 nodes4 = true := by
  decide +kernel

private theorem checked4 (k : Fin (3-2)) :
    descentMesh 4 (k.val + 3) nodes4 = true := by
  fin_cases k
  · exact checked4_3

/-- A common negative quotient grid at size 6. -/
private def nodes6 : Array Necklace.Dyadic :=
#[
  ⟨-12842623, 20⟩,
  ⟨-4295759, 21⟩,
  ⟨-4095245, 23⟩,
  ⟨-10958625, 27⟩
]

private theorem checked6_3 : descentMesh 6 3 nodes6 = true := by
  decide +kernel

private theorem checked6_4 : descentMesh 6 4 nodes6 = true := by
  decide +kernel

private theorem checked6 (k : Fin (4-2)) :
    descentMesh 6 (k.val + 3) nodes6 = true := by
  fin_cases k
  · exact checked6_3
  · exact checked6_4

/-- A common negative quotient grid at size 7. -/
private def nodes7 : Array Necklace.Dyadic :=
#[
  ⟨-12132387, 19⟩,
  ⟨-481563, 17⟩,
  ⟨-1, 0⟩,
  ⟨-4566429, 24⟩,
  ⟨-2900037, 26⟩
]

private theorem checked7_3 : descentMesh 7 3 nodes7 = true := by
  decide +kernel

private theorem checked7_4 : descentMesh 7 4 nodes7 = true := by
  decide +kernel

private theorem checked7 (k : Fin (4-2)) :
    descentMesh 7 (k.val + 3) nodes7 = true := by
  fin_cases k
  · exact checked7_3
  · exact checked7_4

/-- A common negative quotient grid at size 8. -/
private def nodes8 : Array Necklace.Dyadic :=
#[
  ⟨-11080015, 18⟩,
  ⟨-12863317, 21⟩,
  ⟨-14597089, 23⟩,
  ⟨-2410369, 22⟩,
  ⟨-10940995, 26⟩,
  ⟨-6350961, 28⟩
]

private theorem checked8_3 : descentMesh 8 3 nodes8 = true := by
  decide +kernel

private theorem checked8_4 : descentMesh 8 4 nodes8 = true := by
  decide +kernel

private theorem checked8_5 : descentMesh 8 5 nodes8 = true := by
  decide +kernel

private theorem checked8 (k : Fin (5-2)) :
    descentMesh 8 (k.val + 3) nodes8 = true := by
  fin_cases k
  · exact checked8_3
  · exact checked8_4
  · exact checked8_5

/-- A common negative quotient grid at size 9. -/
private def nodes9 : Array Necklace.Dyadic :=
#[
  ⟨-9894933, 17⟩,
  ⟨-2569315, 18⟩,
  ⟨-11640527, 22⟩,
  ⟨-1, 0⟩,
  ⟨-6045151, 24⟩,
  ⟨-13694067, 27⟩,
  ⟨-14223187, 30⟩
]

private theorem checked9_3 : descentMesh 9 3 nodes9 = true := by
  decide +kernel

private theorem checked9_4 : descentMesh 9 4 nodes9 = true := by
  decide +kernel

private theorem checked9_5 : descentMesh 9 5 nodes9 = true := by
  decide +kernel

private theorem checked9 (k : Fin (5-2)) :
    descentMesh 9 (k.val + 3) nodes9 = true := by
  fin_cases k
  · exact checked9_3
  · exact checked9_4
  · exact checked9_5

/-- A common negative quotient grid at size 10. -/
private def nodes10 : Array Necklace.Dyadic :=
#[
  ⟨-4349717, 15⟩,
  ⟨-15952867, 20⟩,
  ⟨-2201201, 19⟩,
  ⟨-6589123, 22⟩,
  ⟨-10679531, 24⟩,
  ⟨-7992085, 25⟩,
  ⟨-8822081, 27⟩,
  ⟨-1011111, 27⟩
]

private theorem checked10_3 : descentMesh 10 3 nodes10 = true := by
  decide +kernel

private theorem checked10_4 : descentMesh 10 4 nodes10 = true := by
  decide +kernel

private theorem checked10_5 : descentMesh 10 5 nodes10 = true := by
  decide +kernel

private theorem checked10_6 : descentMesh 10 6 nodes10 = true := by
  decide +kernel

private theorem checked10 (k : Fin (6-2)) :
    descentMesh 10 (k.val + 3) nodes10 = true := by
  fin_cases k
  · exact checked10_3
  · exact checked10_4
  · exact checked10_5
  · exact checked10_6

/-- A common negative quotient grid at size 11. -/
private def nodes11 : Array Necklace.Dyadic :=
#[
  ⟨-3780847, 14⟩,
  ⟨-12132387, 19⟩,
  ⟨-12863317, 21⟩,
  ⟨-9732927, 22⟩,
  ⟨-1, 0⟩,
  ⟨-14459935, 25⟩,
  ⟨-10940995, 26⟩,
  ⟨-2900037, 26⟩,
  ⟨-4652975, 30⟩
]

private theorem checked11_3 : descentMesh 11 3 nodes11 = true := by
  decide +kernel

private theorem checked11_4 : descentMesh 11 4 nodes11 = true := by
  decide +kernel

private theorem checked11_5 : descentMesh 11 5 nodes11 = true := by
  decide +kernel

private theorem checked11_6 : descentMesh 11 6 nodes11 = true := by
  decide +kernel

private theorem checked11 (k : Fin (6-2)) :
    descentMesh 11 (k.val + 3) nodes11 = true := by
  fin_cases k
  · exact checked11_3
  · exact checked11_4
  · exact checked11_5
  · exact checked11_6

/-- A common negative quotient grid at size 12. -/
private def nodes12 : Array Necklace.Dyadic :=
#[
  ⟨-13033225, 15⟩,
  ⟨-1136351, 15⟩,
  ⟨-4584911, 19⟩,
  ⟨-13807009, 22⟩,
  ⟨-12284435, 23⟩,
  ⟨-5728285, 23⟩,
  ⟨-1274149, 22⟩,
  ⟨-15347897, 27⟩,
  ⟨-15481297, 29⟩,
  ⟨-10798363, 32⟩
]

private theorem checked12_3 : descentMesh 12 3 nodes12 = true := by
  decide +kernel

private theorem checked12_4 : descentMesh 12 4 nodes12 = true := by
  decide +kernel

private theorem checked12_5 : descentMesh 12 5 nodes12 = true := by
  decide +kernel

private theorem checked12_6 : descentMesh 12 6 nodes12 = true := by
  decide +kernel

private theorem checked12_7 : descentMesh 12 7 nodes12 = true := by
  decide +kernel

private theorem checked12 (k : Fin (7-2)) :
    descentMesh 12 (k.val + 3) nodes12 = true := by
  fin_cases k
  · exact checked12_3
  · exact checked12_4
  · exact checked12_5
  · exact checked12_6
  · exact checked12_7

/-- A common negative quotient grid at size 13. -/
private def nodes13 : Array Necklace.Dyadic :=
#[
  ⟨-5578875, 13⟩,
  ⟨-1683929, 15⟩,
  ⟨-12842623, 20⟩,
  ⟨-1190115, 18⟩,
  ⟨-4295759, 21⟩,
  ⟨-1, 0⟩,
  ⟨-4095245, 23⟩,
  ⟨-14781921, 26⟩,
  ⟨-10958625, 27⟩,
  ⟨-10447107, 29⟩,
  ⟨-12613429, 33⟩
]

private theorem checked13_3 : descentMesh 13 3 nodes13 = true := by
  decide +kernel

private theorem checked13_4 : descentMesh 13 4 nodes13 = true := by
  decide +kernel

private theorem checked13_5 : descentMesh 13 5 nodes13 = true := by
  decide +kernel

private theorem checked13_6 : descentMesh 13 6 nodes13 = true := by
  decide +kernel

private theorem checked13_7 : descentMesh 13 7 nodes13 = true := by
  decide +kernel

private theorem checked13 (k : Fin (7-2)) :
    descentMesh 13 (k.val + 3) nodes13 = true := by
  fin_cases k
  · exact checked13_3
  · exact checked13_4
  · exact checked13_5
  · exact checked13_6
  · exact checked13_7

/-- A common negative quotient grid at size 14. -/
private def nodes14 : Array Necklace.Dyadic :=
#[
  ⟨-9502315, 13⟩,
  ⟨-9894933, 17⟩,
  ⟨-554549, 15⟩,
  ⟨-12863317, 21⟩,
  ⟨-11640527, 22⟩,
  ⟨-5835279, 22⟩,
  ⟨-12059191, 24⟩,
  ⟨-6045151, 24⟩,
  ⟨-10940995, 26⟩,
  ⟨-7930853, 27⟩,
  ⟨-14223187, 30⟩,
  ⟨-925679, 30⟩
]

private theorem checked14_3 : descentMesh 14 3 nodes14 = true := by
  decide +kernel

private theorem checked14_4 : descentMesh 14 4 nodes14 = true := by
  decide +kernel

private theorem checked14_5 : descentMesh 14 5 nodes14 = true := by
  decide +kernel

private theorem checked14_6 : descentMesh 14 6 nodes14 = true := by
  decide +kernel

private theorem checked14_7 : descentMesh 14 7 nodes14 = true := by
  decide +kernel

private theorem checked14_8 : descentMesh 14 8 nodes14 = true := by
  decide +kernel

private theorem checked14 (k : Fin (8-2)) :
    descentMesh 14 (k.val + 3) nodes14 = true := by
  fin_cases k
  · exact checked14_3
  · exact checked14_4
  · exact checked14_5
  · exact checked14_6
  · exact checked14_7
  · exact checked14_8

/-- A common negative quotient grid at size 15. -/
private def nodes15 : Array Necklace.Dyadic :=
#[
  ⟨-16117061, 13⟩,
  ⟨-7217943, 16⟩,
  ⟨-12132387, 19⟩,
  ⟨-8555533, 20⟩,
  ⟨-481563, 17⟩,
  ⟨-15670441, 23⟩,
  ⟨-1, 0⟩,
  ⟨-1122635, 21⟩,
  ⟨-4566429, 24⟩,
  ⟨-16449881, 27⟩,
  ⟨-2900037, 26⟩,
  ⟨-9749141, 30⟩,
  ⟨-4366103, 33⟩
]

private theorem checked15_3 : descentMesh 15 3 nodes15 = true := by
  decide +kernel

private theorem checked15_4 : descentMesh 15 4 nodes15 = true := by
  decide +kernel

private theorem checked15_5 : descentMesh 15 5 nodes15 = true := by
  decide +kernel

private theorem checked15_6 : descentMesh 15 6 nodes15 = true := by
  decide +kernel

private theorem checked15_7 : descentMesh 15 7 nodes15 = true := by
  decide +kernel

private theorem checked15_8 : descentMesh 15 8 nodes15 = true := by
  decide +kernel

private theorem checked15 (k : Fin (8-2)) :
    descentMesh 15 (k.val + 3) nodes15 = true := by
  fin_cases k
  · exact checked15_3
  · exact checked15_4
  · exact checked15_5
  · exact checked15_6
  · exact checked15_7
  · exact checked15_8

/-- A common negative quotient grid at size 16. -/
private def nodes16 : Array Necklace.Dyadic :=
#[
  ⟨-6810693, 11⟩,
  ⟨-5235925, 15⟩,
  ⟨-8226015, 18⟩,
  ⟨-5622107, 19⟩,
  ⟨-10023251, 21⟩,
  ⟨-10253177, 22⟩,
  ⟨-11223233, 23⟩,
  ⟨-12539835, 24⟩,
  ⟨-1715779, 22⟩,
  ⟨-7020551, 25⟩,
  ⟨-3129109, 25⟩,
  ⟨-8554415, 28⟩,
  ⟨-6719801, 30⟩,
  ⟨-5166049, 34⟩
]

private theorem checked16_3 : descentMesh 16 3 nodes16 = true := by
  decide +kernel

private theorem checked16_4 : descentMesh 16 4 nodes16 = true := by
  decide +kernel

private theorem checked16_5 : descentMesh 16 5 nodes16 = true := by
  decide +kernel

private theorem checked16_6 : descentMesh 16 6 nodes16 = true := by
  decide +kernel

private theorem checked16_7 : descentMesh 16 7 nodes16 = true := by
  decide +kernel

private theorem checked16_8 : descentMesh 16 8 nodes16 = true := by
  decide +kernel

private theorem checked16_9 : descentMesh 16 9 nodes16 = true := by
  decide +kernel

private theorem checked16 (k : Fin (9-2)) :
    descentMesh 16 (k.val + 3) nodes16 = true := by
  fin_cases k
  · exact checked16_3
  · exact checked16_4
  · exact checked16_5
  · exact checked16_6
  · exact checked16_7
  · exact checked16_8
  · exact checked16_9

/-- A common negative quotient grid at size 17. -/
private def nodes17 : Array Necklace.Dyadic :=
#[
  ⟨-11479505, 11⟩,
  ⟨-3780847, 14⟩,
  ⟨-11080015, 18⟩,
  ⟨-7318425, 19⟩,
  ⟨-12863317, 21⟩,
  ⟨-13159891, 22⟩,
  ⟨-14597089, 23⟩,
  ⟨-1, 0⟩,
  ⟨-2410369, 22⟩,
  ⟨-10694427, 25⟩,
  ⟨-10940995, 26⟩,
  ⟨-4807643, 26⟩,
  ⟨-6350961, 28⟩,
  ⟨-4652975, 30⟩,
  ⟨-12259891, 36⟩
]

private theorem checked17_3 : descentMesh 17 3 nodes17 = true := by
  decide +kernel

private theorem checked17_4 : descentMesh 17 4 nodes17 = true := by
  decide +kernel

private theorem checked17_5 : descentMesh 17 5 nodes17 = true := by
  decide +kernel

private theorem checked17_6 : descentMesh 17 6 nodes17 = true := by
  decide +kernel

private theorem checked17_7 : descentMesh 17 7 nodes17 = true := by
  decide +kernel

private theorem checked17_8 : descentMesh 17 8 nodes17 = true := by
  decide +kernel

private theorem checked17_9 : descentMesh 17 9 nodes17 = true := by
  decide +kernel

private theorem checked17 (k : Fin (9-2)) :
    descentMesh 17 (k.val + 3) nodes17 = true := by
  fin_cases k
  · exact checked17_3
  · exact checked17_4
  · exact checked17_5
  · exact checked17_6
  · exact checked17_7
  · exact checked17_8
  · exact checked17_9

/-- Every nonexceptional size through seventeen has one checked grid for its cutoff rows. -/
theorem exists_descentMesh {n : ℕ} (hn : 3 ≤ n) (hi : n ≤ 17) (five : n ≠ 5) :
    ∃ nodes : Array Necklace.Dyadic, nodes.size = n - 2 ∧
      ∀ k : Fin (lastRepresentative n - 2), descentMesh n (k.val + 3) nodes = true := by
  interval_cases n
  · exact ⟨nodes3, by decide, checked3⟩
  · exact ⟨nodes4, by decide, checked4⟩
  · exact (five rfl).elim
  · exact ⟨nodes6, by decide, checked6⟩
  · exact ⟨nodes7, by decide, checked7⟩
  · exact ⟨nodes8, by decide, checked8⟩
  · exact ⟨nodes9, by decide, checked9⟩
  · exact ⟨nodes10, by decide, checked10⟩
  · exact ⟨nodes11, by decide, checked11⟩
  · exact ⟨nodes12, by decide, checked12⟩
  · exact ⟨nodes13, by decide, checked13⟩
  · exact ⟨nodes14, by decide, checked14⟩
  · exact ⟨nodes15, by decide, checked15⟩
  · exact ⟨nodes16, by decide, checked16⟩
  · exact ⟨nodes17, by decide, checked17⟩

end RealRooted.LongCycleDescents.Finite
