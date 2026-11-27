/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
public import RealRooted.Basic.ProperPosition
public import RealRooted.SimpleRoots
import RealRooted.CombinatorialExamples.CatalanWordPeaks.Certificates
import RealRooted.CombinatorialExamples.CatalanWordPeaks.FiniteData
import Mathlib.Tactic

/-!
# Kernel-checked finite Catalan strict-peak certificates

These theorems concern exactly the polynomial defined by the binomial formula.
All arithmetic certificates are reduced by the kernel, without native evaluation
or increased resource limits. The analytic tail is not used here.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.Finite

private def check (n : ℕ) : Bool :=
  checkRow n (centers.getD n #[]) &&
    (if n < 150 then checkPair n (centers.getD n #[]) (centers.getD (n + 1) #[]) else true)

private theorem checked000 : check 0 = true := by decide +kernel
private theorem checked001 : check 1 = true := by decide +kernel
private theorem checked002 : check 2 = true := by decide +kernel
private theorem checked003 : check 3 = true := by decide +kernel
private theorem checked004 : check 4 = true := by decide +kernel
private theorem checked005 : check 5 = true := by decide +kernel
private theorem checked006 : check 6 = true := by decide +kernel
private theorem checked007 : check 7 = true := by decide +kernel
private theorem checked008 : check 8 = true := by decide +kernel
private theorem checked009 : check 9 = true := by decide +kernel
private theorem checked010 : check 10 = true := by decide +kernel
private theorem checked011 : check 11 = true := by decide +kernel
private theorem checked012 : check 12 = true := by decide +kernel
private theorem checked013 : check 13 = true := by decide +kernel
private theorem checked014 : check 14 = true := by decide +kernel
private theorem checked015 : check 15 = true := by decide +kernel
private theorem checked016 : check 16 = true := by decide +kernel
private theorem checked017 : check 17 = true := by decide +kernel
private theorem checked018 : check 18 = true := by decide +kernel
private theorem checked019 : check 19 = true := by decide +kernel
private theorem checked020 : check 20 = true := by decide +kernel
private theorem checked021 : check 21 = true := by decide +kernel
private theorem checked022 : check 22 = true := by decide +kernel
private theorem checked023 : check 23 = true := by decide +kernel
private theorem checked024 : check 24 = true := by decide +kernel
private theorem checked025 : check 25 = true := by decide +kernel
private theorem checked026 : check 26 = true := by decide +kernel
private theorem checked027 : check 27 = true := by decide +kernel
private theorem checked028 : check 28 = true := by decide +kernel
private theorem checked029 : check 29 = true := by decide +kernel
private theorem checked030 : check 30 = true := by decide +kernel
private theorem checked031 : check 31 = true := by decide +kernel
private theorem checked032 : check 32 = true := by decide +kernel
private theorem checked033 : check 33 = true := by decide +kernel
private theorem checked034 : check 34 = true := by decide +kernel
private theorem checked035 : check 35 = true := by decide +kernel
private theorem checked036 : check 36 = true := by decide +kernel
private theorem checked037 : check 37 = true := by decide +kernel
private theorem checked038 : check 38 = true := by decide +kernel
private theorem checked039 : check 39 = true := by decide +kernel
private theorem checked040 : check 40 = true := by decide +kernel
private theorem checked041 : check 41 = true := by decide +kernel
private theorem checked042 : check 42 = true := by decide +kernel
private theorem checked043 : check 43 = true := by decide +kernel
private theorem checked044 : check 44 = true := by decide +kernel
private theorem checked045 : check 45 = true := by decide +kernel
private theorem checked046 : check 46 = true := by decide +kernel
private theorem checked047 : check 47 = true := by decide +kernel
private theorem checked048 : check 48 = true := by decide +kernel
private theorem checked049 : check 49 = true := by decide +kernel
private theorem checked050 : check 50 = true := by decide +kernel
private theorem checked051 : check 51 = true := by decide +kernel
private theorem checked052 : check 52 = true := by decide +kernel
private theorem checked053 : check 53 = true := by decide +kernel
private theorem checked054 : check 54 = true := by decide +kernel
private theorem checked055 : check 55 = true := by decide +kernel
private theorem checked056 : check 56 = true := by decide +kernel
private theorem checked057 : check 57 = true := by decide +kernel
private theorem checked058 : check 58 = true := by decide +kernel
private theorem checked059 : check 59 = true := by decide +kernel
private theorem checked060 : check 60 = true := by decide +kernel
private theorem checked061 : check 61 = true := by decide +kernel
private theorem checked062 : check 62 = true := by decide +kernel
private theorem checked063 : check 63 = true := by decide +kernel
private theorem checked064 : check 64 = true := by decide +kernel
private theorem checked065 : check 65 = true := by decide +kernel
private theorem checked066 : check 66 = true := by decide +kernel
private theorem checked067 : check 67 = true := by decide +kernel
private theorem checked068 : check 68 = true := by decide +kernel
private theorem checked069 : check 69 = true := by decide +kernel
private theorem checked070 : check 70 = true := by decide +kernel
private theorem checked071 : check 71 = true := by decide +kernel
private theorem checked072 : check 72 = true := by decide +kernel
private theorem checked073 : check 73 = true := by decide +kernel
private theorem checked074 : check 74 = true := by decide +kernel
private theorem checked075 : check 75 = true := by decide +kernel
private theorem checked076 : check 76 = true := by decide +kernel
private theorem checked077 : check 77 = true := by decide +kernel
private theorem checked078 : check 78 = true := by decide +kernel
private theorem checked079 : check 79 = true := by decide +kernel
private theorem checked080 : check 80 = true := by decide +kernel
private theorem checked081 : check 81 = true := by decide +kernel
private theorem checked082 : check 82 = true := by decide +kernel
private theorem checked083 : check 83 = true := by decide +kernel
private theorem checked084 : check 84 = true := by decide +kernel
private theorem checked085 : check 85 = true := by decide +kernel
private theorem checked086 : check 86 = true := by decide +kernel
private theorem checked087 : check 87 = true := by decide +kernel
private theorem checked088 : check 88 = true := by decide +kernel
private theorem checked089 : check 89 = true := by decide +kernel
private theorem checked090 : check 90 = true := by decide +kernel
private theorem checked091 : check 91 = true := by decide +kernel
private theorem checked092 : check 92 = true := by decide +kernel
private theorem checked093 : check 93 = true := by decide +kernel
private theorem checked094 : check 94 = true := by decide +kernel
private theorem checked095 : check 95 = true := by decide +kernel
private theorem checked096 : check 96 = true := by decide +kernel
private theorem checked097 : check 97 = true := by decide +kernel
private theorem checked098 : check 98 = true := by decide +kernel
private theorem checked099 : check 99 = true := by decide +kernel
private theorem checked100 : check 100 = true := by decide +kernel
private theorem checked101 : check 101 = true := by decide +kernel
private theorem checked102 : check 102 = true := by decide +kernel
private theorem checked103 : check 103 = true := by decide +kernel
private theorem checked104 : check 104 = true := by decide +kernel
private theorem checked105 : check 105 = true := by decide +kernel
private theorem checked106 : check 106 = true := by decide +kernel
private theorem checked107 : check 107 = true := by decide +kernel
private theorem checked108 : check 108 = true := by decide +kernel
private theorem checked109 : check 109 = true := by decide +kernel
private theorem checked110 : check 110 = true := by decide +kernel
private theorem checked111 : check 111 = true := by decide +kernel
private theorem checked112 : check 112 = true := by decide +kernel
private theorem checked113 : check 113 = true := by decide +kernel
private theorem checked114 : check 114 = true := by decide +kernel
private theorem checked115 : check 115 = true := by decide +kernel
private theorem checked116 : check 116 = true := by decide +kernel
private theorem checked117 : check 117 = true := by decide +kernel
private theorem checked118 : check 118 = true := by decide +kernel
private theorem checked119 : check 119 = true := by decide +kernel
private theorem checked120 : check 120 = true := by decide +kernel
private theorem checked121 : check 121 = true := by decide +kernel
private theorem checked122 : check 122 = true := by decide +kernel
private theorem checked123 : check 123 = true := by decide +kernel
private theorem checked124 : check 124 = true := by decide +kernel
private theorem checked125 : check 125 = true := by decide +kernel
private theorem checked126 : check 126 = true := by decide +kernel
private theorem checked127 : check 127 = true := by decide +kernel
private theorem checked128 : check 128 = true := by decide +kernel
private theorem checked129 : check 129 = true := by decide +kernel
private theorem checked130 : check 130 = true := by decide +kernel
private theorem checked131 : check 131 = true := by decide +kernel
private theorem checked132 : check 132 = true := by decide +kernel
private theorem checked133 : check 133 = true := by decide +kernel
private theorem checked134 : check 134 = true := by decide +kernel
private theorem checked135 : check 135 = true := by decide +kernel
private theorem checked136 : check 136 = true := by decide +kernel
private theorem checked137 : check 137 = true := by decide +kernel
private theorem checked138 : check 138 = true := by decide +kernel
private theorem checked139 : check 139 = true := by decide +kernel
private theorem checked140 : check 140 = true := by decide +kernel
private theorem checked141 : check 141 = true := by decide +kernel
private theorem checked142 : check 142 = true := by decide +kernel
private theorem checked143 : check 143 = true := by decide +kernel
private theorem checked144 : check 144 = true := by decide +kernel
private theorem checked145 : check 145 = true := by decide +kernel
private theorem checked146 : check 146 = true := by decide +kernel
private theorem checked147 : check 147 = true := by decide +kernel
private theorem checked148 : check 148 = true := by decide +kernel
private theorem checked149 : check 149 = true := by decide +kernel
private theorem checked150 : check 150 = true := by decide +kernel

private theorem checkedRange0 (n : Fin 50) : check (n.val + 0) = true := by
  fin_cases n
  · exact checked000
  · exact checked001
  · exact checked002
  · exact checked003
  · exact checked004
  · exact checked005
  · exact checked006
  · exact checked007
  · exact checked008
  · exact checked009
  · exact checked010
  · exact checked011
  · exact checked012
  · exact checked013
  · exact checked014
  · exact checked015
  · exact checked016
  · exact checked017
  · exact checked018
  · exact checked019
  · exact checked020
  · exact checked021
  · exact checked022
  · exact checked023
  · exact checked024
  · exact checked025
  · exact checked026
  · exact checked027
  · exact checked028
  · exact checked029
  · exact checked030
  · exact checked031
  · exact checked032
  · exact checked033
  · exact checked034
  · exact checked035
  · exact checked036
  · exact checked037
  · exact checked038
  · exact checked039
  · exact checked040
  · exact checked041
  · exact checked042
  · exact checked043
  · exact checked044
  · exact checked045
  · exact checked046
  · exact checked047
  · exact checked048
  · exact checked049

private theorem checkedRange50 (n : Fin 50) : check (n.val + 50) = true := by
  fin_cases n
  · exact checked050
  · exact checked051
  · exact checked052
  · exact checked053
  · exact checked054
  · exact checked055
  · exact checked056
  · exact checked057
  · exact checked058
  · exact checked059
  · exact checked060
  · exact checked061
  · exact checked062
  · exact checked063
  · exact checked064
  · exact checked065
  · exact checked066
  · exact checked067
  · exact checked068
  · exact checked069
  · exact checked070
  · exact checked071
  · exact checked072
  · exact checked073
  · exact checked074
  · exact checked075
  · exact checked076
  · exact checked077
  · exact checked078
  · exact checked079
  · exact checked080
  · exact checked081
  · exact checked082
  · exact checked083
  · exact checked084
  · exact checked085
  · exact checked086
  · exact checked087
  · exact checked088
  · exact checked089
  · exact checked090
  · exact checked091
  · exact checked092
  · exact checked093
  · exact checked094
  · exact checked095
  · exact checked096
  · exact checked097
  · exact checked098
  · exact checked099

private theorem checkedRange100 (n : Fin 50) : check (n.val + 100) = true := by
  fin_cases n
  · exact checked100
  · exact checked101
  · exact checked102
  · exact checked103
  · exact checked104
  · exact checked105
  · exact checked106
  · exact checked107
  · exact checked108
  · exact checked109
  · exact checked110
  · exact checked111
  · exact checked112
  · exact checked113
  · exact checked114
  · exact checked115
  · exact checked116
  · exact checked117
  · exact checked118
  · exact checked119
  · exact checked120
  · exact checked121
  · exact checked122
  · exact checked123
  · exact checked124
  · exact checked125
  · exact checked126
  · exact checked127
  · exact checked128
  · exact checked129
  · exact checked130
  · exact checked131
  · exact checked132
  · exact checked133
  · exact checked134
  · exact checked135
  · exact checked136
  · exact checked137
  · exact checked138
  · exact checked139
  · exact checked140
  · exact checked141
  · exact checked142
  · exact checked143
  · exact checked144
  · exact checked145
  · exact checked146
  · exact checked147
  · exact checked148
  · exact checked149

private theorem checkedRange150 (n : Fin 1) : check (n.val + 150) = true := by
  fin_cases n
  · exact checked150

private theorem checked (n : Fin (150 + 1)) : check n = true := by
  have hv := n.isLt
  by_cases h0 : n.val < 50
  · exact checkedRange0 ⟨n.val, h0⟩
  · by_cases h1 : n.val < 100
    · have heq : n.val - 50 + 50 = n.val := by lia
      simpa only [heq] using checkedRange50 ⟨n.val - 50, by lia⟩
    · by_cases h2 : n.val < 150
      · have heq : n.val - 100 + 100 = n.val := by lia
        simpa only [heq] using checkedRange100 ⟨n.val - 100, by lia⟩
      · have heq : n.val - 150 + 150 = n.val := by lia
        simpa only [heq] using checkedRange150 ⟨n.val - 150, by lia⟩

private theorem row_checked {n : ℕ} (hn : n ≤ 150) :
    checkRow n (centers.getD n #[]) = true :=
  (Bool.and_eq_true_iff.mp (checked ⟨n, by lia⟩)).1

/-- Every row through 150 splits with simple negative roots and has its exact degree. -/
theorem polynomial_roots {n : ℕ} (hn : n ≤ 150) :
    (polynomial n).Splits ∧ HasSimpleRoots (polynomial n) ∧
      (polynomial n).natDegree = rowDegree n ∧ ∀ x ∈ (polynomial n).roots, x < 0 :=
  polynomial_roots_of_checkRow (row_checked hn)

/-- Every consecutive pair before 150 strictly interlaces in the standard orientation,
with no common roots and with the new rightmost root strictly farther right. -/
theorem polynomial_strictInterl {n : ℕ} (hn : n < 150) :
    StrictInterl (polynomial n) (polynomial (n + 1)) ∧
      (∀ x, ¬ ((polynomial n).IsRoot x ∧ (polynomial (n + 1)).IsRoot x)) ∧
      (rowDegree n ≠ 0 → ∃ y ∈ (polynomial (n + 1)).roots,
        (∀ x ∈ (polynomial n).roots, x < y) ∧
        ∀ z ∈ (polynomial (n + 1)).roots, z ≤ y) := by
  have hp := (Bool.and_eq_true_iff.mp (checked ⟨n, by lia⟩)).2
  rw [ite_eq_left hn] at hp
  exact strictInterl_of_checkPair (row_checked hn.le) (row_checked (by lia)) hp

end RealRooted.CatalanWordPeaks.Finite
