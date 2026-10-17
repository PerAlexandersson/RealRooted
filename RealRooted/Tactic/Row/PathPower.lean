import RealRooted.Applications.OEIS.PathPowerRows
import RealRooted.Applications.OEIS.CubicParentRows
import RealRooted.EulerOperator.Polar
import RealRooted.Tactic.Row.Support
import RealRooted.CombinatorialExamples.PathPowerGap

/-!
# Bounded path-power route for row tactics

This module recognizes direct, reflected, shifted, and padded path-power
subsequences by an exact search over `2 ≤ k ≤ 5`, `1 ≤ p ≤ k`, and
`0 ≤ c ≤ p`.  The recurrence certificate is computed from the
characteristic polynomial of the powered companion matrix.
-/

open Lean Elab Tactic Meta Polynomial Finset

noncomputable section

namespace RealRooted.Tactic

private def intPolynomialToReal : ℤ[X] →+* ℝ[X] :=
  Polynomial.mapRingHom (Int.castRingHom ℝ)

private theorem companion_map_intPolynomialToReal (k : ℕ) :
    (RealRooted.PathPowerGap.companion k (X : ℤ[X])).map intPolynomialToReal =
      RealRooted.PathPowerGap.companion k (X : ℝ[X]) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, RealRooted.PathPowerGap.companion]
  split_ifs <;> simp [intPolynomialToReal]

private def evaluatedRecurrence (k p : ℕ) : LinearRecurrence ℝ[X] :=
  ⟨k, fun i ↦ intPolynomialToReal
    ((RealRooted.PathPowerGap.coefficientList k p).getD i 0)⟩

private theorem ofMatrix_companion_eq_evaluatedRecurrence (k p : ℕ) :
    LinearRecurrence.ofMatrix
      (RealRooted.PathPowerGap.companion k (X : ℝ[X]) ^ p) =
        evaluatedRecurrence k p := by
  unfold LinearRecurrence.ofMatrix evaluatedRecurrence
  congr 1
  funext i
  rw [← companion_map_intPolynomialToReal k]
  rw [← Matrix.map_pow, Matrix.charpoly_map, coeff_map, ← map_neg]
  apply congrArg intPolynomialToReal
  rw [RealRooted.PathPowerGap.coefficientList]
  have hi : (i : ℕ) <
      (List.map
        (fun j ↦ -(RealRooted.PathPowerGap.companion k (X : ℤ[X]) ^ p).charpoly.coeff j)
        (List.range k)).length := by
    simp only [List.length_map, List.length_range]
    exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp

private abbrev reflectedRecurrence (E : LinearRecurrence ℝ[X]) : LinearRecurrence ℝ[X] :=
  ⟨E.order, fun i ↦ reflect (E.order - i) (E.coeffs i)⟩

private theorem reflectedRecurrence_isSolution {E : LinearRecurrence ℝ[X]}
    {u : ℕ → ℝ[X]} (hu : E.IsSolution u) (D : ℕ)
    (hcoeff : ∀ i, (E.coeffs i).natDegree ≤ E.order - i)
    (hdegree : ∀ n, (u n).natDegree ≤ D + n) :
    (reflectedRecurrence E).IsSolution fun n ↦ reflect (D + n) (u n) := by
  intro n
  change reflect (D + (n + E.order)) (u (n + E.order)) =
    ∑ i : Fin E.order,
      reflect (E.order - i) (E.coeffs i) * reflect (D + (n + i)) (u (n + i))
  rw [hu n]
  induction (Finset.univ : Finset (Fin E.order)) using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, reflect_add, ih]
      have hindex : D + (n + E.order) = (E.order - i) + (D + (n + i)) := by
        have := i.isLt
        lia
      rw [hindex, reflect_mul _ _ (hcoeff i) (hdegree (n + i))]

private def prepend (a : ℝ[X]) (u : ℕ → ℝ[X]) : ℕ → ℝ[X]
  | 0 => a
  | n + 1 => u n

private abbrev prependedRecurrence (E : LinearRecurrence ℝ[X]) : LinearRecurrence ℝ[X] :=
  ⟨E.order + 1, fun i ↦ Fin.cases 0 E.coeffs i⟩

private theorem prependedRecurrence_isSolution {E : LinearRecurrence ℝ[X]}
    {u : ℕ → ℝ[X]} (hu : E.IsSolution u) (a : ℝ[X]) :
    (prependedRecurrence E).IsSolution (prepend a u) := by
  intro n
  change prepend a u (n + (E.order + 1)) =
    ∑ i : Fin (E.order + 1), Fin.cases 0 E.coeffs i * prepend a u (n + i)
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, zero_mul, zero_add, Fin.cases_succ]
  change u (n + E.order) = ∑ i, E.coeffs i * u (n + i)
  exact hu n

private theorem reflect_X_pow_mul_natCast (D n m : ℕ) :
    reflect D (X ^ n * (m : ℝ[X])) = C (m : ℝ) * X ^ Polynomial.revAt D n := by
  rw [mul_comm]
  rw [show (m : ℝ[X]) = C (m : ℝ) by norm_num, reflect_C_mul_X_pow]

private theorem reflect_X_mul_natCast (D m : ℕ) :
    reflect D (X * (m : ℝ[X])) = C (m : ℝ) * X ^ Polynomial.revAt D 1 := by
  simpa only [pow_one] using reflect_X_pow_mul_natCast D 1 m

private theorem reflect_X_pow_mul_C (D n : ℕ) (a : ℝ) :
    reflect D (X ^ n * C a) = C a * X ^ Polynomial.revAt D n := by
  rw [mul_comm, Polynomial.reflect_C_mul_X_pow]

private theorem reflect_X_mul_C (D : ℕ) (a : ℝ) :
    reflect D (X * C a) = C a * X ^ Polynomial.revAt D 1 := by
  simpa only [pow_one] using reflect_X_pow_mul_C D 1 a

private theorem C_natCast_eq (m : ℕ) : C (m : ℝ) = (m : ℝ[X]) := by
  norm_num

private theorem reflect_eq_of_coeff_eq {f g : ℝ[X]} (D : ℕ)
    (hcoeff : ∀ n ≤ D, f.coeff (D - n) = g.coeff n)
    (hf : f.natDegree ≤ D) (hg : g.natDegree ≤ D) : reflect D f = g := by
  ext n
  by_cases hn : n ≤ D
  · rw [Polynomial.coeff_reflect, Polynomial.revAt_le hn, hcoeff n hn]
  · have hn' : D < n := Nat.lt_of_not_ge hn
    rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hn']
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hn')]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg hn')]

private inductive PathPowerKind where
  | direct
  | reflected
  | shifted
  | padded
  | cubicEven
  | cubicEvenReflect
  | cubicOddReflect
  deriving BEq

private structure PathPowerFit where
  k : Nat
  p : Nat
  c : Nat
  model : Name
  order : Nat
  kind : PathPowerKind
  coeffs : Array QPoly := #[]

private def qPathPower (k N : Nat) : QPoly :=
  QPoly.norm <| (Array.range (N + 1)).map fun i =>
    (((N - (k - 1) * i).choose i : Nat) : Rat)

private def qReflect (D : Nat) (q : QPoly) : QPoly :=
  QPoly.norm <| (Array.range (D + 1)).map fun i => q.coeff (D - i)

private def qCubicEven : Nat → QPoly
  | 0 => QPoly.const 1
  | 1 => QPoly.norm #[1, 1]
  | 2 => QPoly.norm #[1, 5, 1]
  | n + 3 =>
      QPoly.norm #[1, 2] * qCubicEven (n + 2) +
        QPoly.norm #[0, 2, -1] * qCubicEven (n + 1) +
          QPoly.norm #[0, 0, 1] * qCubicEven n

private def qCubicEvenReflect : Nat → QPoly
  | 0 => QPoly.const 1
  | 1 => QPoly.norm #[1, 1]
  | 2 => QPoly.norm #[1, 5, 1]
  | n + 3 =>
      QPoly.norm #[2, 1] * qCubicEvenReflect (n + 2) +
        QPoly.norm #[-1, 2] * qCubicEvenReflect (n + 1) +
          QPoly.X * qCubicEvenReflect n

private def qCubicOddReflect : Nat → QPoly
  | 0 => QPoly.const 1
  | 1 => QPoly.norm #[3, 1]
  | 2 => QPoly.norm #[5, 7, 1]
  | n + 3 =>
      QPoly.norm #[2, 1] * qCubicOddReflect (n + 2) +
        QPoly.norm #[-1, 2] * qCubicOddReflect (n + 1) +
          QPoly.X * qCubicOddReflect n

private def PathPowerFit.row (fit : PathPowerFit) (n : Nat) : QPoly :=
  match fit.kind with
  | .direct => qPathPower fit.k (fit.p * n + fit.c)
  | .reflected =>
      let D₀ := (qPathPower fit.k fit.c).natDegree
      qReflect (D₀ + n) (qPathPower fit.k (fit.p * n + fit.c))
  | .shifted =>
      if n = 0 then QPoly.const 1
      else qReflect n (qPathPower fit.k (fit.p * (n - 1) + fit.c))
  | .padded => qReflect (n + 1) (qPathPower fit.k (fit.p * n + fit.c))
  | .cubicEven => qCubicEven n
  | .cubicEvenReflect => qCubicEvenReflect n
  | .cubicOddReflect => qCubicOddReflect n

private def legacyPathPowerCandidates : Array PathPowerFit := #[
  ⟨3, 3, 0, .anonymous, 3, .direct, #[]⟩,
  ⟨3, 3, 0, ``RealRooted.PathPowerRows.a109955, 3, .reflected, #[]⟩,
  ⟨3, 3, 2, ``RealRooted.PathPowerRows.a127893, 3, .reflected, #[]⟩,
  ⟨3, 3, 2, ``RealRooted.PathPowerRows.a206294, 4, .shifted, #[]⟩,
  ⟨4, 4, 0, ``RealRooted.PathPowerRows.a109960, 4, .reflected, #[]⟩,
  ⟨3, 2, 0, ``RealRooted.PathPowerRows.a116088, 3, .reflected, #[]⟩,
  ⟨4, 3, 0, ``RealRooted.PathPowerRows.a116089, 4, .reflected, #[]⟩,
  ⟨3, 1, 0, ``RealRooted.PathPowerRows.a277627, 3, .padded, #[]⟩,
  ⟨0, 0, 0, ``RealRooted.CubicParentRows.a184883, 3, .cubicEven, #[]⟩,
  ⟨0, 0, 0, ``RealRooted.CubicParentRows.a114123, 3, .cubicEvenReflect, #[]⟩,
  ⟨0, 0, 0, ``RealRooted.CubicParentRows.a216182, 3, .cubicOddReflect, #[]⟩]

private def legacyPathPowerFit? (P : Name) : MetaM (Option PathPowerFit) := do
  let some L ← linRec? P | return none
  unless (L.offset == 3 || L.offset == 4) && L.terms.all fun (_, i, _) => i == 0 do
    return none
  let some rows ← linRecRows? L 8 | return none
  for fit in legacyPathPowerCandidates do
    if L.offset == fit.order && (List.range 9).all fun n => rows[n]!.eqv (fit.row n) then
      return some fit
  return none

private abbrev QMatrix := Array (Array QPoly)

private def qMatrixMul (A B : QMatrix) : QMatrix := Id.run do
  let k := A.size
  let mut C := Array.replicate k (Array.replicate k (QPoly.const 0))
  for i in [0:k] do
    for j in [0:k] do
      let mut x := QPoly.const 0
      for l in [0:k] do
        x := x + (A[i]!)[l]! * (B[l]!)[j]!
      C := C.set! i (C[i]!.set! j x)
  return C

private def qMatrixPow (A : QMatrix) (p : Nat) : QMatrix := Id.run do
  let k := A.size
  let mut result := (Array.range k).map fun i =>
    (Array.range k).map fun j => QPoly.const (if i = j then 1 else 0)
  for _ in [0:p] do
    result := qMatrixMul result A
  return result

private def qCompanion (k : Nat) : QMatrix :=
  (Array.range k).map fun i => (Array.range k).map fun j =>
    if i + 1 < k then
      if j = i + 1 then QPoly.const 1 else QPoly.const 0
    else
      (if j = 0 then QPoly.X else QPoly.const 0) +
        if j + 1 = k then QPoly.const 1 else QPoly.const 0

private def qTrace (A : QMatrix) : QPoly := Id.run do
  let mut x := QPoly.const 0
  for i in [0:A.size] do
    x := x + (A[i]!)[i]!
  return x

/-- Exact powered-companion recurrence coefficients, in increasing shift order. -/
private def poweredCompanionCoeffs (k p : Nat) : Array QPoly := Id.run do
  let M := qMatrixPow (qCompanion k) p
  let mut power := M
  let mut traces := #[]
  for _ in [1:k + 1] do
    traces := traces.push (qTrace power)
    power := qMatrixMul power M
  let mut charCoeffs := #[QPoly.const 1]
  for m in [1:k + 1] do
    let mut x := QPoly.const 0
    for i in [1:m + 1] do
      x := x + charCoeffs[m - i]! * traces[i - 1]!
    charCoeffs := charCoeffs.push (QPoly.smul (-(1 / (m : Rat))) x)
  return (Array.range k).map fun i => -charCoeffs[k - i]!

private initialize poweredCompanionCache :
    IO.Ref (Array (Nat × Nat × Array QPoly)) ← IO.mkRef #[]

private def cachedPoweredCompanionCoeffs (k p : Nat) : MetaM (Array QPoly) := do
  let cache ← poweredCompanionCache.get
  for (k', p', coeffs) in cache do
    if k == k' && p == p' then return coeffs
  let coeffs := poweredCompanionCoeffs k p
  poweredCompanionCache.set (cache.push (k, p, coeffs))
  return coeffs

private def modelCoeffs (kind : PathPowerKind) (raw : Array QPoly) : Array QPoly :=
  match kind with
  | .direct => raw
  | .reflected | .padded =>
      (Array.range raw.size).map fun i => qReflect (raw.size - i) raw[i]!
  | .shifted =>
      #[QPoly.const 0] ++
        (Array.range raw.size).map fun i => qReflect (raw.size - i) raw[i]!
  | _ => #[]

private def recurrenceMatches (L : LinRecData) (coeffs : Array QPoly) : MetaM Bool := do
  if L.offset != coeffs.size || L.terms.any fun (_, i, _) => i != 0 then return false
  for j in [0:coeffs.size] do
    let some a₀ ← L.coeffAt? j 0 0 | return false
    let some a₁ ← L.coeffAt? j 0 1 | return false
    unless a₀.eqv coeffs[j]! && a₁.eqv coeffs[j]! do return false
  return true

private def genericPathPowerFit? (P : Name) : MetaM (Option PathPowerFit) := do
  let some L ← linRec? P | return none
  let some rows ← linRecRows? L 8 | return none
  let kinds := #[PathPowerKind.direct, .reflected, .shifted, .padded]
  for k in [2:6] do
    unless L.offset == k || L.offset == k + 1 do continue
    for p in [1:k + 1] do
      if k == 5 && p == 5 then continue
      let raw ← cachedPoweredCompanionCoeffs k p
      for c in [0:p + 1] do
        for kind in kinds do
          let coeffs := modelCoeffs kind raw
          let fit : PathPowerFit := ⟨k, p, c, .anonymous, coeffs.size, kind, coeffs⟩
          if (← recurrenceMatches L coeffs) &&
              (List.range 9).all (fun n => rows[n]!.eqv (fit.row n)) then
            return some fit
  return none

private def qpolyIntTerm (p : QPoly) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:p.coeffs.size] do
    let c := p.coeff i
    unless c.den == 1 do throwError "rr_row: nonintegral powered-companion coefficient"
    if c == 0 then continue
    let a := rowNumLit c.num.natAbs
    let mono ← match i with
      | 0 => `(($a : ℤ[X]))
      | 1 =>
          if c.num.natAbs == 1 then `(X)
          else `(($a : ℤ[X]) * X)
      | _ =>
          if c.num.natAbs == 1 then `(X ^ $(rowNumLit i))
          else `(($a : ℤ[X]) * X ^ $(rowNumLit i))
    acc := some <| ← match acc, decide (c < 0) with
      | none, false => pure mono
      | none, true => `(-$mono)
      | some a, false => `($a + $mono)
      | some a, true => `($a - $mono)
  match acc with
  | some t => `(($t : ℤ[X]))
  | none => `((0 : ℤ[X]))

private def qpolyRealTerm (p : QPoly) : TacticM Term := do
  let mut acc : Option Term := none
  for i in [0:p.coeffs.size] do
    let c := p.coeff i
    unless c.den == 1 do throwError "rr_row: nonintegral real-polynomial coefficient"
    if c == 0 then continue
    let a := rowNumLit c.num.natAbs
    let mono ← match i with
      | 0 => `(C ($a : ℝ))
      | 1 =>
          if c.num.natAbs == 1 then `(X)
          else `(C ($a : ℝ) * X)
      | _ =>
          if c.num.natAbs == 1 then `(X ^ $(rowNumLit i))
          else `(C ($a : ℝ) * X ^ $(rowNumLit i))
    acc := some <| ← match acc, decide (c < 0) with
      | none, false => pure mono
      | none, true => `(-$mono)
      | some a, false => `($a + $mono)
      | some a, true => `($a - $mono)
  match acc with
  | some t => `(($t : ℝ[X]))
  | none => `((0 : ℝ[X]))

private def pathModelTerm (fit : PathPowerFit) : TacticM Term := do
  let k := rowNumLit fit.k
  let p := rowNumLit fit.p
  let c := rowNumLit fit.c
  let D₀ := rowNumLit (qPathPower fit.k fit.c).natDegree
  match fit.kind with
  | .direct => `(fun n : ℕ => RealRooted.pathPowerCliquePolynomial $k ($p * n + $c))
  | .reflected =>
      `(fun n : ℕ => RealRooted.reciprocalShift ($D₀ + n)
        (RealRooted.pathPowerCliquePolynomial $k ($p * n + $c)))
  | .padded =>
      `(fun n : ℕ => RealRooted.reciprocalShift (n + 1)
        (RealRooted.pathPowerCliquePolynomial $k ($p * n + $c)))
  | .shifted =>
      `(prepend 1 (fun n : ℕ => RealRooted.reciprocalShift (n + 1)
        (RealRooted.pathPowerCliquePolynomial $k ($p * n + $c))))
  | _ => throwError "rr_row: cubic models do not have a path-power term"

private def recurrenceTerm (fit : PathPowerFit) : TacticM Term := do
  let coeffs ← fit.coeffs.mapM qpolyRealTerm
  `(LinearRecurrence.mk $(rowNumLit fit.order) ![$coeffs,*])

private def assertLegacyPathPowerLink (P : Name) (fit : PathPowerFit) : TacticM Ident := do
  let Pi := mkIdent P
  let link := mkIdent `hlink_pathPower
  if fit.kind matches .direct then
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n =
          RealRooted.pathPowerCliquePolynomial 3 (3 * n) := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | n
            · norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial]
            · norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial,
                Finset.sum_range_succ]
            · norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial,
                Finset.sum_range_succ] <;> ring
            · rw [$Pi:ident]
              rw [show RealRooted.pathPowerCliquePolynomial 3 (3 * (n + 3)) =
                  (1 + 3 * X) * RealRooted.pathPowerCliquePolynomial 3 (3 * (n + 2)) -
                    3 * X ^ 2 * RealRooted.pathPowerCliquePolynomial 3 (3 * (n + 1)) +
                      X ^ 3 * RealRooted.pathPowerCliquePolynomial 3 (3 * n) by
                exact RealRooted.pathPowerCliquePolynomial_three_trisection_add_three n]
              simp only [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)] <;>
                ring))
  else if fit.kind matches .cubicEven then
    let Q := mkIdent fit.model
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n = $Q n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | n
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident,
                RealRooted.CubicParent.polynomial_add_three] <;> ring
            · rw [$Pi:ident, RealRooted.CubicParentRows.a184883_add_three]
              simp only [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)] <;>
                ring))
  else if fit.order == 3 then
    let Q := mkIdent fit.model
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n = $Q n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | n
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · rw [$Pi:ident, $Q:ident]
              simp only [ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia),
                map_one, map_ofNat] <;> ring))
  else if fit.order == 4 then
    let Q := mkIdent fit.model
    evalTactic (← `(tactic|
      have $link:ident : ∀ n : ℕ, $Pi n = $Q n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            rcases n with _ | _ | _ | _ | n
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · norm_num [$Pi:ident, $Q:ident]
            · rw [$Pi:ident, $Q:ident]
              simp only [ih (n + 3) (by lia), ih (n + 2) (by lia),
                ih (n + 1) (by lia), ih n (by lia), map_one, map_ofNat] <;> ring))
  else
    throwError "rr_row: unsupported path-power recurrence order {fit.order}"
  return link

private def assertComputedPathPowerLink (P : Name) (fit : PathPowerFit) : TacticM Ident := do
  let Pi := mkIdent P
  let link := mkIdent `hlink_pathPower
  let hcoeff := mkIdent `hcoeff_pathPower
  let hraw := mkIdent `hraw_pathPower
  let hrec := mkIdent `hrecurrence_pathPower
  let hmodel := mkIdent `hmodel_pathPower
  let hP := mkIdent `hP_pathPower
  let k := rowNumLit fit.k
  let p := rowNumLit fit.p
  let c := rowNumLit fit.c
  let D₀ := rowNumLit (qPathPower fit.k fit.c).natDegree
  let rawCoeffs ← cachedPoweredCompanionCoeffs fit.k fit.p
  let coeffTerms ← rawCoeffs.mapM qpolyIntTerm
  let coeffList : Term ← `([$coeffTerms,*])
  let coeffEq : Term ←
    `(RealRooted.PathPowerGap.coefficientList $k $p = $coeffList)
  let model ← pathModelTerm fit
  let E ← recurrenceTerm fit
  let rawFit : PathPowerFit :=
    ⟨fit.k, fit.p, fit.c, .anonymous, fit.k, .direct, rawCoeffs⟩
  let rawE ← recurrenceTerm rawFit
  let rawProof : Term ←
    `(RealRooted.PathPowerGap.companion_pow_isSolution_subsequence
      (k := $k) (y := (X : ℝ[X]))
      (u := fun N ↦ RealRooted.pathPowerCliquePolynomial $k N) (by norm_num)
      (fun n ↦ RealRooted.pathPowerCliquePolynomial_add_lag $k n (by norm_num)) $p $c)
  if fit.k == 3 && fit.p == 2 then
    evalTactic (← `(tactic| have $hcoeff:ident : $coeffEq :=
      RealRooted.PathPowerGap.coefficientList_three_two))
  else if fit.k == 3 && fit.p == 3 then
    evalTactic (← `(tactic| have $hcoeff:ident : $coeffEq :=
      RealRooted.PathPowerGap.coefficientList_three_three))
  else if fit.k == 4 && fit.p == 3 then
    evalTactic (← `(tactic| have $hcoeff:ident : $coeffEq :=
      RealRooted.PathPowerGap.coefficientList_four_three))
  else if fit.k == 4 && fit.p == 4 then
    evalTactic (← `(tactic| have $hcoeff:ident : $coeffEq :=
      RealRooted.PathPowerGap.coefficientList_four_four))
  else
    evalTactic (← `(tactic| have $hcoeff:ident : $coeffEq := by
      norm_num [RealRooted.PathPowerGap.coefficientList,
        RealRooted.PathPowerGap.companion, pow_succ, Matrix.mul_apply,
        Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero,
        Fin.sum_univ_succ, Fin.succAbove, List.range, List.range.loop, List.map] <;>
        ring))
  evalTactic (← `(tactic|
    have hraw_evaluated : (evaluatedRecurrence $k $p).IsSolution
        (fun n : ℕ => RealRooted.pathPowerCliquePolynomial $k ($p * n + $c)) := by
      rw [← ofMatrix_companion_eq_evaluatedRecurrence]
      exact $rawProof))
  evalTactic (← `(tactic|
    have $hraw:ident : ($rawE).IsSolution
        (fun n : ℕ => RealRooted.pathPowerCliquePolynomial $k ($p * n + $c)) := by
      rw [← show evaluatedRecurrence $k $p = $rawE by
        unfold evaluatedRecurrence
        congr 1
        funext i
        fin_cases i <;>
          norm_num [$hcoeff:ident, List.getD, intPolynomialToReal,
            C_natCast_eq, map_ofNat] <;>
          first
          | (ring; done)
          | simp [Polynomial.coeff_monomial]]
      exact hraw_evaluated))
  unless fit.kind matches .direct do
    let transformed : Term ← if fit.kind matches .shifted then
        `(prependedRecurrence (reflectedRecurrence $rawE))
      else
        `(reflectedRecurrence $rawE)
    evalTactic (← `(tactic|
      have $hrec:ident : $E = $transformed := by
        congr 1
        funext i
        fin_cases i <;>
          first
          | rfl
          | (symm
             apply reflect_eq_of_coeff_eq
             · intro n hn
               have hn' : n < 6 := by lia
               interval_cases n <;>
                 norm_num at hn <;>
                 norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
                   Polynomial.coeff_neg, Polynomial.coeff_mul,
                   Polynomial.coeff_X_pow, Polynomial.coeff_X,
                   Polynomial.coeff_C, Polynomial.coeff_ofNat_succ,
                   Polynomial.coeff_one, C_natCast_eq, map_ofNat] <;>
                 first
                 | (ring; done)
                 | simp [Polynomial.coeff_monomial, Nat.choose]
             · compute_degree!
             · compute_degree!)))
  match fit.kind with
  | .direct =>
      evalTactic (← `(tactic| have $hmodel:ident : ($E).IsSolution $model := $hraw))
  | .shifted =>
      evalTactic (← `(tactic|
        have $hmodel:ident : ($E).IsSolution $model := by
          rw [$hrec:ident]
          apply prependedRecurrence_isSolution
          simpa only [RealRooted.reciprocalShift, Nat.add_comm] using
            reflectedRecurrence_isSolution $hraw 1 (by
              intro i
              fin_cases i <;> norm_num <;> compute_degree! <;>
                simp [Polynomial.coeff_monomial]) (by
              intro n
              have h := RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
                $k $p $c n (by norm_num) (by norm_num) (by norm_num)
              have hbase :
                  (RealRooted.pathPowerCliquePolynomial $k $c).natDegree ≤ 1 := by
                norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                  compute_degree!
              lia)))
  | .padded =>
      evalTactic (← `(tactic|
        have $hmodel:ident : ($E).IsSolution $model := by
          rw [$hrec:ident]
          simpa only [RealRooted.reciprocalShift, Nat.add_comm] using
            reflectedRecurrence_isSolution $hraw 1 (by
              intro i
              fin_cases i <;> norm_num <;> compute_degree! <;>
                simp [Polynomial.coeff_monomial]) (by
              intro n
              have h := RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
                $k $p $c n (by norm_num) (by norm_num) (by norm_num)
              have hbase :
                  (RealRooted.pathPowerCliquePolynomial $k $c).natDegree ≤ 1 := by
                norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                  compute_degree!
              lia)))
  | .reflected =>
      evalTactic (← `(tactic|
        have $hmodel:ident : ($E).IsSolution $model := by
          rw [$hrec:ident]
          simpa only [RealRooted.reciprocalShift] using
            reflectedRecurrence_isSolution $hraw $D₀ (by
              intro i
              fin_cases i <;> norm_num <;> compute_degree! <;>
                simp [Polynomial.coeff_monomial]) (by
              intro n
              have h := RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
                $k $p $c n (by norm_num) (by norm_num) (by norm_num)
              have hbase :
                  (RealRooted.pathPowerCliquePolynomial $k $c).natDegree = $D₀ := by
                norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                  compute_degree!
              simpa only [hbase] using h)))
  | _ => throwError "rr_row: unexpected cubic model in computed link"
  evalTactic (← `(tactic|
    have $hP:ident : ($E).IsSolution $Pi := by
      intro n
      simp only [$Pi:ident]
      norm_num [reflectedRecurrence, prependedRecurrence, Fin.sum_univ_succ,
        reflect_X_pow_mul_natCast, reflect_X_mul_natCast, reflect_add,
        reflect_neg, reflect_sub, reflect_monomial, reflect_one,
        reflect_X_pow_mul_C, reflect_X_mul_C,
        Polynomial.reflect_C_mul_X_pow, C_natCast_eq, map_ofNat] <;> ring))
  if fit.kind matches .direct then
    evalTactic (← `(tactic|
      have hinit_pathPower :
          ∀ i : Fin $(rowNumLit fit.order), $Pi i = $model i := by
        intro i
        fin_cases i <;>
          norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial,
            Finset.sum_range_succ] <;> ring))
  else
    evalTactic (← `(tactic|
      have hinit_pathPower :
          ∀ i : Fin $(rowNumLit fit.order), $Pi i = $model i := by
        intro i
        fin_cases i <;>
          norm_num [$Pi:ident, prepend, RealRooted.reciprocalShift] <;>
          first
          | rfl
          | (symm
             apply reflect_eq_of_coeff_eq
             · intro j hj
               have hj' : j < 7 := by lia
               interval_cases j <;>
                 norm_num [$Pi:ident, RealRooted.pathPowerCliquePolynomial,
                   Finset.sum_range_succ, Polynomial.coeff_add,
                   Polynomial.coeff_sub, Polynomial.coeff_neg,
                   Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_pow,
                   Polynomial.coeff_X, Polynomial.coeff_C,
                   Polynomial.coeff_one, Polynomial.coeff_ofNat_succ,
                   Polynomial.coeff_natCast_ite,
                   Polynomial.coeff_monomial] at hj ⊢ <;>
                 first
                 | (ring; done)
                 | norm_num [Nat.choose]
             · norm_num [RealRooted.pathPowerCliquePolynomial,
                 Finset.sum_range_succ] <;> compute_degree!
             · norm_num [$Pi:ident] <;> compute_degree!)))
  evalTactic (← `(tactic|
    have $link:ident : ∀ n : ℕ, $Pi n = $model n := by
      intro n
      have hp := ($E).eq_mk_of_is_sol_of_eq_init $hP (by
        intro i
        exact hinit_pathPower i) n
      have hm := ($E).eq_mk_of_is_sol_of_eq_init $hmodel (by
        intro i
        rfl) n
      exact hp.trans hm.symm))
  evalTactic (← `(tactic|
    clear $hcoeff:ident $hraw:ident $hmodel:ident $hP:ident))
  return link

private def splitsTheorem (model : Name) : Option Name :=
  if model == ``RealRooted.PathPowerRows.a109955 then
    some ``RealRooted.PathPowerRows.splits_a109955
  else if model == ``RealRooted.PathPowerRows.a127893 then
    some ``RealRooted.PathPowerRows.splits_a127893
  else if model == ``RealRooted.PathPowerRows.a206294 then
    some ``RealRooted.PathPowerRows.splits_a206294
  else if model == ``RealRooted.PathPowerRows.a109960 then
    some ``RealRooted.PathPowerRows.splits_a109960
  else if model == ``RealRooted.PathPowerRows.a116088 then
    some ``RealRooted.PathPowerRows.splits_a116088
  else if model == ``RealRooted.PathPowerRows.a116089 then
    some ``RealRooted.PathPowerRows.splits_a116089
  else if model == ``RealRooted.PathPowerRows.a277627 then
    some ``RealRooted.PathPowerRows.splits_a277627
  else if model == ``RealRooted.CubicParentRows.a184883 then
    some ``RealRooted.CubicParentRows.a184883_splits
  else if model == ``RealRooted.CubicParentRows.a114123 then
    some ``RealRooted.CubicParentRows.a114123_splits
  else if model == ``RealRooted.CubicParentRows.a216182 then
    some ``RealRooted.CubicParentRows.a216182_splits
  else none

private def interlacesTheorem (model : Name) : Option Name :=
  if model == ``RealRooted.PathPowerRows.a109955 then
    some ``RealRooted.PathPowerRows.strictInterl_a109955
  else if model == ``RealRooted.PathPowerRows.a127893 then
    some ``RealRooted.PathPowerRows.strictInterl_a127893
  else if model == ``RealRooted.PathPowerRows.a206294 then
    some ``RealRooted.PathPowerRows.strictInterl_a206294
  else if model == ``RealRooted.PathPowerRows.a109960 then
    some ``RealRooted.PathPowerRows.strictInterl_a109960
  else if model == ``RealRooted.PathPowerRows.a116088 then
    some ``RealRooted.PathPowerRows.strictInterl_a116088
  else if model == ``RealRooted.PathPowerRows.a116089 then
    some ``RealRooted.PathPowerRows.strictInterl_a116089
  else if model == ``RealRooted.PathPowerRows.a277627 then
    some ``RealRooted.PathPowerRows.strictInterl_a277627
  else none

private def applyLegacyPathPowerGoal (splits : Bool) (fit : PathPowerFit) (idxE : Expr)
    (hdegree link : Ident) : TacticM Unit := do
  let idx ← Term.exprToSyntax idxE
  let hleft : Term ← `($link:ident $idx)
  let hright : Term ← `($link:ident ($idx + 1))
  let rwleft : TSyntax `Lean.Parser.Tactic.rwRule ←
    `(Lean.Parser.Tactic.rwRule| $hleft:term)
  let rwright : TSyntax `Lean.Parser.Tactic.rwRule ←
    `(Lean.Parser.Tactic.rwRule| $hright:term)
  let oneRule : Array (TSyntax `Lean.Parser.Tactic.rwRule) := #[rwleft]
  let twoRules : Array (TSyntax `Lean.Parser.Tactic.rwRule) := #[rwleft, rwright]
  if fit.kind matches .direct then
    if splits then
      evalTactic (← `(tactic| (
        rw [$oneRule,*]
        apply RealRooted.splits_pathPowerCliquePolynomial)))
    else
      evalTactic (← `(tactic| (
        refine RealRooted.StrictInterl.toInterlaces ?_ (by
          rw [$hdegree:ident $idx, $hdegree:ident ($idx + 1)]
          lia)
        rw [$twoRules,*]
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
          RealRooted.strictInterl_pathPowerCliquePolynomial_add 3 (3 * $idx) 3
            (by norm_num) (by norm_num) (by norm_num))))
    return
  if splits then
    let some thm := splitsTheorem fit.model
      | throwError "rr_row: no splitting theorem for the fitted path-power model"
    evalTactic (← `(tactic| rw [$oneRule,*]))
    (← getMainGoal).assign (mkApp (mkConst thm) idxE)
    setGoals []
  else
    let some thm := interlacesTheorem fit.model
      | throwError "rr_row: no interlacing theorem for the fitted path-power model"
    evalTactic (← `(tactic|
      refine RealRooted.StrictInterl.toInterlaces ?_ (by
        rw [$hdegree:ident $idx, $hdegree:ident ($idx + 1)]
        lia)))
    evalTactic (← `(tactic| rw [$twoRules,*]))
    (← getMainGoal).assign (mkApp (mkConst thm) idxE)
    setGoals []

private def applyPathPowerGoal (splits : Bool) (fit : PathPowerFit) (idx : Expr)
    (hdegree link : Ident) : TacticM Unit := do
  let k := rowNumLit fit.k
  let p := rowNumLit fit.p
  let c := rowNumLit fit.c
  let D₀ := (qPathPower fit.k fit.c).natDegree
  let Dterm := rowNumLit D₀
  let idxStx ← Term.exprToSyntax idx
  let idxTarget : TSyntax `Lean.Parser.Tactic.elimTarget ←
    `(Lean.Parser.Tactic.elimTarget| $idxStx:term)
  let hleft : Term ← `($link:ident $idxStx)
  let hright : Term ← `($link:ident ($idxStx + 1))
  let rwleft : TSyntax `Lean.Parser.Tactic.rwRule ←
    `(Lean.Parser.Tactic.rwRule| $hleft:term)
  let rwright : TSyntax `Lean.Parser.Tactic.rwRule ←
    `(Lean.Parser.Tactic.rwRule| $hright:term)
  if splits then
    evalTactic (← `(tactic| rw [$rwleft]))
    match fit.kind with
    | .direct =>
        evalTactic (← `(tactic| exact RealRooted.splits_pathPowerCliquePolynomial _ _))
    | .reflected =>
        evalTactic (← `(tactic| have hbase :
            (RealRooted.pathPowerCliquePolynomial $k $c).natDegree = $Dterm := by
          norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
            compute_degree!))
        evalTactic (← `(tactic| simpa only [hbase] using
          RealRooted.splits_reciprocalShift_pathPowerCliquePolynomial
            $k $p $c $idxStx (by norm_num) (by norm_num) (by norm_num)))
    | .padded =>
        evalTactic (← `(tactic|
          exact RealRooted.reciprocalShift_splits
            (RealRooted.splits_pathPowerCliquePolynomial _ _) (by
            have h := RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
              $k $p $c $idxStx (by norm_num) (by norm_num) (by norm_num)
            have hbase :
                (RealRooted.pathPowerCliquePolynomial $k $c).natDegree ≤ 1 := by
              norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                compute_degree!
            lia)))
    | .shifted =>
        evalTactic (← `(tactic|
          cases $idxTarget with
          | zero => norm_num [prepend]
          | succ n =>
              exact RealRooted.reciprocalShift_splits
                (RealRooted.splits_pathPowerCliquePolynomial _ _) (by
                have h := RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
                  $k $p $c n (by norm_num) (by norm_num) (by norm_num)
                have hbase :
                    (RealRooted.pathPowerCliquePolynomial $k $c).natDegree ≤ 1 := by
                  norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                    compute_degree!
                lia)))
    | _ => throwError "rr_row: unexpected cubic model"
    return
  evalTactic (← `(tactic|
    refine RealRooted.StrictInterl.toInterlaces ?_ (by
      rw [$hdegree:ident $idxStx, $hdegree:ident ($idxStx + 1)]
      lia)))
  evalTactic (← `(tactic| rw [$rwleft, $rwright]))
  match fit.kind with
  | .direct =>
      evalTactic (← `(tactic|
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
          RealRooted.strictInterl_pathPowerCliquePolynomial_add
            $k ($p * $idxStx + $c) $p (by norm_num) (by norm_num) (by norm_num)))
  | .reflected =>
      evalTactic (← `(tactic| have hbase :
          (RealRooted.pathPowerCliquePolynomial $k $c).natDegree = $Dterm := by
        norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
          compute_degree!))
      evalTactic (← `(tactic| simpa only [hbase] using
        RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
          $k $p $c $idxStx (by norm_num) (by norm_num) (by norm_num)))
  | .padded =>
      if D₀ == 1 then
        evalTactic (← `(tactic| simpa only [Nat.add_comm] using
          RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
            $k $p $c $idxStx (by norm_num) (by norm_num) (by norm_num)))
      else
        let hinter : Term ←
          `(RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
            $k $p $c $idxStx (by norm_num) (by norm_num) (by norm_num))
        evalTactic (← `(tactic| have h := $hinter))
        evalTactic (← `(tactic| have hmul :=
          h.mul_common_factor Polynomial.X_ne_zero Polynomial.Splits.X))
        evalTactic (← `(tactic|
          rw [mul_comm Polynomial.X, mul_comm Polynomial.X] at hmul))
        evalTactic (← `(tactic| have hbase :
            (RealRooted.pathPowerCliquePolynomial $k $c).natDegree = 0 := by
          norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
            compute_degree!))
        evalTactic (← `(tactic| have hd₀ :=
          RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
            $k $p $c $idxStx (by norm_num) (by norm_num) (by norm_num)))
        evalTactic (← `(tactic| have hd₁ :=
          RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
            $k $p $c ($idxStx + 1) (by norm_num) (by norm_num) (by norm_num)))
        evalTactic (← `(tactic| have hd₀' :
            (RealRooted.pathPowerCliquePolynomial $k
              ($p * $idxStx + $c)).natDegree ≤ $idxStx := by
          simpa only [hbase, Nat.zero_add] using hd₀))
        evalTactic (← `(tactic| have hd₁' :
            (RealRooted.pathPowerCliquePolynomial $k
              ($p * ($idxStx + 1) + $c)).natDegree ≤ $idxStx + 1 := by
          simpa only [hbase, Nat.zero_add] using hd₁))
        evalTactic (← `(tactic|
          simpa only [hbase, RealRooted.reciprocalShift, Nat.zero_add, Nat.add_assoc,
            Polynomial.reflect_succ _ hd₀', Polynomial.reflect_succ _ hd₁']
            using hmul))
  | .shifted =>
      if D₀ == 1 then
        evalTactic (← `(tactic|
          cases $idxTarget with
          | zero =>
            norm_num [prepend, RealRooted.pathPowerCliquePolynomial,
              RealRooted.reciprocalShift, Finset.sum_range_succ]
            exact (RealRooted.interlaces_one_linear (by compute_degree!)).toStrictInterl
          | succ n =>
            simp only [prepend]
            have hbase :
                (RealRooted.pathPowerCliquePolynomial $k $c).natDegree = 1 := by
              norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                compute_degree!
            simpa only [hbase, Nat.one_add, Nat.add_assoc, Nat.add_comm] using
              RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
                $k $p $c n (by norm_num) (by norm_num) (by norm_num)))
      else
        evalTactic (← `(tactic|
          cases $idxTarget with
          | zero =>
            norm_num [prepend, RealRooted.pathPowerCliquePolynomial,
              RealRooted.reciprocalShift, Finset.sum_range_succ]
            exact (RealRooted.interlaces_one_linear (by compute_degree!)).toStrictInterl
          | succ n =>
            simp only [prepend]
            have hbase :
                (RealRooted.pathPowerCliquePolynomial $k $c).natDegree = 0 := by
              norm_num [RealRooted.pathPowerCliquePolynomial, Finset.sum_range_succ] <;>
                compute_degree!
            have h :=
              RealRooted.strictInterl_reciprocalShift_pathPowerCliquePolynomial
                $k $p $c n (by norm_num) (by norm_num) (by norm_num)
            have hmul := h.mul_common_factor Polynomial.X_ne_zero Polynomial.Splits.X
            rw [mul_comm Polynomial.X, mul_comm Polynomial.X] at hmul
            have hd₀ :=
              RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
                $k $p $c n (by norm_num) (by norm_num) (by norm_num)
            have hd₁ :=
              RealRooted.pathPowerCliquePolynomial_subsequence_natDegree_le
                $k $p $c (n + 1) (by norm_num) (by norm_num) (by norm_num)
            have hd₀' :
                (RealRooted.pathPowerCliquePolynomial $k ($p * n + $c)).natDegree ≤ n := by
              simpa only [hbase, Nat.zero_add] using hd₀
            have hd₁' :
                (RealRooted.pathPowerCliquePolynomial $k
                  ($p * (n + 1) + $c)).natDegree ≤ n + 1 := by
              simpa only [hbase, Nat.zero_add] using hd₁
            simpa only [hbase, RealRooted.reciprocalShift, Nat.zero_add, Nat.add_assoc,
              Polynomial.reflect_succ _ hd₀', Polynomial.reflect_succ _ hd₁']
              using hmul))
  | _ => throwError "rr_row: unexpected cubic model"

/-- Close a splitting or consecutive-interlacing row goal after the bounded exact probe. -/
def pathPowerGoal (splits : Bool) : TacticM Unit := do
  discard introIfForall
  withMainContext do
  let some P ← findPolySeqConst? (← instantiateMVars (← getMainTarget))
    | throwError "rr_row: no sequence"
  let hdegree := mkIdent `hdegree_pathPower
  if let some fit ← legacyPathPowerFit? P then
    unless splits do
      let Pi := mkIdent P
      let n := mkIdent `n
      let D₀ := (fit.row 0).natDegree
      evalTactic (← `(tactic|
        have $hdegree:ident : ∀ $n:ident : ℕ,
            ($Pi $n).natDegree = $(rowNumLit D₀) + $n := by
          intro $n:ident
          rr_row_natDegree))
    let link ← assertLegacyPathPowerLink P fit
    let idx ← mainRowIndex (mkIdent P)
    applyLegacyPathPowerGoal splits fit idx hdegree link
    return
  let some fit ← genericPathPowerFit? P
    | throwError "rr_row: the rows do not match a bounded path-power or cubic-parent model"
  unless splits do
    let Pi := mkIdent P
    let n := mkIdent `n
    let D₀ := (fit.row 0).natDegree
    evalTactic (← `(tactic|
      have $hdegree:ident : ∀ $n:ident : ℕ,
          ($Pi $n).natDegree = $(rowNumLit D₀) + $n := by
        intro $n:ident
        rr_row_natDegree))
  let link ← assertComputedPathPowerLink P fit
  let idx ← mainRowIndex (mkIdent P)
  applyPathPowerGoal splits fit idx hdegree link

/-- Run only the bounded path-power and cubic-parent splitting route. -/
elab "rr_row_path_power_splits" : tactic => pathPowerGoal true

/-- Run only the bounded path-power consecutive-interlacing route. -/
elab "rr_row_path_power_interlaces" : tactic => pathPowerGoal false

end RealRooted.Tactic
