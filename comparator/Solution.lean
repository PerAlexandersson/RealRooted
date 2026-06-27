import RealRooted

/-!
# Solution: bridge from Challenge to the RealRooted library
-/

open Polynomial

noncomputable section

namespace Comparator

open RealRooted Polynomial

def HasNonnegCoeffs (p : ℝ[X]) : Prop :=
  RealRooted.HasNonnegCoeffs p

def HasPosLeadingCoeff (p : ℝ[X]) : Prop :=
  RealRooted.HasPosLeadingCoeff p

def Prec (f g : ℝ[X]) : Prop :=
  RealRooted.Prec f g

def StrictPrecSameDegree (p q : ℝ[X]) : Prop :=
  RealRooted.StrictPrecSameDegree p q

def IdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  RealRooted.IdTransform d p

def RdTransform (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  RealRooted.RdTransform d p

def fPolynomial (d : ℕ) (h : ℝ[X]) : ℝ[X] :=
  RealRooted.fPolynomial d h

def IsIdDecomposition (d : ℕ) (p a b : ℝ[X]) : Prop :=
  RealRooted.IsIdDecomposition d p a b

def IsPolyaFreqSeq (a : ℕ → ℝ) : Prop :=
  RealRooted.IsPolyaFreqSeq a

def bezoutMatrix (n : ℕ) (p q : ℝ[X]) : Matrix (Fin n) (Fin n) ℝ :=
  RealRooted.bezoutMatrix n p q

theorem brandenSolusTheorem26 :
    ∀ {d : ℕ} {p a b : ℝ[X]},
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (Prec b a ↔ Prec a p) ∧
      (Prec a p ↔ Prec b p) ∧
      (Prec b p ↔ Prec (IdTransform d p) p) ∧
      (Prec (IdTransform d p) p ↔
        Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) :=
  RealRooted.brandenSolusTheorem26

theorem aissenSchoenbergWhitney_reverse {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p)
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsPolyaFreqSeq (fun n ↦ p.coeff n) :=
  RealRooted.aissenSchoenbergWhitney_reverse hpnn hsplits hroots

theorem strictPrecSameDegree_iff_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix n q p).PosDef :=
  RealRooted.strictPrecSameDegree_iff_bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg

end Comparator

end
