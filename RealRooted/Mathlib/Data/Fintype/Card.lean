import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

/-!
# Finite cardinality from unique hits under equivalences

This file provides a reusable counting principle for a finite family of
equivalences: if every point has a unique parameter whose image satisfies a
predicate, then the ambient cardinality is the parameter cardinality times the
cardinality of the predicate subtype.
-/

namespace Fintype

/-- A finite family of equivalences with a unique predicate-hitting parameter
partitions the ambient finite type into equally sized predicate fibers. -/
theorem card_eq_card_mul_card_subtype_of_existsUnique_equiv
    (X C : Type*) [Fintype X] [Fintype C] (act : C → X ≃ X)
    (P : X → Prop) [DecidablePred P]
    (h : ∀ x : X, ∃! c : C, P (act c x)) :
    Fintype.card X = Fintype.card C * Fintype.card {x : X // P x} := by
  classical
  let A := Σ x : X, {c : C // P (act c x)}
  let eAX : A ≃ X := by
    let eFiber : ∀ x : X, {c : C // P (act c x)} ≃ Unit := fun x =>
      { toFun := fun _ => Unit.unit
        invFun := fun _ => ⟨Classical.choose (h x),
          (Classical.choose_spec (h x)).1⟩
        left_inv := by
          intro z
          apply Subtype.ext
          exact (h x).unique (Classical.choose_spec (h x)).1 z.prop
        right_inv := by
          intro z
          exact Unit.ext _ _ }
    exact (Equiv.sigmaEquivProdOfEquiv eFiber).trans
      { toFun := Prod.fst
        invFun := fun x => (x, Unit.unit)
        left_inv := by
          rintro ⟨x, u⟩
          cases u
          rfl
        right_inv := fun _ => rfl }
  let eSwap : A ≃ Σ c : C, {x : X // P (act c x)} :=
    { toFun := fun z => ⟨z.2.val, z.1, z.2.prop⟩
      invFun := fun z => ⟨z.2.val, z.1, z.2.prop⟩
      left_inv := by
        rintro ⟨x, c, hc⟩
        rfl
      right_inv := by
        rintro ⟨c, x, hx⟩
        rfl }
  let eAB : A ≃ C × {x : X // P x} :=
    eSwap.trans <| (Equiv.sigmaCongrRight fun c =>
      (act c).subtypeEquivOfSubtype) |>.trans
        (Equiv.sigmaEquivProd C {x : X // P x})
  calc
    Fintype.card X = Fintype.card A := (Fintype.card_congr eAX).symm
    _ = Fintype.card (C × {x : X // P x}) := Fintype.card_congr eAB
    _ = Fintype.card C * Fintype.card {x : X // P x} := by simp

end Fintype
