import MVAlgebras.Defs
import MVAlgebras.MVAlgebraHom
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Group.Pi.Basic

variable {ι : Type*} {A : ι → Type*} [∀ (i : ι), MVAlgebra (A i)]

instance : MVAlgebra (∀ (i : ι), A i) where
  oAdd_not_zero := by
    intro f
    ext i
    rw[Pi.add_apply]
    rw[Pi.neg_apply]
    rw[Pi.zero_apply]
    apply oAdd_not_zero
  not_switch := by
    intro f g
    ext i
    rw[Pi.add_apply,Pi.add_apply]
    rw[Pi.neg_apply,Pi.neg_apply]
    rw[Pi.add_apply,Pi.add_apply]
    rw[Pi.neg_apply,Pi.neg_apply]
    apply not_switch

@[reducible]
def proj (j : ι) : MVAlgebraHom ((i : ι) → A i) (A j) where
  toFun f := f j
  map_zero' := by rfl
  map_add' _ _ := by rw[Pi.add_apply]
  map_not _ := by rw[Pi.neg_apply]

lemma bot_i_bot {x : (i : ι) → A i} :
  x ∈ (⊥ : MVAlgebra_Ideal (∀ (i : ι), A i))
  ↔ ∀ (i : ι), x i ∈ (⊥ : MVAlgebra_Ideal (A i)) := by
    apply Iff.intro
    case mp =>
      intro h i
      rw[MVIdeal.mem_bot_iff_zero]
      rw[MVIdeal.mem_bot_iff_zero] at h
      rw[h]
      rfl
    case mpr =>
      intro h
      rw[MVIdeal.mem_bot_iff_zero]
      ext i
      suffices this : x i = 0 from by
        apply this
      rw[←MVIdeal.mem_bot_iff_zero]
      apply h i
