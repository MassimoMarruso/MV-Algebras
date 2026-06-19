import MVAlgebras.Defs
import MVAlgebras.Indipendence
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Submonoid.Defs

@[ext]
class MVSubalgebra (A : Type*) [MVAlgebra A] where
  carrier : Set A
  oAdd_mem {x y : A} : x ∈ carrier → y ∈ carrier → (x ⊕ y) ∈ carrier
  zero_mem : 0 ∈ carrier
  not_mem {x : A} : x ∈ carrier → - x ∈ carrier
open MVSubalgebra

@[ext]
class MVSubalgebraClass (S : Type*) (A : outParam Type*) [MVAlgebra A] extends SetLike S A where
  oAdd_mem' {x y : A} {B : S} : x ∈ B → y ∈ B → (x ⊕ y) ∈ B
  zero_mem' (B : S) : 0 ∈ B
  not_mem' {x : A} {B : S} : x ∈ B → - x ∈ B
open MVSubalgebraClass

namespace Subalgebra

variable {A S : Type*} [MVAlgebra A] (B : MVSubalgebra A) [MVSubalgebraClass S A]

instance : SetLike (MVSubalgebra A) A where
  coe B := B.carrier
  coe_injective' := by
    intro B C h
    ext1
    apply h

instance : MVSubalgebraClass (MVSubalgebra A) A where
  oAdd_mem' := MVSubalgebra.oAdd_mem
  zero_mem' _ := MVSubalgebra.zero_mem
  not_mem' := MVSubalgebra.not_mem

@[simp]
lemma oAdd_mem {x y : A} {B : S} : x ∈ B → y ∈ B → (x ⊕ y) ∈ B := MVSubalgebraClass.oAdd_mem'

@[simp]
lemma zero_mem (B : S) : 0 ∈ B := MVSubalgebraClass.zero_mem' B

@[simp]
lemma not_mem {x : A} {B : S} : x ∈ B → - x ∈ B := MVSubalgebraClass.not_mem'

instance (B : MVSubalgebra A) : Reduced.MVAlgebra B where
  oAdd := fun (⟨x,hx⟩ : B) (⟨y,hy⟩ : B) => ⟨x ⊕ y,B.oAdd_mem hx hy⟩
  neg := fun (⟨x,hx⟩ : B) => ⟨- x, B.not_mem hx⟩
  zero := ⟨0,B.zero_mem⟩
  neg_neg := by intro _ ; ext1 ; apply neg_neg
  oAdd_assoc' := by intro _ _ _ ; ext1 ; apply oAdd_assoc
  oAdd_zero' := by intro _ ; ext1 ; apply oAdd_zero
  oAdd_not_zero' := by intro _ ; ext1 ; apply oAdd_not_zero
  not_switch' := by intro _ _ ; ext1 ; apply not_switch

instance (B : MVSubalgebra A) : AddSubmonoid A where
  carrier := B.carrier
  add_mem' := B.oAdd_mem
  zero_mem' := B.zero_mem

instance : AddSubmonoidClass S A where
  add_mem := oAdd_mem
  zero_mem := zero_mem

end Subalgebra
