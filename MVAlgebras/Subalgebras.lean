import MVAlgebras.Defs
import MVAlgebras.Indipendence
import Mathlib.Data.SetLike.Basic
import Mathlib.Algebra.Group.Submonoid.Defs

@[ext]
class MVSubalgebra (A : Type*) [MVAlgebra A] extends AddSubmonoid A where
  not_mem {x : A} : x ∈ carrier → - x ∈ carrier
open MVSubalgebra

@[ext]
class MVSubalgebraClass (S : Type*) (A : outParam Type*) [MVAlgebra A] [SetLike S A]
  extends AddSubmonoidClass S A where
  not_mem' {x : A} {B : S} : x ∈ B → - x ∈ B
open MVSubalgebraClass

namespace Subalgebra

variable {A S : Type*} [MVAlgebra A] (B : MVSubalgebra A) [SetLike S A]
  [MVSubalgebraClass S A]

instance : SetLike (MVSubalgebra A) A where
  coe B := B.carrier
  coe_injective' := by
    intro B C h
    ext1
    apply h

instance : MVSubalgebraClass (MVSubalgebra A) A where
  add_mem := MVSubalgebra.toAddSubmonoid.add_mem
  zero_mem _ := MVSubalgebra.toAddSubmonoid.zero_mem
  not_mem' := MVSubalgebra.not_mem

@[simp]
lemma oAdd_mem {x y : A} {B : S} : x ∈ B → y ∈ B → (x ⊕ y) ∈ B :=
  MVSubalgebraClass.toAddSubmonoidClass.add_mem

@[simp]
lemma zero_mem (B : S) : 0 ∈ B := MVSubalgebraClass.toAddSubmonoidClass.zero_mem B

@[simp]
lemma not_mem {x : A} {B : S} : x ∈ B → - x ∈ B := MVSubalgebraClass.not_mem'

instance (B : MVSubalgebra A) : MVAlgebra B where
  neg := fun (⟨x,hx⟩ : B) => ⟨- x, B.not_mem hx⟩
  neg_neg := by intro _ ; ext1 ; apply neg_neg
  oAdd_not_zero := by intro _ ; ext1 ; apply oAdd_not_zero
  not_switch := by intro _ _ ; ext1 ; apply not_switch



end Subalgebra
