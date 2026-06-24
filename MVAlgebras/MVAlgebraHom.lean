import MVAlgebras.Defs
import MVAlgebras.NaturalOrder
import MVAlgebras.Ideal.Defs
import Mathlib.Order.Hom.Lattice
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Equiv.Defs

@[ext]
class MVAlgebraHom (A : Type*) (B : Type*) [MVAlgebra A] [MVAlgebra B]
  extends AddMonoidHom A B where
  map_not (x : A) : - (toFun x) = toFun (- x)

infix:500 " →⊕ " => MVAlgebraHom

@[ext]
class MVAlgebraHomClass (F : Type*) (A : outParam Type*) (B : outParam Type*)
  [MVAlgebra A] [MVAlgebra B] [FunLike F A B] extends AddMonoidHomClass F A B where
  map_not (f : F) (x : A) : - (f x) = f (- x)

variable {A B : Type*} {F S T : Type*} [MVAlgebra A] [MVAlgebra B] [FunLike F A B]
  [MVAlgebraHomClass F A B] [SetLike S A] [SetLike T B]
[MVAlgebra_IdealClass S A] [MVAlgebra_IdealClass T B]

open MVIdeal MVOrder

instance : FunLike (A →⊕ B) A B where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    ext1
    apply h

instance : MVAlgebraHomClass (A →⊕ B) A B where
  map_zero f := f.map_zero
  map_not f := f.map_not
  map_add f := f.map_add

@[simp]
lemma map_not (f : F) {x : A} : - f x = f (- x) := MVAlgebraHomClass.map_not f x

@[simp]
lemma map_oAdd (f : F) {x y : A} : f (x ⊕ y) = (f x ⊕ f y) :=
  MVAlgebraHomClass.toAddMonoidHomClass.map_add f x y

@[simp]
lemma map_oMul (f : F) {x y : A} : f (x ⊙ y) = f x ⊙ f y := by
  calc f (x ⊙ y)
  _ = f (- (- x ⊕ - y)) := by rw[oMul_dual]
  _ = - f (- x ⊕ - y) := by rw[map_not]
  _ = - (- f x ⊕ - f y) := by rw[map_oAdd,map_not,map_not]

instance : MonoidHomClass F A B where
  map_one := by
    intro f
    calc f 1
    _ = f (- 0) := by simp
    _ = - f 0 := by rw[map_not]
    _ = - 0 := by rw[map_zero]
  map_mul := map_oMul

@[simp]
lemma map_oNeg (f : F) {x y : A} : f (x ⊖ y) = f x ⊖ f y := by
  calc f (x ⊖ y)
  _ = f (x ⊙ (- y)) := by rfl
  _ = f x ⊙ f (- y) := by rw[map_oMul]
  _ = f x ⊙ (- f y) := by rw[map_not]
  _ = f x ⊖ f y := by rfl

lemma monotone (f : F) : Monotone f := by
  intro x y h
  rw[le_iff_not_oAdd]
  calc - f x ⊕ f y
  _ = f (- x ⊕ y) := by simp
  _ = f 1 := by rw[h]
  _ = 1 := by simp

@[simp]
lemma map_sup (f : F) (x y : A) : f (x ⊔ y) = f x ⊔ f y := by
  calc f (x ⊔ y)
  _ = f ((x ⊖ y) ⊕ y) := by rfl
  _ = (f (x ⊖ y) ⊕ f y) := by rw[map_oAdd]
  _ = ((f x ⊖ f y) ⊕ f y) := by rw[map_oNeg]
  _ = f x ⊔ f y := by rfl

@[simp]
lemma map_inf (f : F) (x y : A) : f (x ⊓ y) = f x ⊓ f y := by
  calc f (x ⊓ y)
  _ = f (x ⊙ (- x ⊕ y)) := by rfl
  _ = f x ⊙ f (- x ⊕ y) := by rw[map_oMul]
  _ = f x ⊙ ((- f x) ⊕ f y) := by simp
  _ = f x ⊓ f y := by rfl

instance (f : A →⊕ B) : OrderHom A B where
  toFun := f.toFun
  monotone' := monotone f

instance : OrderHomClass F A B where
  map_rel := monotone

instance (f : A →⊕ B) : LatticeHom A B where
  toFun := f.toFun
  map_inf' := map_inf f
  map_sup' := map_sup f

instance : LatticeHomClass F A B where
  map_inf := map_inf
  map_sup := map_sup

@[reducible]
def comap (f : F) (I : T) : MVAlgebra_Ideal A where
  carrier := f ⁻¹' I
  zero_mem' := by
    rw[Set.mem_preimage]
    rw[map_zero]
    apply zero_mem
  le_mem := by
    intro x y hx h_le
    replace hx : f x ∈ I := by apply hx
    exact le_mem hx (monotone f h_le)
  add_mem' := by
    intro x y
    rw[Set.mem_preimage,Set.mem_preimage,Set.mem_preimage]
    intro hx hy
    rw[map_add]
    exact oAdd_mem hx hy

@[reducible]
def ker (f : F) : MVAlgebra_Ideal A := comap f (⊥ : MVAlgebra_Ideal B)

lemma mem_comap {f : F} {I : T} {x : A} : x ∈ comap f I ↔ f x ∈ I := by
  tauto

lemma le_iff_oNeg_ker (h : F) {x y : A} : h x ≤ h y ↔ x ⊖ y ∈ ker h := by
  calc h x ≤ h y
  _ ↔ (h x ⊖ h y) = 0 := by rw[le_iff_oMul_not,oNeg_def]
  _ ↔ h (x ⊖ y) = 0 := by rw[map_oNeg]
  _ ↔ h (x ⊖ y) ∈ (⊥ : MVAlgebra_Ideal B) := by rw[mem_bot_iff_zero]
  _ ↔ x ⊖ y ∈ comap h (⊥ : MVAlgebra_Ideal B) := by rw[mem_comap]
  _ ↔ x ⊖ y ∈ ker h := by rfl

lemma ker_bot_iff_injective (f : F) : Function.Injective f ↔ ker f = (⊥ : MVAlgebra_Ideal A) := by
  apply Iff.intro
  case mp =>
    intro h
    ext x
    suffices this : x ∈ ker f ↔ x ∈ (⊥ : MVAlgebra_Ideal A) from by apply this
    rw[mem_bot_iff_zero]
    unfold ker
    rw[mem_comap]
    rw[mem_bot_iff_zero]
    calc f x = 0
    _ ↔ f x = f 0 := by rw[map_zero]
    _ ↔ x = 0 := by
      apply Iff.intro
      case mp => apply h
      case mpr => tauto
  case mpr =>
    intro h x y hf
    have hf' {x y : A} (hf : f x = f y) : (y ⊙ (- x)) = 0 := by
      rw[←mem_bot_iff_zero]
      rw[←h]
      rw[mem_comap]
      rw[mem_bot_iff_zero]
      rw[map_oMul]
      rw[←map_not]
      rw[hf]
      rw[oMul_not_self]
    have hf₁ : (y ⊙ (- x)) = 0 := hf' hf
    have hf₂ : (x ⊙ (- y)) = 0 := hf' hf.symm
    calc x
    _ = 0 ⊕ x := by simp
    _ = (y ⊙ (- x)) ⊕ x := by rw[hf₁]
    _ = - ((- y) ⊕ (- - x)) ⊕ x := by simp
    _ = - ((- y) ⊕ x) ⊕ x := by simp
    _ = - ((- x) ⊕ y) ⊕ y := by rw[not_switch]
    _ = ((- - x) ⊙ (- y)) ⊕ y := by simp
    _ = (x ⊙ (- y)) ⊕ y := by simp
    _ = ((- y) ⊙ x) ⊕ y := by simp
    _ = (x ⊙ (- y)) ⊕ y := by simp
    _ = 0 ⊕ y := by rw[hf₂]
    _ = y := by simp

--theorem ker_prime_iff_MVChain (f : F) : isPrime (ker f) ↔ (¬ isTrivial B ∧ )

class MVEquiv (A : Type*) (B : Type*) [MVAlgebra A] [MVAlgebra B] extends
  AddEquiv A B, A →⊕ B

infix:77 "≃⊕" => MVEquiv

namespace MVHom

@[reducible]
def inverse {A B : Type*} [MVAlgebra A] [MVAlgebra B] (f : A →⊕ B) (g : B → A)
  (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) : B →⊕ A where
  toAddMonoidHom := f.inverse g hl hr
  map_not := by
    intro x
    have hs : Function.Surjective f := by
      apply Function.LeftInverse.surjective
      apply Function.RightInverse.leftInverse hr
    have ⟨x',hx⟩ := hs x
    calc - ((f.inverse g hl hr) x)
    _ = - ((AddMonoidHom.inverse f g hl hr) x) := rfl
    _ = - (g x) := by rw[AddMonoidHom.inverse_apply]
    _ = - (g (f x')) := by rw[hx]
    _ = - x' := by rw[hl]
    _ = g (f (- x') ) := by rw[hl]
    _ = g (- f x') := by rw[map_not]
    _ = g (- x) := by rw[hx]
    _ = (f.inverse g hl hr) (- x) := by rw[AddMonoidHom.inverse_apply]

end MVHom
