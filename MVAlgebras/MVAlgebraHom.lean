import MVAlgebras.Basic
import MVAlgebras.NaturalOrder
import MVAlgebras.Ideal

@[ext]
class MVAlgebraHom (A : Type*) (B : Type*) [MVAlgebra A] [MVAlgebra B] where
  toFun : A → B
  map_zero : toFun (0 : A) = (0 : B)
  map_not (x : A) : - (toFun x) = toFun (- x)
  map_oAdd (x y : A) : toFun (x ⊕ y) = toFun x ⊕ toFun y

infix:500 " →⊕ " => MVAlgebraHom

@[ext]
class MVAlgebraHomClass (F : Type*) (A : outParam Type*) (B : outParam Type*)
  [MVAlgebra A] [MVAlgebra B] extends FunLike F A B where
  map_zero (f : F) : f (0 : A) = (0 : B)
  map_not (f : F) (x : A) : - (f x) = f (- x)
  map_oAdd (f : F) (x y : A) : f (x ⊕ y) = f x ⊕ f y

variable {A B : Type*} {F S T : Type*} [MVAlgebra A] [MVAlgebra B] [MVAlgebraHomClass F A B]
[MVAlgebra_IdealClass S A] [MVAlgebra_IdealClass T B]

open MVIdeal MVOrder

instance : CoeOut (MVAlgebraHom A B) (A → B) where
  coe f := f.toFun

instance : MVAlgebraHomClass (A →⊕ B) A B where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    ext1
    apply h
  map_zero f := f.map_zero
  map_oAdd f := f.map_oAdd
  map_not f := f.map_not

@[simp]
lemma map_not (f : F) {x : A} : - f x = f (- x) := MVAlgebraHomClass.map_not f x

@[simp]
lemma map_oAdd (f : F) {x y : A} : f (x ⊕ y) = (f x ⊕ f y) := MVAlgebraHomClass.map_oAdd f x y

instance : ZeroHomClass F A B where
  map_zero := MVAlgebraHomClass.map_zero

@[simp]
lemma map_oMul (f : F) {x y : A} : f (x ⊙ y) = f x ⊙ f y := by
  calc f (x ⊙ y)
  _ = f (- (- x ⊕ - y)) := by rw[oMul_dual]
  _ = - f (- x ⊕ - y) := by rw[map_not]
  _ = - (- f x ⊕ - f y) := by rw[map_oAdd,map_not,map_not]

instance : OneHomClass F A B where
  map_one := by
    intro f
    calc f 1
    _ = f (- 0) := by simp
    _ = - f 0 := by rw[map_not]
    _ = - 0 := by rw[map_zero]

@[simp]
lemma map_oNeg (f : F) {x y : A} : f (x ⊖ y) = f x ⊖ f y := by
  calc f (x ⊖ y)
  _ = f (x ⊙ (- y)) := by rfl
  _ = f x ⊙ f (- y) := by rw[map_oMul]
  _ = f x ⊙ (- f y) := by rw[map_not]
  _ = f x ⊖ f y := by rfl

lemma monotone (f : F) : Monotone f := by
  intro x y h
  rw[le_iff₁]
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

instance (f : A →⊕ B) : AddMonoidHom A B where
  toFun := f.toFun
  map_add' _ _ := map_oAdd f
  map_zero' := map_zero f

instance : AddMonoidHomClass F A B where
  map_add := map_oAdd

instance (f : A →⊕ B) : MonoidHom A B where
  toFun := f.toFun
  map_one' := map_one f
  map_mul' _ _ := map_oMul f

instance : MonoidHomClass F A B where
  map_mul := map_oMul

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
  zero_mem := by
    rw[Set.mem_preimage]
    rw[map_zero]
    apply zero_mem
  le_mem := by
    intro x y hx h_le
    exact le_mem hx (monotone f h_le)
  oAdd_mem := by
    intro x y
    rw[Set.mem_preimage,Set.mem_preimage,Set.mem_preimage]
    intro hx hy
    rw[map_oAdd]
    exact oAdd_mem hx hy

@[reducible]
def ker (f : F) : MVAlgebra_Ideal A := comap f (⊥ : MVAlgebra_Ideal B)

lemma mem_comap {f : F} {I : T} {x : A} : x ∈ comap f I ↔ f x ∈ I := by
  tauto

lemma le_iff_oNeg (h : F) {x y : A} : h x ≤ h y ↔ x ⊖ y ∈ ker h := by
  calc h x ≤ h y
  _ ↔ (h x ⊖ h y) = 0 := by rw[le_iff₂,oNeg_def]
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
