import MVAlgebras.Basic
import MVAlgebras.NaturalOrder

class MVAlgebraHom (A : Type*) (B : Type*) [MVAlgebra A] [MVAlgebra B] where
  toFun : A → B
  map_zero : toFun (0 : A) = (0 : B)
  map_not (x : A) : - (toFun x) = toFun (- x)
  map_oAdd (x y : A) : toFun (x ⊕ y) = toFun x ⊕ toFun y

infix:500 " →⊕ " => MVAlgebraHom

class MVAlgebraHomClass (F : Type*) (A : outParam Type*) (B : outParam Type*)
  [MVAlgebra A] [MVAlgebra B] extends FunLike F A B where
  map_zero (f : F) : f (0 : A) = (0 : B)
  map_not (f : F) (x : A) : - (f x) = f (- x)
  map_oAdd (f : F) (x y : A) : f (x ⊕ y) = f x ⊕ f y

variable {A B : Type*} {F : Type*} [MVAlgebra A] [MVAlgebra B] [MVAlgebraHomClass F A B]

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

lemma map_sup (f : F) (x y : A) : f (x ⊔ y) = f x ⊔ f y := by
  calc f (x ⊔ y)
  _ = f ((x ⊖ y) ⊕ y) := by rfl
  _ = (f (x ⊖ y) ⊕ f y) := by rw[map_oAdd]
  _ = ((f x ⊖ f y) ⊕ f y) := by rw[map_oNeg]
  _ = f x ⊔ f y := by rfl

lemma map_inf (f : F) (x y : A) : f (x ⊓ y) = f x ⊓ f y := by
  calc f (x ⊓ y)
  _ = f (x ⊙ (- x ⊕ y)) := by rfl
  _ = f x ⊙ f (- x ⊕ y) := by rw[map_oMul]
  _ = f x ⊙ ((- f x) ⊕ f y) := by simp
  _ = f x ⊓ f y := by rfl

instance : MVAlgebraHomClass (A →⊕ B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  map_zero f := f.map_zero
  map_not f := f.map_not
  map_oAdd f := f.map_oAdd

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
