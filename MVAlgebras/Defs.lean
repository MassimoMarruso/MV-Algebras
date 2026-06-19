import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder

/-- An MV Algebra is a commutative monoid with an involution ¬
  with the following further axioms
  x ⊕ ¬ 0 = ¬ 0 and
  ¬ (¬ x ⊕ y) ⊕ y = ¬ (¬y ⊕ x) ⊕ x
  We  change the notation from ¬ to - to not
  compete with the negation of Prop
-/
class MVAlgebra (A : Type*) extends InvolutiveNeg A, AddCommMonoid A where
  oAdd_not_zero (x : A) : (x + (- (0 : A))) = - (0 : A)
  not_switch (x y : A) : ((- ((- x) + y)) + y) = (- ((- y) + x)) + x

/-- The class for the ⊕ notation. No axioms are given -/
class OAdd (A : Type*) where
  oAdd : A → A → A

infixl:74 (priority := default) " ⊕ "   => OAdd.oAdd

instance {A : Type*} [MVAlgebra A] : OAdd A where
  oAdd := MVAlgebra.toAddCommMonoid.add

variable {A : Type*} [MVAlgebra A]

@[simp]
lemma oAdd_assoc (x y z : A) : ((x ⊕ y) ⊕ z) = x ⊕ (y ⊕ z) :=
  MVAlgebra.toAddCommMonoid.add_assoc x y z

@[simp]
lemma oAdd_zero (x : A) : (x ⊕ 0) = x := MVAlgebra.toAddCommMonoid.add_zero x

@[simp]
lemma zero_oAdd (x : A) : (0 ⊕ x) = x := MVAlgebra.toAddCommMonoid.zero_add x

@[simp]
lemma oAdd_comm (x y : A) : (x ⊕ y) = y ⊕ x := MVAlgebra.toAddCommMonoid.add_comm x y

@[simp]
lemma oAdd_not_zero (x : A) : (x ⊕ (- (0 : A))) = - (0 : A) :=
  MVAlgebra.oAdd_not_zero x

@[simp]
lemma not_switch (x y : A) : ((- ((- x) ⊕ y)) ⊕ y) = (- ((- y) ⊕ x)) ⊕ x :=
  MVAlgebra.not_switch x y

-- we now begin to add the usual notation of 1, ⊙ and ⊖, along with implementing simp

/-- The class implementing the ⊙ notation -/
class OMul (A : Type*) where
  oMul : A → A → A

/-- The class implementing the ⊖ notation -/
class ONeg (A : Type*) where
  oNeg : A → A → A

infix:500 " ⊙ " => OMul.oMul
infix:600 " ⊖ " => ONeg.oNeg

instance : One A where
  one := - (0 : A)

instance : OMul A where
  oMul x y := - ((- x) ⊕ - y)

instance : ONeg A where
  oNeg x y := x ⊙ (- y)

@[simp]
lemma not_zero : (1 : A) = - (0 : A) := rfl
lemma oMul_dual (x y : A) : x ⊙ y = - (-x ⊕ -y) := rfl
@[simp]
lemma oNeg_def (x y : A) : x ⊖ y = x ⊙ (-y) := rfl

@[simp]
lemma not_iff_not' (x y : A) : x = y ↔ - x = - y := by
  apply Iff.intro
  case mp =>
    intro h ; subst h ; rfl
  case mpr =>
    intro h
    calc x
    _ = - - x := by rw[neg_neg]
    _ = - - y := by rw[h]
    _ = y := by rw[neg_neg]

@[simp]
lemma oNeg_def' (x y : A) : x ⊖ y = - (- x ⊕ y) := by
  rw[oNeg_def,oMul_dual,neg_neg]

@[simp]
lemma oNeg_switch (x y : A) :
  ((x ⊖ y) ⊕ y) = (y ⊖ x) ⊕ x := by
  rw[oNeg_def',oNeg_def']
  apply not_switch

@[simp]
lemma not_one : - (1 : A) = 0 := by
  calc - (1 : A)
  _ = - - (0 : A) := by rw[not_zero]
  _ = 0 := by rw[neg_neg]

@[simp]
lemma oAdd_one (x : A) : (x ⊕ 1) = 1 := by
  rw[not_zero]
  exact MVAlgebra.oAdd_not_zero x

@[simp]
lemma one_oAdd (x : A) : (1 ⊕ x) = 1 := by
  rw[oAdd_comm]
  exact oAdd_one x

lemma oAdd_dual (x y : A) : (x ⊕ y) = - ((- x) ⊙ (- y)) := by
  calc x ⊕ y
  _ = - - (x ⊕ y) := by rw[neg_neg]
  _ = - - (- - x ⊕ - - y) := by rw[neg_neg x,neg_neg y]
  _ = - ((- x) ⊙ (- y)) := by rw[oMul_dual]

@[simp]
lemma oAdd_not_self (x : A) : (x ⊕ - x) = 1 := by
  calc x ⊕ - x
  _ = - x ⊕ x := by rw[oAdd_comm]
  _ = - (0 ⊕ x) ⊕ x := by rw[zero_oAdd]
  _ = - (- (1 : A) ⊕ x) ⊕ x := by rw[not_one]
  _ = - (- x ⊕ 1) ⊕ 1 := by rw[not_switch]
  _ = 1 := by rw[oAdd_one]

@[simp]
lemma not_self_oAdd (x : A) : (- x ⊕ x) = 1 := by
  rw[oAdd_comm]
  apply oAdd_not_self

@[simp]
lemma not_oAdd (x y : A) : - (x ⊕ y) = (- x) ⊙ (- y) := by
  calc - (x ⊕ y)
  _ = - (- - x ⊕ - - y) := by rw[neg_neg,neg_neg]
  _ = (- x) ⊙ (- y) := by rw[oMul_dual]

@[simp]
lemma not_oMul (x y : A) : - (x ⊙ y) = - x ⊕ - y := by
  calc - (x ⊙ y)
  _ = - ((- - x) ⊙ (- - y)) := by rw[neg_neg,neg_neg]
  _ = - x ⊕ - y := by rw[oAdd_dual]

@[simp]
lemma not_not_oAdd {x y : A} : x ⊖ y = - (-x ⊕ y) := by
  calc x ⊖ y
  _ = x ⊙ (- y) := by rw[oNeg_def]
  _ = - (- x ⊕ - - y) := by rw[oMul_dual]
  _ = - (- x ⊕ y) := by rw[neg_neg]

lemma oNeg_oAdd {x y : A} : ((x ⊖ y) ⊕ y) = (y ⊖ x) ⊕ x := by
  calc (x ⊖ y) ⊕ y
  _ = - (- x ⊕ y) ⊕ y := by rw[not_not_oAdd]
  _ = - (- y ⊕ x) ⊕ x := by rw[not_switch]
  _ = (y ⊖ x) ⊕ x := by rw[not_not_oAdd]

lemma oAdd_oNeg {x y : A} : (y ⊕ (x ⊖ y)) = x ⊕ (y ⊖ x) := by
  calc (y ⊕ (x ⊖ y))
  _ = (x ⊖ y) ⊕ y := by rw[oAdd_comm]
  _ = (y ⊖ x) ⊕ x := by rw[oNeg_oAdd]
  _ = x ⊕ (y ⊖ x) := by rw[oAdd_comm]

--we now add an instance of CommMonoid, now with ⊙ being the operation

@[simp]
lemma oMul_comm (x y : A) : x ⊙ y = y ⊙ x := by
  rw[oMul_dual,oMul_dual,oAdd_comm]

@[simp]
lemma oMul_not_self (x : A) : x ⊙ (- x) = 0 := by
  calc x ⊙ (- x)
  _ = - (- x ⊕ x) := by rw[oMul_dual,neg_neg]
  _ = - 1 := by rw[not_self_oAdd]
  _ = 0 := by rw[not_one]

@[simp]
lemma not_self_oMul (x : A) : (- x) ⊙ x = 0 := by
  rw[oMul_comm]
  rw[oMul_not_self]

@[simp]
lemma oMul_assoc (x y z : A) : (x ⊙ y) ⊙ z = x ⊙ (y ⊙ z) := by
  rw[not_iff_not']
  calc - (x ⊙ y) ⊙ z
  _ = (-(x ⊙ y) ⊕ -z) := by rw[not_oMul]
  _ = (-x ⊕ -y) ⊕ -z := by rw[not_oMul]
  _ = -x ⊕ (-y ⊕ -z) := by rw[oAdd_assoc]
  _ = -x ⊕ -(y ⊙ z) := by rw[not_oMul]
  _ = - (x ⊙ (y ⊙ z)) := by rw[←not_oMul]

@[simp]
lemma one_oMul (x : A) : 1 ⊙ x = x := by
  rw[not_iff_not']
  rw[not_oMul]
  rw[not_one]
  rw[zero_oAdd]

@[simp]
lemma oMul_one (x : A) : x ⊙ 1 = x := by
  rw[oMul_comm]
  rw[one_oMul]

@[simp]
lemma oMul_zero (x : A) : (x ⊙ 0) = 0 := by
  rw[not_iff_not']
  rw[not_oMul]
  rw[←not_zero]
  rw[oAdd_one]

@[simp]
lemma zero_oMul (x : A) : (0 ⊙ x) = 0 := by
  rw[oMul_comm]
  apply oMul_zero

instance (A : Type*) [MVAlgebra A] : CommMonoid A where
  mul := (· ⊙ ·)
  mul_assoc := oMul_assoc
  one := 1
  one_mul := one_oMul
  mul_one := oMul_one
  mul_comm := oMul_comm

def isTrivial (A : Type*) [MVAlgebra A] : Prop := ∀ (x : A), x = 0

lemma not_oNeg_not (x y : A) : x ⊖ y = ((- y) ⊖ (- x)) := by
  calc x ⊖ y
  _ = - ((-x) ⊕ y) := by rw[oNeg_def']
  _ = - (y ⊕ (-x)) := by rw[oAdd_comm y]
  _ = - ((- - y) ⊕ (-x)) := by rw[neg_neg]
  _ = ((- y) ⊖ (- x)) := by rw[←oNeg_def']

lemma not_oNeg (x y : A) : (- x) ⊖ y = - (x ⊕ y) := by
  calc (- x) ⊖ y
  _ = (- x) ⊙ (- y) := by rw[oNeg_def]
  _ = - ((- - x) ⊕ (- - y)) := by rw[oMul_dual]
  _ = - (x ⊕ y) := by rw[neg_neg,neg_neg]

lemma not_oNeg' (x y : A) : - (x ⊖ y) = ((- x) ⊕ y) := by
  rw[oNeg_def']
  rw[neg_neg]
