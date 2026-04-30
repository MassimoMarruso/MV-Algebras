import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

/-! This file adds definitions, and proves several simple identities

--/

/- An MV Algebra is a is an algebra with
  certain axioms. The operations are here denoted
  + and -, and the constant is 0
  This allows us to think of some of the axioms as
  this being an AddCommMonoid
  Notice here that the symbol - rapresents what is usually ¬
  Since ¬ is already interpreted as negation of Prop, it cannot be used
  -/

namespace Basic

class OTimes (A : Type*) where
  oTimes : A → A → A

class ONeg (A : Type*) where
  oNeg : A → A → A

infix:500 "⊙" => OTimes.oTimes
infix:600 "⊖" => ONeg.oNeg

class MVAlgebra (A : Type*) extends AddCommMonoid A, InvolutiveNeg A where
  add_neg_zero {x : A} : x + (- (0 : A)) = - (0 : A)
  neg_switch {x y : A} : - ((- x) + y) + y = (- ((- y) + x)) + x

instance [MVAlgebra A] : One A where
  one := - (0 : A)

instance [MVAlgebra A] : OTimes A where
  oTimes x y := - ((- x) + - y)

instance [MVAlgebra A] : ONeg A where
  oNeg x y := x ⊙ (- y)

@[simp]
theorem neg_zero [MVAlgebra A] : (1 : A) = - (0 : A) := rfl
theorem oTimes_neg_add [MVAlgebra A] (x y : A) : x ⊙ y = - (-x + -y) := rfl
theorem oNeg_def [MVAlgebra A] (x y : A) : x ⊖ y = x ⊙ (-y) := rfl
@[simp]
theorem neg_switch [MVAlgebra A] (x y : A) : - (- x + y) + y = - (- y + x) + x :=
  MVAlgebra.neg_switch

@[simp]
lemma oNeg_def' [MVAlgebra A] (x y : A) : x ⊖ y = - (- x + y) := by
  rw[oNeg_def,oTimes_neg_add,neg_neg]

@[simp]
theorem neg_one [MVAlgebra A] : - (1 : A) = 0 := by
  calc - (1 : A)
  _ = - - (0 : A) := by rw[neg_zero]
  _ = 0 := by rw[neg_neg]

@[simp]
theorem add_one [MVAlgebra A] (x : A) : x + 1 = 1 := by
  rw[neg_zero]
  exact MVAlgebra.add_neg_zero

@[simp]
lemma one_add [MVAlgebra A] (x : A) : 1 + x = 1 := by
  rw[add_comm]
  exact add_one x

theorem add_neg_oTimes [MVAlgebra A] {x y : A} : x + y = - ((- x) ⊙ (- y)) := by
  calc x + y
  _ = - - (x + y) := by rw[neg_neg]
  _ = - - (- - x + - - y) := by rw[neg_neg x,neg_neg y]
  _ = - ((- x) ⊙ (- y)) := by rw[oTimes_neg_add]

@[simp]
theorem add_neg [MVAlgebra A] (x : A) : x + - x = 1 := by
  calc x + - x
  _ = - x + x := by rw[add_comm]
  _ = - (0 + x) + x := by rw[zero_add]
  _ = - (- (1 : A) + x) + x := by rw[neg_one]
  _ = - (- x + 1) + 1 := by rw[neg_switch]
  _ = 1 := by rw[add_one]

@[simp]
lemma neg_add [MVAlgebra A] (x : A) : - x + x = 1 := by
  rw[add_comm]
  exact add_neg x

@[simp]
theorem neg_add' {A : Type*} [MVAlgebra A] {x y : A} : - (x + y) = (- x) ⊙ (- y) := by
  calc - (x + y)
  _ = - (- - x + - - y) := by rw[neg_neg,neg_neg]
  _ = (- x) ⊙ (- y) := by rw[oTimes_neg_add]

@[simp]
theorem neg_oTimes' {A : Type*} [MVAlgebra A] {x y : A} : - (x ⊙ y) = - x + - y := by
  calc - (x ⊙ y)
  _ = - ((- - x) ⊙ (- - y)) := by rw[neg_neg,neg_neg]
  _ = - x + - y := by rw[add_neg_oTimes]

lemma minus_add {A : Type*} [MVAlgebra A] {x y : A} : (x ⊖ y) + y = (y ⊖ x) + x := by
  calc (x ⊖ y) + y
  _ = - (- x + y) + y := by simp
  _ = - (- y + x) + x := by rw[neg_switch]
  _ = (y ⊖ x) + x := by simp

end Basic
