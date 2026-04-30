import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

/- An MV Algebra is a is an algebra with
  certain axioms. The operations are here denoted
  + and -, and the constant is 0
  This allows us to think of some of the axioms as
  this being an AddCommMonoid
  Notice here that the symbol - rapresents what is usually ¬
  Since ¬ is already interpreted as negation of Prop, it cannot be used
  -/

/-- We however define an MV-Algebra as an Algebra with fewer axioms, with
  a binary +, an unary - and a constant 0
  This ends up being a commutative monoid, but commutativity is not asked as an axiom
  In fact, being a monoid is not asked at all: the element zero is only required
  to be a right identity, it being a left identity comes later
  Notice how two of the axioms are stated in the definition implicity,
  by saying that neg is involutive and + is a semigroup -/
class MVAlgebra (A : Type*) extends AddSemigroup A, InvolutiveNeg A, Zero A where
  add_zero (x : A) : x + 0 = x
  add_neg_zero (x : A) : x + (- (0 : A)) = - (0 : A)
  neg_switch (x y : A) : - ((- x) + y) + y = (- ((- y) + x)) + x

open MVAlgebra

lemma lem₁ [MVAlgebra A]
  (x y : A) : x + y = x + (0 + y) := by
    calc x + y
    _ = (x + 0) + y := by rw[add_zero x]
    _ = x + (0 + y) := by rw[add_assoc]

lemma lem₂ [MVAlgebra A]
  (x : A) : - (- 0 + x) + x = x := by
      calc - (-0 + x) + x
      _ = - (- x + 0) + 0 := neg_switch 0 x
      _ = - - x := by rw[add_zero (- x),add_zero (- - x)]
      _ = x := by rw[neg_neg]

lemma lem₃ [MVAlgebra A]
  (x : A) : 0 + x = x := by
  calc 0 + x
    _ = - (- 0 + (0 + x)) + (0 + x) := (lem₂ (0 + x)).symm
    _ = - (- 0 + 0 + x) + 0 + x := by rw[add_assoc,add_assoc]
    _ = - (- 0 + x) + x := by rw[MVAlgebra.add_zero,MVAlgebra.add_zero]
    _ = x := lem₂ x

lemma lem₄ [MVAlgebra A]
  (x y z : A) : - (- x + y) + (y + z) = - (- y + x) + (x + z) := by
      calc - (- x + y) + (y + z)
      _ = - (- x + y) + y + z := by rw[add_assoc]
      _ = - (- y + x) + x + z := by rw[neg_switch]
      _ = - (- y + x) + (x + z) := by rw[add_assoc]

lemma lem₅ [MVAlgebra A]
  (x : A) : - 0 = - x + x := by
    calc - 0
    _ = - (- x + - 0) + - 0 := (add_neg_zero (- (- x + - 0))).symm
    _ = - (- - 0 + x) + x := by rw[neg_switch]
    _ = - (0 + x) + x := by rw[neg_neg]
    _ = - x + x := by rw[lem₃ x]

lemma lem₆ [MVAlgebra A]
  (x y : A) : - 0 = - (y + x) + (x + y) := by
    calc - 0
    _ = - (- x + - y) + - 0 := by rw[add_neg_zero (- (-x + - y))]
    _ = - (- x + - y) + (- y + y) := by rw[lem₅ y]
    _ = - (- x + - y) + - y + y := by rw[add_assoc]
    _ = - (- - y + x) + x + y := by rw[neg_switch x (-y)]
    _ = - (y + x) + (x + y) := by rw[add_assoc,neg_neg]

instance (A : Type*) [MVAlgebra A] : AddCommMonoid A where
  add_zero := MVAlgebra.add_zero
  add_comm := by
    intro x y
    calc x + y
    _ = 0 + (x + y) := by rw[lem₃ (x + y)]
    _ = - - 0 + (x + y) := by rw[neg_neg]
    _ = - (- (y + x) + (x + y)) + (x + y) := by rw[lem₆ x y]
    _ = - (- (x + y) + (y + x)) + (y + x) := (neg_switch (x + y) (y + x)).symm
    _ = - - 0 + (y + x) := by rw[lem₆ y x]
    _ = 0 + (y + x) := by rw[neg_neg]
    _ = y + x := by rw[lem₃ (y + x)]
  zero_add := lem₃
  nsmul := nsmulRec
  nsmul_zero := by tauto

-- now we begin to add the usual notation of 1, ⊙ and ⊖, along with implementing simp

class OTimes (A : Type*) where
  oTimes : A → A → A

class ONeg (A : Type*) where
  oNeg : A → A → A

infix:500 "⊙" => OTimes.oTimes
infix:600 "⊖" => ONeg.oNeg

instance [MVAlgebra A] : One A where
  one := - (0 : A)

instance [MVAlgebra A] : OTimes A where
  oTimes x y := - ((- x) + - y)

instance [MVAlgebra A] : ONeg A where
  oNeg x y := x ⊙ (- y)

@[simp]
lemma neg_zero' [MVAlgebra A] : (1 : A) = - (0 : A) := rfl
lemma oTimes_dual [MVAlgebra A] (x y : A) : x ⊙ y = - (-x + -y) := rfl
lemma oNeg_def [MVAlgebra A] (x y : A) : x ⊖ y = x ⊙ (-y) := rfl

@[simp]
lemma oNeg_def' [MVAlgebra A] (x y : A) : x ⊖ y = - (- x + y) := by
  rw[oNeg_def,oTimes_dual,neg_neg]

@[simp]
lemma neg_one [MVAlgebra A] : - (1 : A) = 0 := by
  calc - (1 : A)
  _ = - - (0 : A) := by rw[neg_zero']
  _ = 0 := by rw[neg_neg]

@[simp]
lemma add_one [MVAlgebra A] (x : A) : x + 1 = 1 := by
  rw[neg_zero']
  exact MVAlgebra.add_neg_zero _

@[simp]
lemma one_add [MVAlgebra A] (x : A) : 1 + x = 1 := by
  rw[add_comm]
  exact add_one x

lemma add_dual [MVAlgebra A] {x y : A} : x + y = - ((- x) ⊙ (- y)) := by
  calc x + y
  _ = - - (x + y) := by rw[neg_neg]
  _ = - - (- - x + - - y) := by rw[neg_neg x,neg_neg y]
  _ = - ((- x) ⊙ (- y)) := by rw[oTimes_dual]

@[simp]
lemma neg_canc' [MVAlgebra A] (x : A) : x + - x = 1 := by
  calc x + - x
  _ = - x + x := by rw[add_comm]
  _ = - (0 + x) + x := by rw[zero_add]
  _ = - (- (1 : A) + x) + x := by rw[neg_one]
  _ = - (- x + 1) + 1 := by rw[neg_switch]
  _ = 1 := by rw[add_one]

@[simp]
lemma neg_canc [MVAlgebra A] (x : A) : - x + x = 1 := by
  rw[add_comm]
  exact neg_canc' x

@[simp]
lemma add_dual' {A : Type*} [MVAlgebra A] {x y : A} : - (x + y) = (- x) ⊙ (- y) := by
  calc - (x + y)
  _ = - (- - x + - - y) := by rw[neg_neg,neg_neg]
  _ = (- x) ⊙ (- y) := by rw[oTimes_dual]

@[simp]
lemma oTimes_dual' {A : Type*} [MVAlgebra A] {x y : A} : - (x ⊙ y) = - x + - y := by
  calc - (x ⊙ y)
  _ = - ((- - x) ⊙ (- - y)) := by rw[neg_neg,neg_neg]
  _ = - x + - y := by rw[add_dual]

lemma minus_add {A : Type*} [MVAlgebra A] {x y : A} : (x ⊖ y) + y = (y ⊖ x) + x := by
  calc (x ⊖ y) + y
  _ = - (- x + y) + y := by simp
  _ = - (- y + x) + x := by rw[neg_switch]
  _ = (y ⊖ x) + x := by simp

@[simp]
lemma neg_switch {A : Type*} [MVAlgebra A] (x y : A) :
  - ((- x) + y) + y = (- ((- y) + x)) + x := MVAlgebra.neg_switch _ _
