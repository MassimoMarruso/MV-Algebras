import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

/- An MV Algebra is a commutative monoid with an involution ¬
  with the following further axioms
  x + ¬ 0 = ¬ 0 and
  ¬ (¬ x + y) + y = ¬ (¬y + x) + x
  The usual notation for the operation here called + is ⊕
  and we also change the notation from ¬ to - (it's a minus sign)
  This allows the code to see it as an AddCommMonoid and InvolutiveNeg
  with the two axioms above
  -/

/-It is however proven in Miroslav Kolařík's "Indipendence of the axiomatic system
  for MV-Algebras" that the axioms above are redundant.
  In particular, we can replace the AddCommMonoid stracture with an AddSemigroup that has
  a right identity
  We follow Kolařík's proof exactly, defining MV-Algebras with the reduced set of axioms
  and then proving that any MVAlgebra is an AddCommMonoid-/
class MVAlgebra (A : Type*) extends AddSemigroup A, InvolutiveNeg A, Zero A where
  add_zero (x : A) : x + 0 = x
  add_neg_zero (x : A) : x + (- (0 : A)) = - (0 : A)
  neg_switch (x y : A) : - ((- x) + y) + y = (- ((- y) + x)) + x

open MVAlgebra

variable {A : Type*} [MVAlgebra A]

lemma lem₁ (x y : A) : x + y = x + (0 + y) := by
    calc x + y
    _ = (x + 0) + y := by rw[add_zero x]
    _ = x + (0 + y) := by rw[add_assoc]

lemma lem₂ (x : A) : - (- 0 + x) + x = x := by
      calc - (-0 + x) + x
      _ = - (- x + 0) + 0 := neg_switch 0 x
      _ = - - x := by rw[add_zero (- x),add_zero (- - x)]
      _ = x := by rw[neg_neg]

lemma lem₃ (x : A) : 0 + x = x := by
  calc 0 + x
    _ = - (- 0 + (0 + x)) + (0 + x) := (lem₂ (0 + x)).symm
    _ = - (- 0 + 0 + x) + 0 + x := by rw[add_assoc,add_assoc]
    _ = - (- 0 + x) + x := by rw[MVAlgebra.add_zero,MVAlgebra.add_zero]
    _ = x := lem₂ x

lemma lem₄ (x y z : A) : - (- x + y) + (y + z) = - (- y + x) + (x + z) := by
      calc - (- x + y) + (y + z)
      _ = - (- x + y) + y + z := by rw[add_assoc]
      _ = - (- y + x) + x + z := by rw[neg_switch]
      _ = - (- y + x) + (x + z) := by rw[add_assoc]

lemma lem₅ (x : A) : - 0 = - x + x := by
    calc - 0
    _ = - (- x + - 0) + - 0 := (add_neg_zero (- (- x + - 0))).symm
    _ = - (- - 0 + x) + x := by rw[neg_switch]
    _ = - (0 + x) + x := by rw[neg_neg]
    _ = - x + x := by rw[lem₃ x]

lemma lem₆ (x y : A) : - 0 = - (y + x) + (x + y) := by
    calc - 0
    _ = - (- x + - y) + - 0 := by rw[add_neg_zero (- (-x + - y))]
    _ = - (- x + - y) + (- y + y) := by rw[lem₅ y]
    _ = - (- x + - y) + - y + y := by rw[add_assoc]
    _ = - (- - y + x) + x + y := by rw[neg_switch x (-y)]
    _ = - (y + x) + (x + y) := by rw[add_assoc,neg_neg]

instance : AddCommMonoid A where
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

-- we now begin to add the usual notation of 1, ⊙ and ⊖, along with implementing simp

class OTimes (A : Type*) where
  oTimes : A → A → A

class ONeg (A : Type*) where
  oNeg : A → A → A

infix:500 "⊙" => OTimes.oTimes
infix:600 "⊖" => ONeg.oNeg

instance : One A where
  one := - (0 : A)

instance : OTimes A where
  oTimes x y := - ((- x) + - y)

instance : ONeg A where
  oNeg x y := x ⊙ (- y)

@[simp]
lemma neg_zero' : (1 : A) = - (0 : A) := rfl
lemma oTimes_dual (x y : A) : x ⊙ y = - (-x + -y) := rfl
lemma oNeg_def (x y : A) : x ⊖ y = x ⊙ (-y) := rfl

@[simp]
lemma oNeg_def' (x y : A) : x ⊖ y = - (- x + y) := by
  rw[oNeg_def,oTimes_dual,neg_neg]

@[simp]
lemma neg_one : - (1 : A) = 0 := by
  calc - (1 : A)
  _ = - - (0 : A) := by rw[neg_zero']
  _ = 0 := by rw[neg_neg]

@[simp]
lemma add_one (x : A) : x + 1 = 1 := by
  rw[neg_zero']
  exact MVAlgebra.add_neg_zero _

@[simp]
lemma one_add (x : A) : 1 + x = 1 := by
  rw[add_comm]
  exact add_one x

lemma add_dual {x y : A} : x + y = - ((- x) ⊙ (- y)) := by
  calc x + y
  _ = - - (x + y) := by rw[neg_neg]
  _ = - - (- - x + - - y) := by rw[neg_neg x,neg_neg y]
  _ = - ((- x) ⊙ (- y)) := by rw[oTimes_dual]

@[simp]
lemma add_canc' (x : A) : x + - x = 1 := by
  calc x + - x
  _ = - x + x := by rw[add_comm]
  _ = - (0 + x) + x := by rw[zero_add]
  _ = - (- (1 : A) + x) + x := by rw[neg_one]
  _ = - (- x + 1) + 1 := by rw[neg_switch]
  _ = 1 := by rw[add_one]

@[simp]
lemma add_canc (x : A) : - x + x = 1 := by
  rw[add_comm]
  exact add_canc' x

@[simp]
lemma add_dual' {x y : A} : - (x + y) = (- x) ⊙ (- y) := by
  calc - (x + y)
  _ = - (- - x + - - y) := by rw[neg_neg,neg_neg]
  _ = (- x) ⊙ (- y) := by rw[oTimes_dual]

@[simp]
lemma oTimes_dual' {x y : A} : - (x ⊙ y) = - x + - y := by
  calc - (x ⊙ y)
  _ = - ((- - x) ⊙ (- - y)) := by rw[neg_neg,neg_neg]
  _ = - x + - y := by rw[add_dual]

lemma minus_add {x y : A} : (x ⊖ y) + y = (y ⊖ x) + x := by
  calc (x ⊖ y) + y
  _ = - (- x + y) + y := by simp
  _ = - (- y + x) + x := by rw[neg_switch]
  _ = (y ⊖ x) + x := by simp

@[simp]
lemma oTimes_comm (x y : A) : x ⊙ y = y ⊙ x := by
  rw[oTimes_dual,oTimes_dual,add_comm]

@[simp]
lemma oTimes_canc (x : A) : x ⊙ (- x) = 0 := by
  rw[oTimes_comm]
  rw[oTimes_dual]
  rw[neg_neg]
  rw[add_comm]
  rw[add_canc]
  rw[neg_one]

@[simp]
lemma oTimes_canc' (x : A) : (- x) ⊙ x = 0 := by
  rw[oTimes_comm]
  rw[oTimes_canc]

@[simp]
lemma neg_switch (x y : A) :
  - ((- x) + y) + y = (- ((- y) + x)) + x := MVAlgebra.neg_switch _ _

@[simp]
lemma neg_switch' (x y : A) :
  ( x ⊖ y) + y = ( y ⊖ x) + x := by
  rw[oNeg_def',oNeg_def']
  apply _root_.neg_switch
