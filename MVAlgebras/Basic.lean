import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

/- An MV Algebra is a commutative monoid with an involution ¬
  with the following further axioms
  x ⊕ ¬ 0 = ¬ 0 and
  ¬ (¬ x ⊕ y) ⊕ y = ¬ (¬y ⊕ x) ⊕ x
  We  change the notation from ¬ to - (it's a minus sign) to not
  compete with the negation of Prop
  -/

/-It is however proven in Miroslav Kolařík's "Indipendence of the axiomatic system
  for MV-Algebras" that the axioms above are redundant.
  In particular, we can replace the AddCommMonoid stracture with an AddSemigroup that has
  a right identity
  We follow Kolařík's proof exactly, defining MV-Algebras with the reduced set of axioms
  and then proving that any MVAlgebra is an AddCommMonoid-/

namespace Basic

class OAdd (A : Type*) where
  oAdd : A → A → A

infixl:74 (priority := default) " ⊕ "   => OAdd.oAdd

class MVAlgebra (A : Type*) extends OAdd A, InvolutiveNeg A, Zero A where
  oAdd_assoc (x y z : A) : ((x ⊕ y) ⊕ z) = x ⊕ (y ⊕ z)
  oAdd_zero (x : A) : (x ⊕ 0) = x
  oAdd_not_zero (x : A) : (x ⊕ (- (0 : A))) = - (0 : A)
  not_switch (x y : A) : ((- ((- x) ⊕ y)) ⊕ y) = (- ((- y) ⊕ x)) ⊕ x

variable {A : Type*} [MVAlgebra A]

@[simp]
lemma oAdd_assoc (x y z : A) : ((x ⊕ y) ⊕ z) = x ⊕ (y ⊕ z) := MVAlgebra.oAdd_assoc x y z

@[simp]
lemma oAdd_zero (x : A) : (x ⊕ 0) = x := MVAlgebra.oAdd_zero _

@[simp]
lemma oAdd_not_zero (x : A) : (x ⊕ (- (0 : A))) = - (0 : A) :=
  MVAlgebra.oAdd_not_zero x

@[simp]
lemma not_switch (x y : A) : ((- ((- x) ⊕ y)) ⊕ y) = (- ((- y) ⊕ x)) ⊕ x :=
  MVAlgebra.not_switch x y

/-now begins the proof, with several lemmas-/

lemma lem₁ (x y : A) : (x ⊕ y) = x ⊕ (0 ⊕ y) := by
    calc x ⊕ y
    _ = (x ⊕ 0) ⊕ y := by rw[oAdd_zero x]
    _ = x ⊕ (0 ⊕ y) := by rw[oAdd_assoc]

lemma lem₂ (x : A) : ((- ((- 0 : A) ⊕ x)) ⊕ x) = x := by
      calc (- ((- 0 : A) ⊕ x)) ⊕ x
      _ = (- (-x ⊕ 0)) ⊕ 0 := by rw[not_switch]
      _ = - - x := by rw[oAdd_zero (- x),oAdd_zero (- - x)]
      _ = x := by rw[neg_neg x]

lemma zero_oAdd (x : A) : (0 ⊕ x) = x := by
  calc 0 ⊕ x
    _ = (- (- 0 ⊕ (0 ⊕ x))) ⊕ (0 ⊕ x) := (lem₂ (0 ⊕ x)).symm
    _ = ((- ((- 0 ⊕ 0) ⊕ x)) ⊕ 0) ⊕ x := by rw[oAdd_assoc,oAdd_assoc]
    _ = (- (- 0 ⊕ x)) ⊕ x := by rw[oAdd_zero,oAdd_zero]
    _ = x := lem₂ x

lemma lem₄ (x y z : A) : ((- (- x ⊕ y)) ⊕ (y ⊕ z)) = (- (- y ⊕ x)) ⊕ (x ⊕ z) := by
      calc (- (- x ⊕ y)) ⊕ (y ⊕ z)
      _ = ((- (- x ⊕ y)) ⊕ y) ⊕ z := by rw[oAdd_assoc]
      _ = ((- (- y ⊕ x)) ⊕ x) ⊕ z := by rw[not_switch]
      _ = (- (- y ⊕ x)) ⊕ (x ⊕ z) := by rw[oAdd_assoc]

lemma lem₅ (x : A) : - 0 = - x ⊕ x := by
    calc - 0
    _ = - (- x ⊕ - 0) ⊕ - 0 := (oAdd_not_zero (- (- x ⊕ - 0))).symm
    _ = - (- - 0 ⊕ x) ⊕ x := by rw[not_switch]
    _ = - (0 ⊕ x) ⊕ x := by rw[neg_neg]
    _ = - x ⊕ x := by rw[zero_oAdd x]

lemma lem₆ (x y : A) : - 0 = - (y ⊕ x) ⊕ (x ⊕ y) := by
    calc - 0
    _ = - (- x ⊕ - y) ⊕ - 0 := by rw[oAdd_not_zero (- (-x ⊕ - y))]
    _ = - (- x ⊕ - y) ⊕ (- y ⊕ y) := by rw[lem₅ y]
    _ = - (- x ⊕ - y) ⊕ - y ⊕ y := by rw[oAdd_assoc]
    _ = - (- - y ⊕ x) ⊕ x ⊕ y := by rw[not_switch x (-y)]
    _ = - (y ⊕ x) ⊕ (x ⊕ y) := by rw[oAdd_assoc,neg_neg]

@[simp]
theorem oAdd_comm (x y : A) : (x ⊕ y) = y ⊕ x := by
  calc x ⊕ y
  _ = 0 ⊕ (x ⊕ y) := by rw[zero_oAdd (x ⊕ y)]
  _ = - - 0 ⊕ (x ⊕ y) := by rw[neg_neg]
  _ = - (- (y ⊕ x) ⊕ (x ⊕ y)) ⊕ (x ⊕ y) := by rw[lem₆ x y]
  _ = - (- (x ⊕ y) ⊕ (y ⊕ x)) ⊕ (y ⊕ x) := (not_switch (x ⊕ y) (y ⊕ x)).symm
  _ = - - 0 ⊕ (y ⊕ x) := by rw[lem₆ y x]
  _ = 0 ⊕ (y ⊕ x) := by rw[neg_neg]
  _ = y ⊕ x := by rw[zero_oAdd (y ⊕ x)]

def nsmul (n : Nat) : A → A :=
  match n with
  |0 => (fun _ => 0)
  |n + 1 => (fun x => (nsmul n x) ⊕ x)

--we now have proven that A is an AddCommMonoid

instance (A : Type*) [MVAlgebra A] : AddCommMonoid A where
  add := OAdd.oAdd
  add_assoc := oAdd_assoc
  add_zero := MVAlgebra.oAdd_zero
  add_comm := oAdd_comm
  zero_add := zero_oAdd
  nsmul := nsmul

-- we now begin to add the usual notation of 1, ⊙ and ⊖, along with implementing simp

class OMul (A : Type*) where
  oMul : A → A → A

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
    intro h
    subst_eqs
    tauto
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
lemma not_switch' (x y : A) :
  ((x ⊖ y) ⊕ y) = ( y ⊖ x) ⊕ x := by
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

lemma oAdd_dual {x y : A} : (x ⊕ y) = - ((- x) ⊙ (- y)) := by
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
  exact oAdd_not_self x

@[simp]
lemma oAdd_dual' {x y : A} : - (x ⊕ y) = (- x) ⊙ (- y) := by
  calc - (x ⊕ y)
  _ = - (- - x ⊕ - - y) := by rw[neg_neg,neg_neg]
  _ = (- x) ⊙ (- y) := by rw[oMul_dual]

@[simp]
lemma oMul_dual' {x y : A} : - (x ⊙ y) = - x ⊕ - y := by
  calc - (x ⊙ y)
  _ = - ((- - x) ⊙ (- - y)) := by rw[neg_neg,neg_neg]
  _ = - x ⊕ - y := by rw[oAdd_dual]

lemma oNeg_oAdd {x y : A} : ((x ⊖ y) ⊕ y) = (y ⊖ x) ⊕ x := by
  calc (x ⊖ y) ⊕ y
  _ = - (- x ⊕ y) ⊕ y := by simp
  _ = - (- y ⊕ x) ⊕ x := by rw[not_switch]
  _ = (y ⊖ x) ⊕ x := by simp

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
  _ = (-(x ⊙ y) ⊕ -z) := by rw[oMul_dual']
  _ = (-x ⊕ -y) ⊕ -z := by rw[oMul_dual']
  _ = -x ⊕ (-y ⊕ -z) := by rw[oAdd_assoc]
  _ = -x ⊕ -(y ⊙ z) := by rw[oMul_dual']
  _ = - (x ⊙ (y ⊙ z)) := by rw[←oMul_dual']

@[simp]
lemma one_oMul (x : A) : 1 ⊙ x = x := by
  rw[not_iff_not']
  rw[oMul_dual']
  rw[not_one]
  rw[zero_oAdd]

@[simp]
lemma oMul_one (x : A) : x ⊙ 1 = x := by
  rw[oMul_comm]
  rw[one_oMul]

instance (A : Type*) [MVAlgebra A] : CommMonoid A where
  mul := (· ⊙ ·)
  mul_assoc := oMul_assoc
  one := 1
  one_mul := one_oMul
  mul_one := oMul_one
  mul_comm := oMul_comm

def isTrivial (A : Type*) [MVAlgebra A] : Prop := ∀ (x : A), x = 0

end Basic
