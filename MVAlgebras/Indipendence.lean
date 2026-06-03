import MVAlgebras.Defs

/-It is proven in Miroslav Kolařík's "Indipendence of the axiomatic system
  for MV-Algebras" that the axioms above are redundant.
  In particular, we can replace the AddCommMonoid stracture with an AddSemigroup that has
  a right identity
  We follow Kolařík's proof exactly, defining MV-Algebras with the reduced set of axioms -/

/-now begins the proof, with several lemmas-/

variable {A : Type*}


namespace Reduced

class MVAlgebra (A : Type*) extends InvolutiveNeg A, Zero A, OAdd A where
  oAdd_assoc' : ∀ (x y z : A), ((x ⊕ y) ⊕ z) = x ⊕ (y ⊕ z)
  oAdd_not_zero' : ∀ (x : A), (x ⊕ (-(0 : A))) = -(0 : A)
  not_switch' : ∀ (x y : A), ((-((-x) ⊕ y)) ⊕ y) = (-((-y) ⊕ x)) ⊕ x
  oAdd_zero' : ∀ (x : A), (x ⊕ 0) = x

open MVAlgebra

variable [MVAlgebra A]

lemma lem₁ (x y : A) : (x ⊕ y) = x ⊕ (0 ⊕ y) := by
    calc x ⊕ y
    _ = (x ⊕ 0) ⊕ y := by rw[oAdd_zero' x]
    _ = x ⊕ (0 ⊕ y) := by rw[oAdd_assoc']

lemma lem₂ (x : A) : ((- ((- 0 : A) ⊕ x)) ⊕ x) = x := by
      calc (- ((- 0 : A) ⊕ x)) ⊕ x
      _ = (- (-x ⊕ 0)) ⊕ 0 := by rw[not_switch']
      _ = - - x := by rw[oAdd_zero' (- x),oAdd_zero' (- - x)]
      _ = x := by rw[neg_neg x]

lemma zero_oAdd' (x : A) : (0 ⊕ x) = x := by
  calc 0 ⊕ x
    _ = (- (- 0 ⊕ (0 ⊕ x))) ⊕ (0 ⊕ x) := (lem₂ (0 ⊕ x)).symm
    _ = ((- ((- 0 ⊕ 0) ⊕ x)) ⊕ 0) ⊕ x := by rw[oAdd_assoc',oAdd_assoc']
    _ = (- (- 0 ⊕ x)) ⊕ x := by rw[oAdd_zero',oAdd_zero']
    _ = x := lem₂ x

lemma lem₄ (x y z : A) : ((- (- x ⊕ y)) ⊕ (y ⊕ z)) = (- (- y ⊕ x)) ⊕ (x ⊕ z) := by
      calc (- (- x ⊕ y)) ⊕ (y ⊕ z)
      _ = ((- (- x ⊕ y)) ⊕ y) ⊕ z := by rw[oAdd_assoc']
      _ = ((- (- y ⊕ x)) ⊕ x) ⊕ z := by rw[not_switch']
      _ = (- (- y ⊕ x)) ⊕ (x ⊕ z) := by rw[oAdd_assoc']

lemma lem₅ (x : A) : - 0 = - x ⊕ x := by
    calc - 0
    _ = - (- x ⊕ - 0) ⊕ - 0 := (oAdd_not_zero' (- (- x ⊕ - 0))).symm
    _ = - (- - 0 ⊕ x) ⊕ x := by rw[not_switch']
    _ = - (0 ⊕ x) ⊕ x := by rw[neg_neg]
    _ = - x ⊕ x := by rw[zero_oAdd' x]

lemma lem₆ (x y : A) : - 0 = - (y ⊕ x) ⊕ (x ⊕ y) := by
    calc - 0
    _ = - (- x ⊕ - y) ⊕ - 0 := by rw[oAdd_not_zero' (- (-x ⊕ - y))]
    _ = - (- x ⊕ - y) ⊕ (- y ⊕ y) := by rw[lem₅ y]
    _ = - (- x ⊕ - y) ⊕ - y ⊕ y := by rw[oAdd_assoc']
    _ = - (- - y ⊕ x) ⊕ x ⊕ y := by rw[not_switch' x (-y)]
    _ = - (y ⊕ x) ⊕ (x ⊕ y) := by rw[oAdd_assoc',neg_neg]

@[simp]
theorem oAdd_comm' (x y : A) : (x ⊕ y) = y ⊕ x := by
  calc x ⊕ y
  _ = 0 ⊕ (x ⊕ y) := by rw[zero_oAdd' (x ⊕ y)]
  _ = - - 0 ⊕ (x ⊕ y) := by rw[neg_neg]
  _ = - (- (y ⊕ x) ⊕ (x ⊕ y)) ⊕ (x ⊕ y) := by rw[lem₆ x y]
  _ = - (- (x ⊕ y) ⊕ (y ⊕ x)) ⊕ (y ⊕ x) := (not_switch' (x ⊕ y) (y ⊕ x)).symm
  _ = - - 0 ⊕ (y ⊕ x) := by rw[lem₆ y x]
  _ = 0 ⊕ (y ⊕ x) := by rw[neg_neg]
  _ = y ⊕ x := by rw[zero_oAdd' (y ⊕ x)]

instance [MVAlgebra A] : Add A where
  add := MVAlgebra.toOAdd.oAdd

instance (A : Type*) [MVAlgebra A] : _root_.MVAlgebra A where
  add_assoc := MVAlgebra.oAdd_assoc'
  add_zero := MVAlgebra.oAdd_zero'
  not_switch := MVAlgebra.not_switch'
  oAdd_not_zero := MVAlgebra.oAdd_not_zero'
  zero_add := zero_oAdd'
  add_comm := oAdd_comm'
  nsmul := nsmulRec

end Reduced
