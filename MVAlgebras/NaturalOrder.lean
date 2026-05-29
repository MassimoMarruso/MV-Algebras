import MVAlgebras.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/- This file introduces what is called the "Natural Order" on MVAlgebras
  The beginning of the file introduces a notation ≤ without any propreties, then
  equivalent notions are derived. Finally, it is proven to be a partial order
  This proof is from the first chapter of Mundici
  Later in the file it is proven to be a lattice -/

variable {A : Type*} [MVAlgebra A]

instance [MVAlgebra A] : LE A where
  le x y := ((- x) ⊕ y) = 1

lemma le_iff₁ {x y : A} : x ≤ y ↔ ((- x) ⊕ y) = 1 := by
  rfl

lemma le_iff₂ {x y : A} : x ≤ y ↔ x ⊙ (- y) = 0 := by
  calc x ≤ y
  _ ↔ ((- x) ⊕ y) = 1 := by rw[le_iff₁]
  _ ↔ - (x ⊙ (- y)) = 1 := by rw[oMul_dual',neg_neg y]
  _ ↔ - (x ⊙ (- y)) = - 0 := by rw[not_zero]
  _ ↔ (x ⊙ (-y)) = 0 := by rw[←not_iff_not' _ 0]

lemma le_iff₃ {x y : A} : x ≤ y ↔ y = (x ⊕ (y ⊖ x)) := by
  apply Iff.intro
  case mp =>
    intro h
    calc y
    _ = 0 ⊕ y := by rw[zero_oAdd]
    _ = ((x ⊙ (- y)) ⊕ y) := by rw[le_iff₂.mp h]
    _ = - (- x ⊕ y) ⊕ y := by simp
    _ = - (- y ⊕ x) ⊕ x := by rw[not_switch]
    _ = x ⊕ - (- y ⊕ x) := by rw[oAdd_comm]
    _ = x ⊕ (y ⊖ x) := by simp
  case mpr =>
    intro h
    apply le_iff₂.mpr
    calc x ⊙ (- y)
    _ = - (- x ⊕ y) := by simp
    _ = - (- x ⊕ (x ⊕ y ⊖ x)) := by rw[←h]
    _ = - (- x ⊕ (y ⊖ x ⊕ x)) := by rw[oAdd_comm x]
    _ = - ((y ⊖ x ⊕ x) ⊕ - x) := by rw[oAdd_comm (-x)]
    _ = - (((x ⊖ y) ⊕ y) ⊕ - x) := by rw[oNeg_oAdd]
    _ = - ((x ⊖ y) ⊕ (y ⊕ - x)) := by rw[oAdd_assoc]
    _ = - ((x ⊖ y) ⊕ (- x ⊕ y)) := by rw[oAdd_comm (- x)]
    _ = - ((x ⊖ y) ⊕ - - (- x ⊕ y)) := by rw[neg_neg]
    _ = - ((x ⊖ y) ⊕ - (x ⊖ y)) := by rw[oNeg_def']
    _ = - (1 : A) := by rw[oAdd_not_self (x ⊖ y)]
    _ = 0 := by simp

lemma le_iff₄ {x y : A} : x ≤ y ↔ ∃ (z : A), (x ⊕ z) = y := by
  apply Iff.intro
  case mp =>
    intro h
    use y ⊖ x
    apply (le_iff₃.mp h).symm
  case mpr =>
    intro ⟨z,h⟩
    apply le_iff₁.mpr
    calc -x ⊕ y
    _ = - x ⊕ (x ⊕ z) := by rw[←h]
    _ = (- x ⊕ x) ⊕ z := by rw[oAdd_assoc]
    _ = 1 ⊕ z := by simp
    _ = 1 := by rw[one_oAdd]

namespace MVOrder

variable {A : Type*} [MVAlgebra A]

instance {A : Type*} [MVAlgebra A] : PartialOrder A where
  le x y := x ≤ y
  le_refl := by
    intro x
    rw[le_iff₁]
    simp
  le_trans := by
    intro x y z
    rw[le_iff₄,le_iff₄,le_iff₄]
    intro ⟨x',hx⟩ ⟨y',hy⟩
    use x' ⊕ y'
    calc x ⊕ (x' ⊕ y')
    _ = x ⊕ x' ⊕ y' := by rw[oAdd_assoc]
    _ = y ⊕ y' := by rw[hx]
    _ = z := by rw[hy]
  le_antisymm := by
    intro x y h₁ h₂
    replace h₁ : x ⊙ (- y) = 0 := le_iff₂.mp h₁
    replace h₂ : x = y ⊕ (x ⊖ y) := le_iff₃.mp h₂
    calc x
    _ = y ⊕ (x ⊖ y) := h₂
    _ = y ⊕ (x ⊙ (- y)) := by rw[oNeg_def]
    _ = y := by rw[h₁,oAdd_zero]

lemma not_iff (a : A) (x : A) : -a = x ↔ (a ⊕ x) = 1 ∧ a ⊙ x = 0 := by
  apply Iff.intro
  case mpr =>
    intro ⟨h₁,h₂⟩
    replace h₁ : (- - a ⊕ x) = 1 := by
      rw[neg_neg]
      exact h₁
    replace h₁ : -a ≤ x := le_iff₁.mpr h₁
    have h₂ : x ⊙ (- - a) = 0 := by
      rw[neg_neg]
      rw[oMul_comm]
      exact h₂
    replace h₂ : x ≤ -a := le_iff₂.mpr h₂
    exact le_antisymm h₁ h₂
  case mp =>
    intro h
    subst_eqs
    exact ⟨oAdd_not_self a,oMul_not_self a⟩

lemma not_le (x y : A) : x ≤ y ↔ - y ≤ - x := by
  calc x ≤ y
  _ ↔ (-x ⊕ y) = 1 := by rw[le_iff₁]
  _ ↔ - (x ⊙ (- y)) = 1 := by rw[oAdd_dual,neg_neg]
  _ ↔ (x ⊙ (- y)) = - 1 := by rw[not_iff_not',neg_neg]
  _ ↔ x ⊙ (- y) = 0 := by rw[not_one]
  _ ↔ (- y) ⊙ (- - x) = 0 := by rw[oMul_comm,neg_neg]
  _ ↔ - y ≤ - x := by rw[le_iff₂]

lemma antitone_not : Antitone (fun (x : A) => - x) := by
  intro x y hle
  suffices this : - y ≤ - x from by apply this
  rw[←not_le]
  apply hle

lemma oAdd_le (x y z : A) (h : x ≤ y) : (x ⊕ z) ≤ y ⊕ z := by
  apply le_iff₄.mpr
  replace ⟨w,h⟩ := le_iff₄.mp h
  use w
  calc ((x ⊕ z) ⊕ w)
  _ = x ⊕ (z ⊕ w) := by rw[oAdd_assoc]
  _ = x ⊕ (w ⊕ z) := by rw[oAdd_comm z]
  _ = (x ⊕ w) ⊕ z := by rw[oAdd_assoc]
  _ = y ⊕ z := by rw[h]

lemma le_oAdd (x y z : A) (h : x ≤ y) : (z ⊕ x) ≤ z ⊕ y := by
  rw[oAdd_comm z x]
  rw[oAdd_comm z y]
  exact oAdd_le x y z h

lemma oMul_le (x y z : A) (h : x ≤ y) : x ⊙ z ≤ y ⊙ z := by
  suffices this : - (y ⊙ z) ≤ - (x ⊙ z) from by apply (not_le _ _).mpr ; exact this
  suffices this : (- y ⊕ - z) ≤ - x ⊕ - z from by rw[oMul_dual',oMul_dual'] ; exact this
  suffices this : -y ≤ - x from oAdd_le _ _ _ this
  exact (not_le _ _).mp h

lemma le_oMul (x y z : A) (h : x ≤ y) : z ⊙ x ≤ z ⊙ y := by
  suffices this : x ⊙ z ≤ y ⊙ z from by
    rw[oMul_comm z x]
    rw[oMul_comm z y]
    apply this
  exact oMul_le _ _ _ h

lemma sup_le (x y z : A) (hx : x ≤ z) (hy : y ≤ z) : ((x ⊖ y) ⊕ y) ≤ z := by
  replace hx := le_iff₁.mp hx
  replace hy := le_iff₃.mp hy
  apply le_iff₁.mpr
  calc -(x ⊖ y ⊕ y) ⊕ z
    _ = -((- - (x ⊖ y)) ⊕ y) ⊕ z := by rw[neg_neg]
    _ = ((- (x ⊖ y)) ⊖ y) ⊕ z := by rw[oNeg_def' (- (x ⊖ y))]
    _ = ((- (x ⊖ y)) ⊖ y) ⊕ (y ⊕ (z ⊖ y)) := by rw[←hy]
    _ = ((- (x ⊖ y)) ⊖ y) ⊕ y ⊕ (z ⊖ y) := by rw[oAdd_assoc]
    _ = (y ⊖ (- (x ⊖ y))) ⊕ (- (x ⊖ y)) ⊕ (z ⊖ y) := by rw[not_switch']
    _ = (y ⊖ (- (x ⊖ y))) ⊕ - -(- x ⊕ y) ⊕ (z ⊖ y) := by rw[oNeg_def' x y]
    _ = (y ⊖ (- (x ⊖ y))) ⊕ (- x ⊕ y) ⊕ (z ⊖ y) := by rw[neg_neg]
    _ = (y ⊖ (- (x ⊖ y))) ⊕ (- x) ⊕ (y ⊕ (z ⊖ y)) := by rw[oAdd_assoc,oAdd_assoc,oAdd_assoc]
    _ = (y ⊖ (- (x ⊖ y))) ⊕ (- x) ⊕ z := by rw[←hy]
    _ = (y ⊖ (- (x ⊖ y))) ⊕ 1 := by rw[oAdd_assoc,hx]
    _ = 1 := by rw[oAdd_one]

lemma not_sup' (y z : A) : ((-y) ⊖ (-z) ⊕ (- z)) = -(y ⊙ (-y ⊕ z)) := by
    calc (-y) ⊖ (-z) ⊕ (- z)
    _ = (-z) ⊖ (-y) ⊕ (-y) := by rw[not_switch']
    _ = (-z) ⊙ (- - y) ⊕ (- y) := by rw[oNeg_def]
    _ = - (z ⊕ - y) ⊕ -y := by rw[oMul_dual,neg_neg,neg_neg]
    _ = -y ⊕ - (- y ⊕ z) := by rw[oAdd_comm z,oAdd_comm]
    _ = -(y ⊙ (-y ⊕ z)) := by rw[oMul_dual,neg_neg]

instance : Lattice A where
  sup x y := (x ⊖ y) ⊕ y
  inf x y := x ⊙ (- x ⊕ y)
  le_sup_left := by
    intro x y
    suffices this : x ≤ (y ⊖ x) ⊕ x from by rw[not_switch'] ; exact this
    apply le_iff₄.mpr
    use y ⊖ x
    exact oAdd_comm x _
  le_sup_right := by
    intro x y
    apply le_iff₄.mpr
    use x ⊖ y
    exact oAdd_comm _ _
  sup_le := sup_le
  le_inf := by
    intro x y z hy hz
    suffices this : - (y ⊙ (-y ⊕ z)) ≤ -x from by rw[not_le] ; exact this
    replace hy : -y ≤ - x := (not_le _ _).mp hy
    replace hz : -z ≤ - x := (not_le _ _).mp hz
    suffices this : ((-y) ⊖ (-z) ⊕ (- z)) ≤ - x from by rw[←not_sup'] ; exact this
    exact sup_le _ _ _ hy hz
  inf_le_left := by
    intro x y
    suffices h : - x ≤ - (x ⊙ (- x ⊕ y)) from by rw[not_le] ; exact h
    suffices h : - x ≤ (-x) ⊖ (-y) ⊕ (-y) from by rw[←not_sup'] ; exact h
    suffices h : - x ≤ (-y) ⊖ (-x) ⊕ (-x) from by rw[not_switch'] ; exact h
    rw[le_iff₄]
    use (-y) ⊖ (-x)
    rw[oAdd_comm]
  inf_le_right := by
    intro x y
    suffices h : - y ≤ - (x ⊙ (-x ⊕ y)) from by rw[not_le] ; exact h
    suffices h : - y ≤ (-x) ⊖ (-y) ⊕ (- y) from by rw[←not_sup'] ; exact h
    suffices h : - y ≤ - y ⊕ (-x) ⊖ (-y) from by rw[oAdd_comm] ; exact h
    rw[le_iff₄]
    use (-x)⊖(-y)

@[simp]
lemma inf_def (x y : A) : x ⊓ y = x ⊙ (- x ⊕ y) := rfl

@[simp]
lemma sup_def (x y : A) : x ⊔ y = (x ⊖ y) ⊕ y := rfl

@[simp]
lemma not_sup (x y : A) : - (x ⊔ y) = (-x) ⊓ (-y) := by
  rw[inf_def,sup_def]
  suffices this : - ((- - x) ⊖ (- - y) ⊕ - - y) = (-x) ⊙ (- - x ⊕ - y) from by
    rw[neg_neg x] at this
    rw[neg_neg y] at this
    rw[neg_neg x]
    apply this
  rw[not_sup' (-x) (-y)]
  rw[neg_neg]

@[simp]
lemma not_inf (x y : A) : - (x ⊓ y) = (-x) ⊔ (-y) := by
  rw[not_iff_not',neg_neg]
  rw[not_sup,neg_neg,neg_neg]

lemma oMul_le_le_not_oAdd (x y z : A) : x ⊙ y ≤ z ↔ x ≤ - y ⊕ z := by
  calc x ⊙ y ≤ z
  _ ↔ (- (x ⊙ y) ⊕ z) = 1 := by rw[le_iff₁]
  _ ↔ ((- x ⊕ - y) ⊕ z) = 1 := by rw[oMul_dual']
  _ ↔ (- x ⊕ (- y ⊕ z)) = 1 := by rw[oAdd_assoc]
  _ ↔ x ≤ - y ⊕ z := by rw[le_iff₁]

lemma oMul_sup_distrib (x y z : A) : x ⊙ (y ⊔ z) = (x ⊙ y) ⊔ (x ⊙ z) := by
  have h₁ : (x ⊙ y) ≤ x ⊙ (y ⊔ z) := by
    apply le_oMul
    exact le_sup_left
  have h₂ : (x ⊙ z) ≤ x ⊙ (y ⊔ z) := by
    apply le_oMul
    exact le_sup_right
  have h_le := (@sup_le_iff A _ _ _ _).mpr ⟨h₁,h₂⟩
  have le_h : x ⊙ (y ⊔ z) ≤ (x ⊙ y) ⊔ (x ⊙ z) := by
    let t := (x ⊙ y) ⊔ (x ⊙ z)
    have h₁' : x ⊙ y ≤ t := by unfold t ; apply le_sup_left
    have h₂' : x ⊙ z ≤ t := by unfold t ; apply le_sup_right
    replace h₁' : y ≤ (- x) ⊕ t := by rw[←oMul_le_le_not_oAdd,oMul_comm] ; exact h₁'
    replace h₂' : z ≤ (- x) ⊕ t := by rw[←oMul_le_le_not_oAdd,oMul_comm] ; exact h₂'
    have h' : y ⊔ z ≤ (- x) ⊕ t := sup_le y z ((- x) ⊕ t) h₁' h₂'
    replace h' : x ⊙ (y ⊔ z) ≤ t := by rw[oMul_comm,oMul_le_le_not_oAdd] ; exact h'
    apply h'
  exact le_antisymm le_h h_le

lemma oAdd_inf_distrib (x y z : A) : (x ⊕ (y ⊓ z)) = (x ⊕ y) ⊓ (x ⊕ z) := by
  rw[not_iff_not']
  rw[not_inf]
  rw[oAdd_dual']
  rw[not_inf]
  rw[oAdd_dual,oAdd_dual]
  rw[neg_neg,neg_neg]
  apply oMul_sup_distrib

lemma le_zero {x : A} (h : x ≤ 0) : x = 0 := by
  suffices this : 0 = x from by apply this.symm
  calc 0
  _ = x ⊙ (- 0) := by rw[le_iff₂.mp h]
  _ = x ⊙ 1 := by simp
  _ = x := by simp

lemma zero_le (x : A) : 0 ≤ x := by
  rw[le_iff₄]
  use x
  simp

lemma one_le {x : A} (h : 1 ≤ x) : x = 1 := by
  rw[not_iff_not']
  rw[not_one]
  apply le_zero
  rw[←not_one]
  apply (not_le _ _).mp h

lemma le_one (x : A) : x ≤ 1 := by
  rw[not_le]
  rw[not_one]
  apply zero_le

instance : BoundedOrder A where
  bot := 0
  bot_le := zero_le
  top := 1
  le_top := le_one

instance : CanonicallyOrderedAdd A where
  exists_add_of_le := by
    intro x y
    rw[le_iff₄]
    intro ⟨z,h⟩
    use z
    apply h.symm
  le_add_self := by
    intro x y
    rw[le_iff₄]
    use y
    apply oAdd_comm
  le_self_add := by
    intro x y
    rw[le_iff₄]
    use y
    rfl

def isMVChain (A : Type*) [MVAlgebra A] : Prop := ∀ (x y : A), x ≤ y ∨ y ≤ x

class MVChain (A : Type*) [MVAlgebra A] where
  isMVChain' : isMVChain A

open Classical in
theorem min_def (x y : A) [MVChain A] : x ⊓ y = if (x ≤ y) then x else y := by
    by_cases x ≤ y
    case pos h₁ =>
      have h' : x ≤ y ↔ True := by
        rw[iff_true]
        exact h₁
      replace h' : (x ≤ y) = True := by rw[h']
      calc x ⊓ y
      _ = x ⊙ (- x ⊕ y) := rfl
      _ = x ⊙ (- ( - - x) ⊙ (- y)) := by simp
      _ = x ⊙ (- (x) ⊙ (- y)) := by simp
      _ = x ⊙ (- 0) := by rw[le_iff₂.mp h₁]
      _ = x ⊙ 1 := by simp
      _ = x := by simp
      _ = if True then x else y := by simp
      _ = if x ≤ y then x else y := by rw[h'] ; simp
    case neg h₂ =>
      have h₂' : (x ≤ y) = False := by
        rw[eq_iff_iff]
        rw[iff_false]
        exact h₂
      have h : y ≤ x := by
        refine Or.by_cases (MVChain.isMVChain' x y) ?h1 ?h2
        case h1 =>
          intro hq
          exfalso
          apply h₂ hq
        case h2 =>
          intro h ; exact h
      calc x ⊓ y
      _ = y ⊓ x := by rw[inf_comm]
      _ = y ⊙ ((- y) ⊕ x) := rfl
      _ = y ⊙ (- ( - - y) ⊙ (- x)) := by simp
      _ = y ⊙ (- (y) ⊙ (- x)) := by simp
      _ = y ⊙ (- 0) := by rw[le_iff₂.mp h]
      _ = y ⊙ 1 := by simp
      _ = y := by simp
      _ = if False then x else y := by simp
      _ = if x ≤ y then x else y := by rw[h₂'] ; simp

/-open Classical in
noncomputable instance [MVChain A] : LinearOrder A where
  le_total := MVChain.isMVChain'
  toDecidableLE := by
    apply Classical.decRel
  compare x y :=
  min_def x y := NaturalOrder.min_def x y
  max_def := by
    intro x y
    calc x ⊔ y
    _ = (- - x) ⊔ (- - y) := by simp
    _ = - ((- x) ⊓ (- y)) := by rw[not_inf]
    _ = - (if - x ≤ - y then - x else - y) := by rw[min_def]
    _ = - (if y ≤ x then - x else - y) := by rw[←not_le]
    _ = if y ≤ x then - - x else - - y := by rw[]-/

end MVOrder
