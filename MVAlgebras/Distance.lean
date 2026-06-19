import MVAlgebras.Defs
import MVAlgebras.NaturalOrder

variable {A : Type*} [MVAlgebra A]

namespace MVDist

def dist {A : Type*} [MVAlgebra A] (x y : A) : A := (x ⊖ y) ⊕ (y ⊖ x)

lemma dist_self {x : A} : dist x x = 0 := by
  unfold dist
  rw[oNeg_def]
  rw[oMul_not_self]
  rw[oAdd_zero]

lemma eq_of_dist_eq_zero {x y : A} : dist x y = 0 → x = y := by
  intro h
  unfold dist at h
  refine le_antisymm ?h1 ?h2
  case h1 =>
    rw[le_iff_exists]
    use (y ⊖ x) ⊕ (y ⊖ x)
    calc x ⊕ ((y ⊖ x) ⊕ (y ⊖ x))
    _ = ((y ⊖ x) ⊕ (y ⊖ x)) ⊕ x := by rw[oAdd_comm]
    _ = (y ⊖ x) ⊕ ((y ⊖ x) ⊕ x) := by rw[oAdd_assoc]
    _ = (y ⊖ x) ⊕ ((x ⊖ y) ⊕ y) := by rw[oNeg_switch]
    _ = ((y ⊖ x) ⊕ (x ⊖ y)) ⊕ y := by rw[oAdd_assoc]
    _ = ((x ⊖ y) ⊕ (y ⊖ x)) ⊕ y := by rw[oAdd_comm (x ⊖ y)]
    _ = 0 ⊕ y := by rw[h]
    _ = y := by rw[zero_oAdd]
  case h2 =>
    rw[le_iff_exists]
    use (x ⊖ y) ⊕ (x ⊖ y)
    calc y ⊕ ((x ⊖ y) ⊕ (x ⊖ y))
    _ = ((x ⊖ y) ⊕ (x ⊖ y)) ⊕ y := by rw[oAdd_comm]
    _ = (x ⊖ y) ⊕ ((x ⊖ y) ⊕ y) := by rw[oAdd_assoc]
    _ = (x ⊖ y) ⊕ ((y ⊖ x) ⊕ x) := by rw[oNeg_switch]
    _ = ((x ⊖ y) ⊕ (y ⊖ x)) ⊕ x := by rw[oAdd_assoc]
    _ = 0 ⊕ x := by rw[h]
    _ = x := by rw[zero_oAdd]

lemma dist_comm (x y : A) : dist x y = dist y x := by
  unfold dist
  rw[oAdd_comm]

lemma dist_triangle (x y z : A) : dist x z ≤ dist x y ⊕ dist y z := by
  have h (x y z : A) : ((- (x ⊖ z)) ⊕ ((x ⊖ y) ⊕ (y ⊖ z))) = 1 := by
    apply MVOrder.one_le
    calc 1
    _ = y ⊕ (- y) := by rw[oAdd_not_self]
    _ = (- y) ⊕ y := by rw[oAdd_comm]
    _ ≤ (-x ⊔ - y) ⊕ y := by apply MVOrder.oAdd_le ; apply le_sup_right
    _ ≤ (-x ⊔ - y) ⊕ (z ⊔ y) := by apply MVOrder.le_oAdd ; apply le_sup_right
    _ = ((-x) ⊖ (-y) ⊕ (-y)) ⊕ ((z ⊖ y) ⊕ y) := by rfl
    _ = ((-x) ⊖ (-y) ⊕ (-y)) ⊕ ((y ⊖ z) ⊕ z) := by rw[oNeg_switch z]
    _ = ((-x) ⊖ (-y) ⊕ (-y)) ⊕ (z ⊕ (y ⊖ z)) := by rw[oAdd_comm z]
    _ = (((-x) ⊖ (-y) ⊕ (-y)) ⊕ z) ⊕ (y ⊖ z) := by rw[oAdd_assoc ((-x) ⊖ (-y) ⊕ (-y))]
    _ = (((-y) ⊖ (-x) ⊕ (-x)) ⊕ z) ⊕ (y ⊖ z) := by rw[oNeg_switch]
    _ = (((-y) ⊖ (-x)) ⊕ ((-x) ⊕ z)) ⊕ (y ⊖ z) := by rw[oAdd_assoc ((-y) ⊖ (-x))]
    _ = (((-y) ⊖ (-x)) ⊕ - ((- - x) ⊙ (- z))) ⊕ (y ⊖ z) := by rw[oAdd_dual (- x)]
    _ = (((-y) ⊖ (-x)) ⊕ - (x ⊙ (- z))) ⊕ (y ⊖ z) := by rw[neg_neg]
    _ = (((-y) ⊖ (-x)) ⊕ - (x ⊖ z)) ⊕ (y ⊖ z) := by rw[←oNeg_def]
    _ = ((- (x ⊖ z)) ⊕ ((-y) ⊖ (-x))) ⊕ (y ⊖ z) := by rw[oAdd_comm (- (x ⊖ z))]
    _ = ((- (x ⊖ z)) ⊕ (- ((- - y) ⊕ (-x)))) ⊕ (y ⊖ z) := by rw[←oNeg_def']
    _ = ((- (x ⊖ z)) ⊕ (- (y ⊕ (-x)))) ⊕ (y ⊖ z) := by rw[neg_neg]
    _ = ((- (x ⊖ z)) ⊕ (- ((- x) ⊕ y))) ⊕ (y ⊖ z) := by rw[oAdd_comm y]
    _ = ((- (x ⊖ z)) ⊕ (- - ((- - x) ⊙ (- y)))) ⊕ (y ⊖ z) := by rw[oAdd_dual (- x)]
    _ = ((- (x ⊖ z)) ⊕ (x ⊙ (- y))) ⊕ (y ⊖ z) := by rw[neg_neg,neg_neg]
    _ = ((- (x ⊖ z)) ⊕ (x ⊖ y)) ⊕ (y ⊖ z) := by rw[←oNeg_def]
    _ = (- (x ⊖ z)) ⊕ ((x ⊖ y) ⊕ (y ⊖ z)) := by rw[oAdd_assoc]
  have h₁ : (x ⊖ z) ≤ ((x ⊖ y) ⊕ (y ⊖ z)) := by
    rw[le_iff_not_oAdd]
    apply h x y z
  have h₂ : (z ⊖ x) ≤ ((y ⊖ x) ⊕ (z ⊖ y)) := by
    rw[le_iff_not_oAdd]
    rw[oAdd_comm (y ⊖ x)]
    apply h
  calc dist x z
  _ ≤ (x ⊖ z) ⊕ (z ⊖ x) := by rfl
  _ ≤ ((x ⊖ y) ⊕ (y ⊖ z)) ⊕ (z ⊖ x) := by apply MVOrder.oAdd_le ; apply h₁
  _ ≤ ((x ⊖ y) ⊕ (y ⊖ z)) ⊕ ((y ⊖ x) ⊕ (z ⊖ y)) := by apply MVOrder.le_oAdd ; apply h₂
  _ = (((x ⊖ y) ⊕ (y ⊖ z)) ⊕ (y ⊖ x)) ⊕ (z ⊖ y) := by rw[oAdd_assoc _ _ (z ⊖ y)]
  _ = ((x ⊖ y) ⊕ ((y ⊖ z) ⊕ (y ⊖ x))) ⊕ (z ⊖ y) := by rw[oAdd_assoc (x ⊖ y)]
  _ = ((x ⊖ y) ⊕ ((y ⊖ x) ⊕ (y ⊖ z))) ⊕ (z ⊖ y) := by rw[oAdd_comm (y ⊖ x)]
  _ = (((x ⊖ y) ⊕ (y ⊖ x)) ⊕ (y ⊖ z)) ⊕ (z ⊖ y) := by rw[←oAdd_assoc (x ⊖ y)]
  _ = ((x ⊖ y) ⊕ (y ⊖ x)) ⊕ ((y ⊖ z) ⊕ (z ⊖ y)) := by rw[oAdd_assoc]

lemma not_dist (x y : A) : dist x y = dist (-x) (-y) := by
  unfold dist
  rw[←not_oNeg_not,←not_oNeg_not]
  rw[oAdd_comm]

lemma oAdd_dist (x y s t : A) : dist (x ⊕ s) (y ⊕ t) ≤ dist x y ⊕ dist s t := by
  have h (x y s t : A) : ((- (x ⊕ s) ⊖ (y ⊕ t) ) ⊕ ((x ⊖ y) ⊕ (s ⊖ t))) =
    (-(x ⊕ s)) ⊕ ((x ⊔ y) ⊕ (t ⊔ s)) := by
    calc ((- (x ⊕ s) ⊖ (y ⊕ t) ) ⊕ ((x ⊖ y) ⊕ (s ⊖ t)))
    _ = ((- (x ⊕ s)) ⊕ (y ⊕ t) ) ⊕ ((x ⊖ y) ⊕ (s ⊖ t)) := by rw[not_oNeg']
    _ = (- (x ⊕ s)) ⊕ ((y ⊕ t)  ⊕ ((x ⊖ y) ⊕ (s ⊖ t))) := by rw[oAdd_assoc]
    _ = (- (x ⊕ s)) ⊕ (((y ⊕ t) ⊕ (x ⊖ y)) ⊕ (s ⊖ t)) := by rw[oAdd_assoc (y ⊕ t)]
    _ = (- (x ⊕ s)) ⊕ ((y ⊕ (t ⊕ (x ⊖ y))) ⊕ (s ⊖ t)) := by rw[oAdd_assoc y]
    _ = (- (x ⊕ s)) ⊕ ((y ⊕ ((x ⊖ y) ⊕ t)) ⊕ (s ⊖ t)) := by rw[oAdd_comm t]
    _ = (- (x ⊕ s)) ⊕ (((y ⊕ (x ⊖ y)) ⊕ t) ⊕ (s ⊖ t)) := by rw[←oAdd_assoc y]
    _ = (- (x ⊕ s)) ⊕ ((y ⊕ (x ⊖ y)) ⊕ (t ⊕ (s ⊖ t))) := by rw[oAdd_assoc]
    _ = (- (x ⊕ s)) ⊕ (((x ⊖ y) ⊕ y) ⊕ ((s ⊖ t) ⊕ t)) := by rw[oAdd_comm y,oAdd_comm t]
    _ = (- (x ⊕ s)) ⊕ ((x ⊔ y) ⊕ (s ⊔ t)) := rfl
    _ = (- (x ⊕ s)) ⊕ ((x ⊔ y) ⊕ (t ⊔ s)) := by rw[sup_comm s]
  have h (x y s t : A) : ((- (x ⊕ s) ⊖ (y ⊕ t) ) ⊕ ((x ⊖ y) ⊕ (s ⊖ t))) = 1 := by
    rw[h]
    apply MVOrder.one_le
    calc 1
    _ = (x ⊕ s) ⊕ (- (x ⊕ s)) := by rw[oAdd_not_self]
    _ = (- (x ⊕ s)) ⊕ (x ⊕ s) := by rw[oAdd_comm]
    _ ≤ (-(x ⊕ s)) ⊕ (x ⊕ (t ⊔ s)) := by
      apply MVOrder.le_oAdd
      apply MVOrder.le_oAdd
      apply le_sup_right
    _ ≤ (-(x ⊕ s)) ⊕ ((x ⊔ y) ⊕ (t ⊔ s)) := by
      apply MVOrder.le_oAdd
      apply MVOrder.oAdd_le
      apply le_sup_left
  replace h (x y s t : A) : (x ⊕ s) ⊖ (y ⊕ t) ≤ (x ⊖ y) ⊕ (s ⊖ t) := by
    rw[le_iff_not_oAdd]
    apply h
  replace h :
    ((x + s) ⊖ (y + t)) + ((y ⊕ t) ⊖ (x ⊕ s)) ≤ x ⊖ y ⊕ y ⊖ x ⊕ (s ⊖ t ⊕ t ⊖ s) := by
    calc (x ⊕ s) ⊖ (y ⊕ t) ⊕ (y ⊕ t) ⊖ (x ⊕ s)
    _ ≤ (x ⊖ y) ⊕ (s ⊖ t) ⊕ (y ⊕ t) ⊖ (x ⊕ s) := by
      apply MVOrder.oAdd_le ; apply h
    _ = (x ⊖ y) ⊕ (s ⊖ t) ⊕ ((y ⊕ t) ⊖ (x ⊕ s)) := by rw[oAdd_assoc]
    _ ≤ (x ⊖ y) ⊕ (s ⊖ t) ⊕ ((y ⊖ x) ⊕ (t ⊖ s)) := by
      apply MVOrder.le_oAdd ; apply h
    _ = (x ⊖ y) ⊕ ((s ⊖ t) ⊕ ((y ⊖ x) ⊕ (t ⊖ s))) := by rw[oAdd_assoc]
    _ = (x ⊖ y) ⊕ (((s ⊖ t) ⊕ (y ⊖ x)) ⊕ (t ⊖ s)) := by rw[oAdd_assoc]
    _ = (x ⊖ y) ⊕ (((y ⊖ x) ⊕ (s ⊖ t)) ⊕ (t ⊖ s)) := by rw[oAdd_comm (y ⊖ x)]
    _ = (x ⊖ y) ⊕ ((y ⊖ x) ⊕ ((s ⊖ t) ⊕ (t ⊖ s))) := by rw[oAdd_assoc]
    _ = x ⊖ y ⊕ y ⊖ x ⊕ (s ⊖ t ⊕ t ⊖ s) := by rw[oAdd_assoc]
  unfold dist
  apply h

end MVDist
