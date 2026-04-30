import MVAlgebras.Basic

open Basic

/- This file introduces what is called the "Natural Order" on MVAlgebras
 The beginning of the file introduces a notation ≤ without any propreties, then
 equivalent notions are derived. Finally, it is proven to be a partial order
  This proof is from the first chapter of Mundici -/

instance [MVAlgebra A] : LE A where
  le x y := (- x) + y = 1

lemma le_iff₁ [MVAlgebra A] {x y : A} : x ≤ y ↔ (- x) + y = 1 := by
  tauto

lemma le_iff₂ [MVAlgebra A] {x y : A} : x ≤ y ↔ x ⊙ (- y) = 0 := by
  rw[le_iff₁]
  rw[oTimes_neg_add]
  rw[neg_neg]
  rw[Basic.neg_zero]
  apply Iff.intro
  case mp =>
    intro h
    rw[h,neg_neg]
  case mpr =>
    intro h
    rw[←neg_neg (- x + y),h]

lemma le_iff₃ [MVAlgebra A] {x y : A} : x ≤ y ↔ y = x + (y ⊖ x) := by
  apply Iff.intro
  case mp =>
    intro h
    calc y
    _ = (x ⊙ (- y)) + y := by simp[le_iff₂.mp h]
    _ = - (- x + y) + y := by simp
    _ = - (- y + x) + x := by rw[neg_switch]
    _ = x + - (- y + x) := by rw[add_comm]
    _ = x + (y ⊖ x) := by simp
  case mpr =>
    intro h
    apply le_iff₂.mpr
    calc x ⊙ (- y)
    _ = - (- x + y) := by simp
    _ = - (- x + (x + y ⊖ x)) := by rw[←h]
    _ = - (- x + (y + x ⊖ y)) := by rw[add_comm y,minus_add,add_comm x]
    _ = - ((- x + y) + x ⊖ y) := by rw[add_assoc]
    _ = - (- (x ⊖ y) + x ⊖ y) := by simp
    _ = - (1 : A) := by rw[neg_add (x ⊖ y)]
    _ = 0 := by simp

lemma le_iff₄ [MVAlgebra A] {x y : A} : x ≤ y ↔ ∃ (z : A), x + z = y := by
  apply Iff.intro
  case mp =>
    intro h
    use y ⊖ x
    apply (le_iff₃.mp h).symm
  case mpr =>
    intro ⟨z,h⟩
    apply le_iff₁.mpr
    calc -x + y
    _ = - x + (x + z) := by rw[←h]
    _ = (- x + x) + z := by rw[add_assoc]
    _ = 1 + z := by simp
    _ = 1 := by rw[one_add]

instance {A : Type*} [MVAlgebra A] : Preorder A where
  le x y := x ≤ y
  le_refl := by
    intro x
    rw[le_iff₁]
    simp
  le_trans := by
    intro x y z
    rw[le_iff₄,le_iff₄,le_iff₄]
    intro ⟨x',hx⟩ ⟨y',hy⟩
    use x' + y'
    calc x + (x' + y')
    _ = x + x' + y' := by rw[add_assoc]
    _ = y + y' := by rw[hx]
    _ = z := by rw[hy]
