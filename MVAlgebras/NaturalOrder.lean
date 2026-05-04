import MVAlgebras.Basic

/- This file introduces what is called the "Natural Order" on MVAlgebras
  The beginning of the file introduces a notation ≤ without any propreties, then
  equivalent notions are derived. Finally, it is proven to be a partial order
  This proof is from the first chapter of Mundici -/

variable {A : Type*} [MVAlgebra A]

instance : LE A where
  le x y := (- x) + y = 1

lemma le_iff₁ {x y : A} : x ≤ y ↔ (- x) + y = 1 := by
  tauto

lemma le_iff₂ {x y : A} : x ≤ y ↔ x ⊙ (- y) = 0 := by
  calc x ≤ y
  _ ↔ (- x) + y = 1 := by rw[le_iff₁]
  _ ↔ - (x ⊙ (- y)) = 1 := by rw[oTimes_dual',neg_neg y]
  _ ↔ - (x ⊙ (- y)) = - 0 := by rw[neg_zero']
  _ ↔ x ⊙ (-y) = 0 := by rw[←neg_iff_neg]

lemma le_iff₃ {x y : A} : x ≤ y ↔ y = x + (y ⊖ x) := by
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
    _ = - (1 : A) := by rw[add_canc (x ⊖ y)]
    _ = 0 := by simp

lemma le_iff₄ {x y : A} : x ≤ y ↔ ∃ (z : A), x + z = y := by
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
    use x' + y'
    calc x + (x' + y')
    _ = x + x' + y' := by rw[add_assoc]
    _ = y + y' := by rw[hx]
    _ = z := by rw[hy]
  le_antisymm := by
    intro x y h₁ h₂
    replace h₁ : x ⊙ (- y) = 0 := le_iff₂.mp h₁
    replace h₂ : x = y + (x ⊖ y) := le_iff₃.mp h₂
    calc x
    _ = y + (x ⊖ y) := h₂
    _ = y + (x ⊙ (- y)) := by rw[oNeg_def]
    _ = y := by rw[h₁,add_zero]

lemma neg_iff (a : A) (x : A) : a + x = 1 ∧ a ⊙ x = 0 ↔ -a = x := by
  apply Iff.intro
  case mp =>
    intro ⟨h₁,h₂⟩
    replace h₁ : - - a + x = 1 := by
      rw[neg_neg]
      exact h₁
    replace h₁ : -a ≤ x := le_iff₁.mpr h₁
    have h₂ : x ⊙ (- - a) = 0 := by
      rw[neg_neg]
      rw[oTimes_comm]
      exact h₂
    replace h₂ : x ≤ -a := le_iff₂.mpr h₂
    exact le_antisymm h₁ h₂
  case mpr =>
    intro h
    subst_eqs
    exact ⟨add_canc' a,oTimes_canc a⟩

theorem neg_le' (x y : A) : x ≤ y ↔ - y ≤ - x := by
  calc x ≤ y
  _ ↔ -x + y = 1 := by rw[le_iff₁]
  _ ↔ - (x ⊙ (- y)) = 1 := by rw[add_dual,neg_neg]
  _ ↔ x ⊙ (- y) = 0 := by rw[neg_eq_iff_eq_neg,neg_one]
  _ ↔ (- y) ⊙ (- - x) = 0 := by rw[oTimes_comm,neg_neg]
  _ ↔ - y ≤ - x := by rw[le_iff₂]

theorem add_le' (x y z : A) (h : x ≤ y) : x + z ≤ y + z := by
  apply le_iff₄.mpr
  replace ⟨w,h⟩ := le_iff₄.mp h
  use w
  calc x + z + w
  _ = (x + w) + z := by rw[add_right_comm]
  _ = y + z := by rw[h]

theorem oTimes_le (x y z : A) (h : x ≤ y) : x ⊙ z ≤ y ⊙ z := by
  suffices this : - (y ⊙ z) ≤ - (x ⊙ z) from by apply (neg_le' _ _).mpr ; exact this
  suffices this : - y + - z ≤ - x + - z from by rw[oTimes_dual',oTimes_dual'] ; exact this
  suffices this : -y ≤ - x from add_le' _ _ _ this
  exact (neg_le' _ _).mp h

theorem sup_le' (x y z : A) (hx : x ≤ z) (hy : y ≤ z) : (x ⊖ y) + y ≤ z := by
  replace hx := le_iff₁.mp hx
  replace hy := le_iff₃.mp hy
  apply le_iff₁.mpr
  calc -(x ⊖ y + y) + z
    _ = -((- - (x ⊖ y)) + y) + z := by rw[neg_neg]
    _ = ((- (x ⊖ y)) ⊖ y) + z := by rw[oNeg_def' (- (x ⊖ y))]
    _ = ((- (x ⊖ y)) ⊖ y) + (y + (z ⊖ y)) := by nth_rewrite 1 [hy] ; tauto
    _ = ((- (x ⊖ y)) ⊖ y) + y + (z ⊖ y) := by rw[add_assoc]
    _ = (y ⊖ (- (x ⊖ y))) + (- (x ⊖ y)) + (z ⊖ y) := by rw[neg_switch']
    _ = (y ⊖ (- (x ⊖ y))) + (- x + y) + (z ⊖ y) := by nth_rewrite 3 [oNeg_def'] ; rw[neg_neg]
    _ = (y ⊖ (- (x ⊖ y))) + (- x) + (y + (z ⊖ y)) := by rw[add_assoc,add_assoc,add_assoc]
    _ = (y ⊖ (- (x ⊖ y))) + (- x) + z := by nth_rewrite 1 [←hy] ; tauto
    _ = (y ⊖ (- (x ⊖ y))) + 1 := by rw[add_assoc,hx]
    _ = 1 := by rw[add_one]

lemma neg_sup' (y z : A) : (-y) ⊖ (-z) + (- z) = -(y ⊙ (-y + z)) := by
    calc (-y) ⊖ (-z) + (- z)
    _ = (-z) ⊖ (-y) + (-y) := by rw[neg_switch']
    _ = (-z) ⊙ (- - y) + (- y) := by rw[oNeg_def]
    _ = - (z + - y) + -y := by rw[oTimes_dual,neg_neg,neg_neg]
    _ = -y + - (- y + z) := by rw[add_comm z,add_comm]
    _ = -(y ⊙ (-y + z)) := by rw[oTimes_dual,neg_neg]

instance : Lattice A where
  sup x y := (x ⊖ y) + y
  inf x y := x ⊙ (- x + y)
  le_sup_left := by
    intro x y
    suffices this : x ≤  - ((-x) + y) + y from by rw[oNeg_def'] ; exact this
    suffices this : x ≤  - ((-y) + x) + x from by rw[neg_switch] ; exact this
    apply le_iff₄.mpr
    use (- (- y + x))
    exact add_comm x _
  le_sup_right := by
    intro x y
    apply le_iff₄.mpr
    use x ⊖ y
    exact add_comm _ _
  sup_le := sup_le'
  le_inf := by
    intro x y z hy hz
    suffices this : - (y ⊙ (-y + z)) ≤ -x from by rw[neg_le'] ; exact this
    replace hy : -y ≤ - x := (neg_le' _ _).mp hy
    replace hz : -z ≤ - x := (neg_le' _ _).mp hz
    suffices this : (-y) ⊖ (-z) + (- z) ≤ - x from by rw[←neg_sup'] ; exact this
    exact sup_le' _ _ _ hy hz
  inf_le_left := by
    intro x y
    suffices h : -( - x + - (-x + y)) ≤ x from by rw[oTimes_dual] ; exact h
    suffices h : - x ≤ - x + - (-x + y) from by rw[neg_le',neg_neg] ; exact h
    rw[le_iff₄]
    use -(-x + y)
  inf_le_right := by
    intro x y
    suffices h : - y ≤ - (x ⊙ (-x + y)) from by rw[neg_le'] ; exact h
    suffices h : - y ≤ (-x) ⊖ (-y) + (- y) from by rw[←neg_sup'] ; exact h
    suffices h : - y ≤ - y + (-x) ⊖ (-y) from by rw[add_comm] ; exact h
    rw[le_iff₄]
    use (-x)⊖(-y)
