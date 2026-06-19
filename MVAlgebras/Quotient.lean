import MVAlgebras.Defs
import MVAlgebras.Ideal.Defs
import MVAlgebras.Distance
import MVAlgebras.Indipendence

variable {A : Type*} [MVAlgebra A] {I : MVAlgebra_Ideal A}

open MVDist

def dist_in {A : Type*} [MVAlgebra A] (I : MVAlgebra_Ideal A) : A → A → Prop :=
  fun (x y : A) => dist x y ∈ I

instance equivOfDist : Equivalence (fun (x y : A) => dist x y ∈ I) where
  refl := by
    intro x
    unfold dist
    rw[oNeg_def]
    rw[oMul_not_self]
    rw[oAdd_zero]
    apply zero_mem
  symm := by
    intro x y h
    unfold dist at h
    unfold dist
    rw[oAdd_comm]
    apply h
  trans := by
    intro x y z hxy hyz
    suffices this :(dist x y ⊕ dist y z) ∈ I from by
      apply le_mem this
      apply dist_triangle
    apply oAdd_mem hxy hyz

instance setoidOfDist (I : MVAlgebra_Ideal A) : Setoid A where
  r := (fun (x y : A) => dist x y ∈ I)
  iseqv := equivOfDist

instance : Zero (Quotient (setoidOfDist I)) where
  zero := Quotient.mk (setoidOfDist I) (0 : A)

instance : Reduced.MVAlgebra (Quotient (setoidOfDist I)) where
  neg := by
    refine Quotient.lift (fun (x : A) => Quotient.mk (setoidOfDist I) (- x)) ?_
    intro x y h
    rw[Quotient.eq]
    suffices this : dist (- x) (- y) ∈ I from by
      apply this
    rw[←not_dist]
    apply h
  neg_neg := by
    apply Quotient.ind
    intro x
    rw[Quotient.lift_mk]
    rw[Quotient.lift_mk]
    rw[neg_neg]
  oAdd := by
    refine Quotient.lift₂ (fun (x y : A) =>
      Quotient.mk (setoidOfDist I) (x ⊕ y) ) ?_
    intro x y x' y' hx hy
    rw[Quotient.eq]
    suffices this : dist (x ⊕ y) (x' ⊕ y') ∈ I from by apply this
    suffices this : (dist x x' ⊕ dist y y') ∈ I from by
      apply I.le_mem this
      apply oAdd_dist
    apply I.add_mem hx hy
  oAdd_assoc' := by
    apply Quotient.ind₂
    intro x y
    apply Quotient.ind
    intro z
    rw[Quotient.lift₂,Quotient.lift₂,Quotient.lift₂,Quotient.lift₂]
    rw[Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk]
    rw[Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk]
    rw[Quotient.eq]
    rw[oAdd_assoc]
    suffices this : dist (x ⊕ (y ⊕ z)) (x ⊕ (y ⊕ z)) ∈ I from by apply this
    rw[dist_self]
    apply zero_mem
  oAdd_zero' := by
    apply Quotient.ind
    intro x
    unfold OAdd.oAdd
    have hz : 0 = Quotient.mk (setoidOfDist I) (0 : A) := by rfl
    rw[hz]
    rw[Quotient.lift₂]
    rw[Quotient.lift_mk,Quotient.lift_mk]
    rw[Quotient.eq]
    suffices this : dist (x ⊕ 0) x ∈ I from by apply this
    rw[oAdd_zero]
    rw[dist_self]
    apply zero_mem
  oAdd_not_zero' := by
    have hz : 0 = Quotient.mk (setoidOfDist I) (0 : A) := by rfl
    apply Quotient.ind
    intro x
    rw[Quotient.lift₂]
    rw[Quotient.lift_mk]
    rw[hz]
    rw[Quotient.lift_mk]
    rw[Quotient.lift_mk]
    rw[Quotient.eq]
    suffices this : dist (x ⊕ (- 0)) (- 0) ∈ I from by apply this
    rw[oAdd_not_zero]
    rw[dist_self]
    apply zero_mem
  not_switch' := by
    apply Quotient.ind
    intro x
    apply Quotient.ind
    intro y
    rw[Quotient.lift₂,Quotient.lift₂,Quotient.lift₂,Quotient.lift₂]
    rw[Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk]
    rw[Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk]
    rw[Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk,Quotient.lift_mk]
    rw[Quotient.eq]
    suffices this : dist ((-((-x) ⊕ y)) ⊕ y) ((-((-y) ⊕ x)) ⊕ x) ∈ I from by apply this
    rw[not_switch]
    rw[dist_self]
    apply zero_mem

def QuotientMV := fun (A : Type*) [MVAlgebra A] (I : MVAlgebra_Ideal A) =>
  (Quotient (setoidOfDist I))

infix:75 "⧸ " => QuotientMV

instance : MVAlgebra (A ⧸ I) :=
  @Reduced.instMVAlgebraOfMVAlgebra (A ⧸ I) instMVAlgebraQuotientSetoidOfDist


