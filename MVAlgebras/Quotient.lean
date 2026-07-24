import MVAlgebras.Defs
import MVAlgebras.MVAlgebraHom
import MVAlgebras.Ideal.Defs
import MVAlgebras.Ideal.Basic
import MVAlgebras.Distance
import MVAlgebras.Indipendence
import Mathlib.Algebra.Quotient

variable {A : Type*} [MVAlgebra A] {I : MVAlgebra_Ideal A}

open MVDist

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
    repeat rw[Quotient.lift_mk]
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
    repeat rw[Quotient.lift₂]
    repeat rw[Quotient.lift_mk]
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
    repeat rw[Quotient.lift_mk]
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
    rw[hz]
    repeat rw[Quotient.lift_mk]
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
    repeat rw[Quotient.lift₂]
    repeat rw[Quotient.lift_mk]
    rw[Quotient.eq]
    suffices this : dist ((-((-x) ⊕ y)) ⊕ y) ((-((-y) ⊕ x)) ⊕ x) ∈ I from by apply this
    rw[not_switch]
    rw[dist_self]
    apply zero_mem

def QuotientMV := fun (A : Type*) [MVAlgebra A] (I : MVAlgebra_Ideal A) =>
  (Quotient (setoidOfDist I))

namespace QuotientMV

instance (A : Type*) [MVAlgebra A] : HasQuotient A (MVAlgebra_Ideal A) where
  Quotient I := QuotientMV A I

instance : MVAlgebra (A ⧸ I) :=
  @Reduced.instMVAlgebraOfMVAlgebra (A ⧸ I) instMVAlgebraQuotientSetoidOfDist

@[implicit_reducible]
def mk' (I : MVAlgebra_Ideal A) : A →⊕ (A ⧸ I) where
  toFun x := Quotient.mk (setoidOfDist I) x
  map_zero' := rfl
  map_not := by
    intro _ ; rfl
  map_add' := by
    intro _ _ ; rfl

theorem ker_quot_self : ker (mk' I) = I := by
  ext x
  calc x ∈ ker (mk' I)
  _ ↔ mk' I x ∈ ⊥ := by rw[mem_comap]
  _ ↔ mk' I x = 0 := by rw[MVIdeal.mem_bot_iff_zero]
  _ ↔ Quotient.mk (setoidOfDist I) x = Quotient.mk (setoidOfDist I) 0 := by rfl
  _ ↔ dist x 0 ∈ I := by rw[Quotient.eq] ; unfold setoidOfDist ; rfl
  _ ↔ ((x ⊖ 0) ⊕ (0 ⊖ x)) ∈ I := by rfl
  _ ↔ ((x ⊙ (- 0)) ⊕ (0 ⊙ (- x))) ∈ I := by rw[oNeg_def,oNeg_def]
  _ ↔ ((x ⊙ 1) ⊕ (0 ⊙ (- x))) ∈ I := by rw[not_zero]
  _ ↔ (x ⊕ 0) ∈ I := by rw[oMul_one,zero_oMul]
  _ ↔ x ∈ I := by rw [oAdd_zero]

@[implicit_reducible]
def lift {A B : Type*} [MVAlgebra A] [MVAlgebra B]
  {I : MVAlgebra_Ideal A} (f : A →⊕ B) (h : I ≤ ker f) : (A ⧸ I) →⊕ B where
  toFun := by
    refine Quotient.lift f ?_
    intro x y h'
    apply eq_of_dist_eq_zero
    replace h' : dist x y ∈ I := by apply h'
    replace h' : dist x y ∈ ker f := h h'
    rw[mem_comap] at h'
    rw[MVIdeal.mem_bot_iff_zero] at h'
    rw[map_dist] at h'
    apply h'
  map_zero' := by
    have hz : ⟦(0 : A)⟧ = (0 : A ⧸ I) := by rfl
    rw[←hz]
    rw[Quotient.lift_mk]
    apply map_zero
  map_not := by
    apply Quotient.ind
    intro x
    calc - Quotient.lift f _ ⟦x⟧
    _ = - f x := by rw[Quotient.lift_mk]
    _ = f (- x) := by rw[map_not]
    _ = Quotient.lift f _ (- ⟦x⟧) := by rw[←Quotient.lift_mk f _ (- x)] ; rfl
  map_add' := by
    apply Quotient.ind
    intro x
    apply Quotient.ind
    intro y
    calc Quotient.lift f _ (⟦x⟧ ⊕ ⟦y⟧)
    _ = Quotient.lift f _ ⟦x ⊕ y⟧ := by rfl
    _ = f (x ⊕ y) := rfl
    _ = f x ⊕ f y := by rw[map_oAdd]
    _ = Quotient.lift f _ ⟦x⟧ ⊕ Quotient.lift f _ ⟦y⟧ := rfl

theorem lift_mk {A B : Type*} [MVAlgebra A] [MVAlgebra B] {f : A →⊕ B}
  {I : MVAlgebra_Ideal A} {h : I ≤ ker f} {x : A}
  : lift f h ⟦x⟧ = f x := by
    calc lift f h ⟦x⟧
    _ = ⇑(lift f h) ⟦x⟧ := by rfl

theorem eq {A : Type*} [MVAlgebra A] {I : MVAlgebra_Ideal A} {x y : A} :
    (⟦x⟧ : A ⧸ I) = ⟦y⟧ ↔ dist x y ∈ I := by
    rw[Quotient.eq_iff_equiv]
    rfl

@[implicit_reducible]
def quot_ker {A B : Type*} [MVAlgebra A] [MVAlgebra B] (f : A →⊕ B) :
  (A ⧸ ker f) →⊕ B := QuotientMV.lift f (le_refl _)

theorem quot_ker_injective {A B : Type*} [MVAlgebra A] [MVAlgebra B] (f : A →⊕ B)
  : Function.Injective (quot_ker f) := by
    apply Quotient.ind
    intro x
    apply Quotient.ind
    intro y h
    unfold quot_ker at h
    rw[lift_mk,lift_mk] at h
    suffices this :(setoidOfDist (ker f)) x y from by
      rw[←Quotient.eq] at this
      apply this
    suffices this : dist x y ∈ ker f from by
      apply this
    rw[mem_comap]
    rw[MVIdeal.mem_bot_iff_zero]
    rw[map_dist]
    rw[←h]
    apply MVDist.dist_self

theorem quot_ker_bijective {A B : Type*} [MVAlgebra A] [MVAlgebra B]
  (g : A →⊕ B) {hg : Function.Surjective g} : Function.Bijective (quot_ker g) := by
    apply And.intro
    case left =>
      apply quot_ker_injective
    case right =>
      intro x
      have ⟨x',hx'⟩ := hg x
      use ⟦x'⟧
      calc (quot_ker g) ⟦x'⟧
      _ = QuotientMV.lift g (le_refl _) ⟦x'⟧ := rfl
      _ = g x' := by rw[QuotientMV.lift_mk]
      _ = x := by rw[hx']

@[reducible]
noncomputable def quot_ker_eq {A B : Type*} [MVAlgebra A] [MVAlgebra B]
  (g : A →⊕ B) {hg : Function.Surjective g} : (A ⧸ (ker g)) ≃⊕ B where
  toMVAlgebraHom := QuotientMV.quot_ker g
  invFun (x : B) := ⟦Function.surjInv hg x⟧
  left_inv := by
    apply Quotient.ind
    intro x
    calc ⟦Function.surjInv hg ((QuotientMV.lift g _) ⟦x⟧)⟧
    _ = ⟦(Function.surjInv hg) (g x)⟧ := by rw[QuotientMV.lift_mk]
    _ = ⟦x⟧ := by
      rw[Quotient.eq]
      suffices this : dist ((Function.surjInv hg) (g x)) x ∈ ker g from by
        apply this
      rw[mem_comap]
      rw[MVIdeal.mem_bot_iff_zero]
      rw[map_dist]
      calc dist (g ((Function.surjInv hg) (g x))) (g x)
      _ = dist ((g ∘ (Function.surjInv hg)) (g x)) (g x) := rfl
      _ = dist (g x) (g x) := by rw[Function.comp_surjInv] ; rfl
      _ = 0 := by rw[dist_self]
  right_inv := by
    intro x
    calc (QuotientMV.lift g _) ⟦Function.surjInv hg x⟧
    _ = g (Function.surjInv hg x) := by rw[QuotientMV.lift_mk]
    _ = (g ∘ (Function.surjInv hg)) x := rfl
    _ = x := by rw[Function.comp_surjInv] ; rfl

theorem second_iso_theorem {A B C : Type*} [MVAlgebra A] [MVAlgebra B] [MVAlgebra C]
  (f : A →⊕ B) (g : A →⊕ C) (hf : Function.Surjective f) (hg : Function.Surjective g)
  : (ker f ≤ ker g) ↔ (∃ (k : B →⊕ C), Function.Surjective k ∧ MVHom.comp k f = g) := by
    apply Iff.intro
    case mp =>
      intro hker
      let k : B →⊕ C := {
        toFun := g ∘ (Function.surjInv hf)
        map_zero' := by
          rw[←MVIdeal.mem_bot_iff_zero]
          rw[Function.comp_apply]
          rw[←mem_comap]
          apply hker
          rw[SetLike.mem_coe]
          rw[mem_comap]
          rw[MVIdeal.mem_bot_iff_zero]
          rw[Function.surjInv_eq hf]
        map_add' := by
          intro x y
          refine le_antisymm ?h1 ?h2
          case h1 =>
            rw[le_iff_oNeg]
            calc g (Function.surjInv hf (x ⊕ y)) ⊖
              (g (Function.surjInv hf x) ⊕ g (Function.surjInv hf y))
            _ = g ((Function.surjInv hf (x ⊕ y)) ⊖
              ((Function.surjInv hf x) ⊕ (Function.surjInv hf y))) := by rw[←map_oAdd,map_oNeg]
            _ = 0  := by
              rw[←MVIdeal.mem_bot_iff_zero]
              rw[←mem_comap]
              apply hker
              rw[SetLike.mem_coe]
              rw[mem_comap]
              rw[map_oNeg,map_oAdd]
              repeat rw[Function.surjInv_eq hf]
              rw[oNeg_self]
              rw[MVIdeal.mem_bot_iff_zero]
          case h2 =>
            rw[le_iff_oNeg]
            calc (g (Function.surjInv hf x) ⊕ g (Function.surjInv hf y)) ⊖
              (g (Function.surjInv hf (x ⊕ y)))
            _ = g (((Function.surjInv hf x) ⊕ (Function.surjInv hf y)) ⊖
              (Function.surjInv hf (x ⊕ y))) := by rw[←map_oAdd,←map_oNeg]
            _ = 0 := by
              rw[←MVIdeal.mem_bot_iff_zero]
              rw[←mem_comap]
              apply hker
              rw[SetLike.mem_coe]
              rw[mem_comap]
              rw[map_oNeg,map_oAdd]
              repeat rw[Function.surjInv_eq hf]
              rw[oNeg_self]
              rw[MVIdeal.mem_bot_iff_zero]
        map_not := by
          intro x
          refine le_antisymm ?h1 ?h2
          case h1 =>
            repeat rw[Function.comp_apply]
            rw[le_iff_oNeg]
            rw[map_not]
            rw[←map_oNeg]
            rw[←MVIdeal.mem_bot_iff_zero]
            rw[←mem_comap]
            apply hker
            rw[SetLike.mem_coe]
            rw[mem_comap]
            rw[map_oNeg]
            rw[←map_not]
            repeat rw[Function.surjInv_eq hf]
            rw[oNeg_self]
            rw[MVIdeal.mem_bot_iff_zero]
          case h2 =>
            repeat rw[Function.comp_apply]
            rw[le_iff_oNeg]
            rw[map_not]
            rw[←map_oNeg]
            rw[←MVIdeal.mem_bot_iff_zero]
            rw[←mem_comap]
            apply hker
            rw[SetLike.mem_coe]
            rw[mem_comap]
            rw[map_oNeg]
            rw[←map_not]
            repeat rw[Function.surjInv_eq hf]
            rw[oNeg_self]
            rw[MVIdeal.mem_bot_iff_zero]
      }
      use k
      apply And.intro
      case right =>
        ext x
        refine le_antisymm ?h1 ?h2
        case h1 =>
          rw[le_iff_oNeg]
          suffices this : (g (Function.surjInv hf (f x))) ⊖ (g x) = 0 from by
            apply this
          rw[←map_oNeg]
          rw[←MVIdeal.mem_bot_iff_zero]
          rw[←mem_comap]
          apply hker
          rw[SetLike.mem_coe]
          rw[mem_comap]
          rw[map_oNeg]
          rw[Function.surjInv_eq hf]
          rw[oNeg_self]
          rw[MVIdeal.mem_bot_iff_zero]
        case h2 =>
          rw[le_iff_oNeg]
          suffices this : (g x) ⊖ (g (Function.surjInv hf (f x))) = 0 from by
            apply this
          rw[←map_oNeg]
          rw[←MVIdeal.mem_bot_iff_zero]
          rw[←mem_comap]
          apply hker
          rw[SetLike.mem_coe]
          rw[mem_comap]
          rw[map_oNeg]
          rw[Function.surjInv_eq hf]
          rw[oNeg_self]
          rw[MVIdeal.mem_bot_iff_zero]
      case left =>
        intro x
        have ⟨x',hx'⟩ := hg x
        use f x'
        suffices this :
          g (Function.surjInv hf (f x')) = x from by
          apply this
        rw[←hx']
        refine le_antisymm ?h1 ?h2
        case h1 =>
          rw[le_iff_oNeg]
          rw[←MVIdeal.mem_bot_iff_zero]
          rw[←map_oNeg]
          rw[←mem_comap]
          apply hker
          rw[SetLike.mem_coe]
          rw[mem_comap]
          rw[map_oNeg]
          rw[MVIdeal.mem_bot_iff_zero]
          rw[Function.surjInv_eq hf]
          rw[oNeg_self]
        case h2 =>
          rw[le_iff_oNeg]
          rw[←MVIdeal.mem_bot_iff_zero]
          rw[←map_oNeg]
          rw[←mem_comap]
          apply hker
          rw[SetLike.mem_coe]
          rw[mem_comap]
          rw[map_oNeg]
          rw[MVIdeal.mem_bot_iff_zero]
          rw[Function.surjInv_eq hf]
          rw[oNeg_self]
    case mpr =>
      intro ⟨k,hs,hc⟩ x h
      rw[SetLike.mem_coe]
      rw[mem_comap]
      rw[SetLike.mem_coe] at h
      rw[mem_comap] at h
      rw[MVIdeal.mem_bot_iff_zero]
      rw[MVIdeal.mem_bot_iff_zero] at h
      rw[←hc]
      suffices this : k (f x) = 0 from by
        apply this
      rw[h]
      rw[map_zero]







end QuotientMV
