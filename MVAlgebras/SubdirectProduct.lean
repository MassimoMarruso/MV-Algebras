import MVAlgebras.Defs
import MVAlgebras.Quotient
import MVAlgebras.Prod
import MVAlgebras.MVAlgebraHom
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Order.BoundedOrder.Basic

variable {A' : Type*} {ι : Type*} {A : ι → Type*} [MVAlgebra A']
  [(i : ι) → MVAlgebra (A i)]

def isSubdirectProd (A' : Type*) {ι : Type*} (A : ι → Type*) [MVAlgebra A']
  [(i : ι) → MVAlgebra (A i)] : Prop := ∃ (f : A' →⊕ (∀ (i : ι), A i)),
    Function.Injective f ∧ ∀ (i : ι), Function.Surjective (MVHom.comp (proj i) f)

open MVHom

theorem subdirect_rapresentation : isSubdirectProd A' A ↔ ∃ (J : ι → MVAlgebra_Ideal A'),
  ∃ (ε : (i : ι) → (A i ≃⊕ (A' ⧸ (J i)))), (⨅ (i : ι), J i = ⊥) := by
  apply Iff.intro
  case mpr =>
    intro ⟨J,ε,hJ⟩
    let f : A' →⊕ ∀ (i : ι), A i := {
      toFun x i := (MVEquiv.symm (ε i)).toEquiv ⟦x⟧
      map_zero' := by
        ext i
        calc (ε i).symm.toEquiv ⟦0⟧
        _ = (ε i).symm.toEquiv (0 : A' ⧸ J i) := by rfl
        _ = (MVEquiv.symm (ε i)).toMVAlgebraHom 0 := rfl
        _ = 0 := by rw[map_zero]
      map_add' := by
        intro x y
        ext i
        calc (ε i).symm.toEquiv ⟦x + y⟧
        _ = (ε i).symm.toEquiv (⟦x⟧ ⊕ ⟦y⟧) := by rfl
        _ = (MVEquiv.symm (ε i)).toMVAlgebraHom (⟦x⟧ ⊕ ⟦y⟧) := rfl
        _ = (MVEquiv.symm (ε i)).toMVAlgebraHom ⟦x⟧ ⊕ (MVEquiv.symm (ε i)).toMVAlgebraHom ⟦y⟧
          := by rw[map_oAdd]
      map_not := by
        intro x
        ext i
        calc - ((MVEquiv.symm (ε i)).toMVAlgebraHom ⟦x⟧)
        _ = (MVEquiv.symm (ε i)).toMVAlgebraHom ⟦- x⟧ := by rw[map_not] ; rfl
    }
    use f
    apply And.intro
    case left =>
      rw[ker_bot_iff_injective]
      rw[←le_bot_iff]
      intro x h
      rw[SetLike.mem_coe]
      rw[SetLike.mem_coe] at h
      rw[mem_comap] at h
      rw[MVIdeal.mem_bot_iff_zero] at h
      unfold f at h
      rw[←hJ]
      intro I' ⟨I,hI,hI'⟩
      rw[←hI']
      rw[SetLike.mem_coe]
      have ⟨i,hI⟩ := hI
      rw[←hI]
      replace h : (fun (i : ι) => (ε i).symm.toEquiv ⟦x⟧) = 0 := by
        apply h
      replace h : (ε i).symm.toEquiv ⟦x⟧ = 0 := by
        calc (ε i).symm.toEquiv ⟦x⟧
        _ = (fun (i : ι) => (ε i).symm.toEquiv ⟦x⟧) i := rfl
        _ = (0 : ∀ (i : ι), A i) i := by rw[h]
        _ = 0 := rfl
      rw[←MVIdeal.mem_bot_iff_zero] at h
      replace h :
        ⟦x⟧ ∈ ker (MVEquiv.symm (ε i)).toMVAlgebraHom := by apply h
      have h' : ker (MVEquiv.symm (ε i)).toMVAlgebraHom = ⊥ := by
        rw[←ker_bot_iff_injective]
        apply Equiv.injective
      rw[h'] at h
      replace h : (⟦x⟧ : A' ⧸ J i) = (0 : (A' ⧸ J i)) :=
         MVIdeal.mem_bot_iff_zero.mp h
      replace h : (⟦x⟧ : A' ⧸ J i) = (⟦0⟧ : (A' ⧸ J i)) := by
        rw[h]
        rfl
      replace h : dist x 0 ∈ J i := Quotient.eq.mp h
      rw[MVDist.dist_zero] at h
      apply h
    case right =>
      intro i
      unfold f
      suffices this : Function.Surjective (fun (x : A') =>  (ε i).symm.toEquiv ⟦x⟧)
        from by apply this
      apply Function.Surjective.comp
      case hg =>
        intro x
        use (ε i).toEquiv x
        calc (ε i).toEquiv.symm ((ε i).toEquiv x)
        _ = (ε i).toEquiv.symm ((ε i).toEquiv.symm.symm x) := by rw[Equiv.symm_symm]
        _ = x := by rw[Equiv.apply_symm_apply (ε i).toEquiv.symm]
      case hf =>
        apply Quotient.ind
        intro x
        use x
  case mp =>
    intro ⟨f,hi,hs⟩
    let J (i : ι) : MVAlgebra_Ideal A' := ker (MVHom.comp (proj i) f)
    use J
    let ε₁ (i : ι) : (A' ⧸ J i) →⊕ (A i) := by
      refine QuotientMV.lift (MVHom.comp (proj i) f) ?_
      rfl
    let ε₂' (i : ι) : A i → A' := Function.surjInv (hs i)
    let ε₂ (i : ι) : A i → A' ⧸ J i := (Quotient.mk'') ∘ (ε₂' i)
    let ε (i : ι) : (A' ⧸ J i) ≃⊕ (A i) := {
        toMVAlgebraHom := ε₁ i
        invFun := ε₂ i
        left_inv := by
          apply Quotient.ind
          intro x
          have h : (ε₂ i) ((ε₁ i).toAddMonoidHom.toFun ⟦x⟧) =
            ⟦Function.surjInv (hs i) (((MVHom.comp (proj i) f) x))⟧ := by
            calc (ε₂ i) ((ε₁ i) ⟦x⟧)
            _ = (ε₂ i) ((MVHom.comp (proj i) f) x) := by rfl
            _ = (ε₂ i) ((proj i) (f x)) := by rfl
            _ = (Quotient.mk'') ((ε₂' i) ((proj i) (f x))) := by rfl
            _ = ⟦(ε₂' i) ((proj i) (f x))⟧ := by rfl
            _ = ⟦Function.surjInv (hs i) ((proj i) (f x))⟧ := by rfl
            _ = ⟦Function.surjInv (hs i) (((MVHom.comp (proj i) f) x))⟧ := by rfl
          rw[h]
          apply Quotient.eq_iff_equiv.mpr
          suffices this : dist (Function.surjInv (hs i) (((MVHom.comp (proj i) f) x))) x
               ∈ J i from by
            apply this
          unfold J
          unfold ker
          rw[mem_comap]
          rw[MVIdeal.mem_bot_iff_zero]
          calc (MVHom.comp (proj i) f) (dist
            (Function.surjInv (hs i) (((MVHom.comp (proj i) f) x))) x)
          _ = dist ((MVHom.comp (proj i) f)
            (Function.surjInv (hs i) (((MVHom.comp (proj i) f) x))))
            ((MVHom.comp (proj i) f) x)
            := by rw[map_dist]
          _ = dist (((MVHom.comp (proj i) f) x)) ((MVHom.comp (proj i) f) x)
            := by rw[Function.surjInv_eq (hs i)]
          _ = 0 := by rw[MVDist.dist_self]
        right_inv := by
          intro x
          calc (ε₁ i) ((ε₂ i) x)
          _ = ε₁ i ((Quotient.mk'' ∘ Function.surjInv (hs i)) x) := rfl
          _ = QuotientMV.lift (MVHom.comp (proj i) f) _
            ((Quotient.mk'' ∘ Function.surjInv (hs i)) x) := rfl
          _ = QuotientMV.lift (MVHom.comp (proj i) f) _
            ⟦(Function.surjInv (hs i)) x⟧ := by rfl
          _ = (MVHom.comp (proj i) f) ((Function.surjInv (hs i)) x) :=
            by rw[QuotientMV.lift_mk]
          _ = x := by rw[Function.surjInv_eq (hs i)]
      }
    use fun (i : ι) => MVEquiv.symm (ε i)
    rw[←le_bot_iff]
    intro x h
    rw[SetLike.mem_coe] at h
    rw[SetLike.mem_coe]
    have hz : ker f = ⊥ := (ker_bot_iff_injective f).mp hi
    rw[←hz]
    rw[mem_comap]
    rw[MVIdeal.mem_bot_iff_zero]
    ext i
    replace h : x ∈ J i := by
      apply h
      use (J i)
      apply And.intro
      case right => rfl
      case left => use i
    unfold J at h
    replace h : (MVHom.comp (proj i) f) x = 0 := by
      rw[←MVIdeal.mem_bot_iff_zero]
      apply h
    apply h
