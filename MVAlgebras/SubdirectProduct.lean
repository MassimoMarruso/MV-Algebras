import MVAlgebras.Defs
import MVAlgebras.Quotient
import MVAlgebras.Prod
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Order.BoundedOrder.Basic

variable {A' : Type*} {ι : Type*} {A : ι → Type*} [MVAlgebra A']
  [(i : ι) → MVAlgebra (A i)]

def isSubdirectProd (A' : Type*) {ι : Type*} (A : ι → Type*) [MVAlgebra A']
  [(i : ι) → MVAlgebra (A i)] : Prop := ∃ (f : A' →⊕ (∀ (i : ι), A i)),
    Function.Injective f ∧ ∀ (i : ι), Function.Surjective (fun (x : A') => (f x) i)

theorem subdirect_rapresentation : isSubdirectProd A' A ↔ ∃ (J : ι → MVAlgebra_Ideal A'),
  (∃ (ε : (i : ι) → (A i →⊕ (A' ⧸ (J i)))), ∀ (i : ι), Function.Bijective (ε i))
    ∧ (⨅ (i : ι), J i = ⊥) := by
  apply Iff.intro
  case mpr =>
    intro ⟨J,ε,hJ⟩
    have ⟨ε,hε⟩ := ε
    let f'' (i : ι) := Function.surjInv (hε i).right
    have h1 (i : ι) : Function.LeftInverse (f'' i) (ε i) := by
      apply Function.leftInverse_surjInv
      apply hε i
    have h2 (i : ι) : Function.RightInverse (f'' i) (ε i) := by
      apply Function.rightInverse_surjInv
    let f' (i : ι) : (A' ⧸ J i) →⊕ A i := by
      apply MVHom.inverse (ε i) (f'' i) (h1 i) (h2 i)
    let f : A' →⊕ ∀ (i : ι), A i := {
      toFun x i := f' i ⟦x⟧
      map_zero' := by
        ext i
        calc f' i ⟦0⟧
        _ = f' i (0 : A' ⧸ J i) := by rfl
        _ = 0 := by rw[map_zero]
      map_add' := by
        intro x y
        ext i
        calc f' i ⟦x + y⟧
        _ = f' i (⟦x⟧ + ⟦y⟧) := by rfl
        _ = f' i (⟦x⟧ ⊕ ⟦y⟧) := by rfl
        _ = (f' i ⟦x⟧) ⊕ (f' i ⟦y⟧) := by rw[map_oAdd]
      map_not := by
        intro x
        ext i
        calc - (f' i ⟦x⟧)
        _ = f' i ⟦- x⟧ := by rw[map_not] ; rfl
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
      replace h : (fun (i : ι) => f' i ⟦x⟧) = 0 := by
        apply h
      unfold f' at h
      replace h : (fun (i : ι) => (ε i).inverse (f'' i) (h1 i) (h2 i) ⟦x⟧) = 0 := by
        apply h
      replace h (i : ι) : (ε i).inverse (f'' i) (h1 i) (h2 i) ⟦x⟧ = 0 := by
        calc (ε i).inverse (f'' i) (h1 i) (h2 i) ⟦x⟧
        _ = (fun (i : ι) => (ε i).inverse (f'' i) (h1 i) (h2 i) ⟦x⟧) i := by rfl
        _ = (0 : (i : ι) → A i) i := by rw[h]
        _ = (0 : A i) := by rfl
      replace h (i : ι) : ⟦x⟧ ∈ ker
        (MVHom.inverse (ε i) (f'' i) (h1 i) (h2 i)) := by
        unfold ker
        apply h
      have h' (i : ι) : ker (MVHom.inverse (ε i) (f'' i) (h1 i) (h2 i)) = ⊥ := by
        rw[←ker_bot_iff_injective]
        suffices this : Function.Injective (Function.surjInv (hε i).right) from by
          apply this
        rw[Function.injective_iff_hasLeftInverse]
        use (ε i)
        rw[Function.leftInverse_iff_comp]
        ext y
        calc ((ε i) ∘ (Function.surjInv (hε i).right)) y
        _ = (ε i) ((Function.surjInv (hε i).right) y) := by rfl
        _ = y := by
          apply Function.surjInv_eq
      replace h (i : ι) : ⟦x⟧ ∈ (⊥ : MVAlgebra_Ideal (A' ⧸ J i)) := by
        rw[←h' i]
        apply h i
      replace h (i : ι) : (⟦x⟧ : A' ⧸ J i) = (0 : (A' ⧸ J i)) :=
         MVIdeal.mem_bot_iff_zero.mp (h i)
      replace h (i : ι) : (⟦x⟧ : A' ⧸ J i) = (⟦0⟧ : (A' ⧸ J i)) := by
        calc ⟦x⟧
        _ = (0 : (A' ⧸ J i)) := by rw[h i]
      replace h (i : ι) : dist x 0 ∈ J i := Quotient.eq.mp (h i)
      replace h (i : ι) : x ∈ J i := by
        rw[MVDist.dist_zero] at h
        apply h i
      rw[←hJ]
      intro I'
      rw[Set.mem_setOf]
      intro ⟨I,hI,hI'⟩
      rw[←hI']
      rw[SetLike.mem_coe]
      have ⟨i,hI⟩ := hI
      rw[←hI]
      suffices this : x ∈ J i from by apply this
      apply h i
    case right =>
      intro i
      unfold f
      suffices this : Function.Surjective (fun (x : A') => f' i ⟦x⟧) from by
        apply this
      unfold f'
      suffices this : Function.Surjective (fun (x : A') =>
        Function.surjInv (hε i).right ⟦x⟧) from by
        apply this
      suffices this : Function.Surjective (fun (x : A') =>
        Function.surjInv (hε i).right (Quotient.mk (setoidOfDist (J i)) x)) from by
        apply this
      suffices this : Function.Surjective
        ((Function.surjInv (hε i).right) ∘ (Quotient.mk (setoidOfDist (J i)))) from by
        apply this
      apply Function.Surjective.comp
      case hg =>
        intro x
        use (ε i) x
        have hq := Function.leftInverse_surjInv (hε i)
        rw[Function.leftInverse_iff_comp] at hq
        calc Function.surjInv (hε i).right ((ε i) x)
        _ = (Function.surjInv (hε i).right ∘ (ε i)) x := rfl
        _ = id x := by rw[hq]
        _ = x := rfl
      case hf =>
        apply Quotient.ind
        intro x
        use x
  case mp =>
    intro ⟨f,hi,hs⟩
    let J (i : ι) : MVAlgebra_Ideal A' := ker (MVHom.comp (proj i) f)
    use J
    apply And.intro
    case left =>
      sorry -- 1.2.8
    case right =>
      rw[←le_bot_iff]
      intro x h
      rw[SetLike.mem_coe]
      rw[SetLike.mem_coe] at h
      replace h (i : ι) : x ∈ J i := by
        apply h
        rw[Set.mem_setOf]
        use J i
        apply And.intro
        case left => use i
        case right => rfl
      replace h (i : ι) : (MVHom.comp (proj i) f) x = 0 := by
        rw[←MVIdeal.mem_bot_iff_zero]
        rw[←mem_comap]
        apply h i
      replace h (i : ι) : proj i (f x) = 0 := by
        apply h i
      replace h : f x = 0 := by
        ext i
        apply h i
      replace h : x ∈ ker f := by
        rw[mem_comap]
        apply h
      have hb : ker f = ⊥ := by
        rw[←ker_bot_iff_injective]
        apply hi
      rw[hb] at h
      apply h
