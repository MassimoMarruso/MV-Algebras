import MVAlgebras.Defs
import MVAlgebras.Ideal.Defs
import MVAlgebras.NaturalOrder

variable {A : Type*} [MVAlgebra A]

namespace MVIdeal

def isMaximal (I : MVAlgebra_Ideal A) : Prop :=
  I ≠ ⊤ ∧ ∀ (J : MVAlgebra_Ideal A), I < J → J = ⊤

class MaximalIdeal (A : Type*) [MVAlgebra A] extends MVAlgebra_Ideal A where
  isMaximal' : carrier ≠ ⊤ ∧ ∀ (J : MVAlgebra_Ideal A), carrier < J → J = ⊤

theorem maximal_iff (J : MVAlgebra_Ideal A) : isMaximal J ↔
  (∀ (x : A), ¬ x ∈ (J : Set A) ↔ ∃ (n : Nat), -(n • x) ∈ (J : Set A)) := by
  apply Iff.intro
  case mp =>
    intro ⟨hntop,hmax⟩ x
    let K := closure (J ∪ {x})
    have htop (hxJ : x ∉ (J : Set A)) : K = ⊤ := by
      apply hmax
      apply (Preorder.lt_iff_le_not_ge _ _).mpr
      apply And.intro
      case a.left =>
        apply Set.le_iff_subset.mpr
        calc (J : Set A)
        _ ⊆ J ∪ {x}:= Set.subset_union_left
        _ ⊆ closure (J ∪ {x}) := subset_closure (J ∪ {x})
        _ = K := rfl
      case a.right =>
        intro h
        have hxK : x ∈ K := by
          unfold K
          apply subset_closure
          right
          rfl
        exact hxJ (h hxK)
    apply Iff.intro
    case mp =>
      intro hxJ
      have hK : K = ⊤ := htop hxJ
      replace hK (y : A) : y ∈ K := by
        rw[hK]
        use y
      unfold K at hK
      replace hK (y : A) : y ∈ {y : A | ∃ (a : J), ∃ (n : Nat), y ≤ (n • x) ⊕ a} := by
        rw[←closure_union]
        apply hK
      replace hK (y : A) : ∃ (a : J), ∃ (n : Nat), y ≤ (n • x) ⊕ a := by
        apply hK
      have ⟨a,n,hle⟩ := hK 1
      replace ⟨a,haJ⟩ := a
      use n
      replace hle : ((n • x) ⊕ a) = 1 := MVOrder.one_le hle
      replace hle : - (n • x) ≤ a := by
        apply le_iff₂.mpr
        rw[oMul_dual]
        rw[neg_neg,neg_neg]
        rw[not_iff_not']
        rw[←not_zero]
        rw[neg_neg]
        apply hle
      apply le_mem haJ hle
    case mpr =>
      intro ⟨n,h⟩ hxJ
      let K := closure (J ∪ {x})
      have heq : J = K := by
        calc J
        _ = closure J := by rw[closure_eq]
        _ = closure (J ∪ {x}) := by
          rw[Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hxJ)]
        _ = K := by rfl
      apply hntop
      apply top_iff_mem_one.mpr
      rw[←oAdd_not_self (n • x)]
      refine oAdd_mem ?_ h
      apply nsmul_mem hxJ
  case mpr =>
    intro h
    apply And.intro
    case left =>
      intro h₂
      replace h₂ := top_iff_mem_one.mp h₂
      suffices this : 1 ∉ (J : Set A) from by
        exact this h₂
      apply (h 1).mpr
      use 1
      rw[one_nsmul]
      rw[not_one]
      apply zero_mem
    case right =>
      intro I hle
      replace hle : (J : Set A) ⊂ (I : Set A) := by apply hle
      let K := (I : Set A) \ J
      have hnK : K.Nonempty := by
        unfold K
        apply Set.diff_nonempty.mpr
        intro h₂
        replace h₂ := h₂.trans_ssubset hle
        replace ⟨hpos,hneg⟩ := Set.ssubset_def.mp h₂
        apply hneg hpos
      replace hnK : Nonempty K := by
        rw[Set.nonempty_iff_ne_empty']
        symm
        rw[←Set.nonempty_iff_empty_ne]
        exact hnK
      have ⟨y,hy⟩ := Classical.choice hnK
      apply top_iff_mem_one.mpr
      have hny : y ∉ J := by
        unfold K at hy
        rw[Set.mem_diff] at hy
        apply hy.right
      have ⟨n,h₃⟩ := (h y).mp hny
      replace h₃ := hle.subset h₃
      rw[←oAdd_not_self (n • y)]
      refine oAdd_mem ?_ h₃
      apply nsmul_mem
      unfold K at hy
      apply ((Set.mem_diff y).mp hy).left

def isPrime (I : MVAlgebra_Ideal A) : Prop :=
  ∀ {x y : A}, x ⊖ y ∈ I ∨ y ⊖ x ∈ I

class Prime_Ideal A [MVAlgebra A] extends MVAlgebra_Ideal A where
  isPrime' : ∀ {x y : A}, x ⊖ y ∈ carrier ∨ y ⊖ x ∈ carrier

instance (I : MVAlgebra_Ideal A) (h : isPrime I) : Prime_Ideal A where
  isPrime' := h

end MVIdeal
