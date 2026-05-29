import MVAlgebras.Basic
import MVAlgebras.NaturalOrder
import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Group.Submonoid.Defs

open MVOrder

/-- An ideal of an MVAlgebra is a subset that contains zero, is closed under addition,
and is donward closed
-/
@[ext]
class MVAlgebra_IdealClass (S : Type*) (A : outParam Type*) [MVAlgebra A] extends
  (SetLike S A) where
  zero_mem' (I : S) : (0 : A) ∈ I
  le_mem' {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I
  oAdd_mem' {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I

/-A concrete ideal of an MVAlgebra A-/
@[ext]
class MVAlgebra_Ideal (A : Type*) [MVAlgebra A] where
  carrier : Set A
  zero_mem : 0 ∈ carrier
  le_mem {x y : A} : x ∈ carrier → y ≤ x → y ∈ carrier
  oAdd_mem {x y : A} : x ∈ carrier → y ∈ carrier → (x ⊕ y) ∈ carrier

namespace MVIdeal

variable {A : outParam Type*} {S : semiOutParam Type*} {S' : Type*} [MVAlgebra A]
  [MVAlgebra_IdealClass S A]

lemma le_mem {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I := MVAlgebra_IdealClass.le_mem'

lemma oAdd_mem {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I := MVAlgebra_IdealClass.oAdd_mem'

instance : SetLike (MVAlgebra_Ideal A) A where
  coe := fun I => I.carrier
  coe_injective' := by
    intro I J h
    ext1
    apply h

instance : MVAlgebra_IdealClass (MVAlgebra_Ideal A) A where
  zero_mem' _ := MVAlgebra_Ideal.zero_mem
  le_mem' := MVAlgebra_Ideal.le_mem
  oAdd_mem' := MVAlgebra_Ideal.oAdd_mem

instance (I : MVAlgebra_Ideal A) : AddSubmonoid A where
  carrier := I.carrier
  add_mem' := by
    intro x y
    apply I.oAdd_mem
  zero_mem' := by
    apply I.zero_mem

instance : AddSubmonoidClass S A where
  add_mem := oAdd_mem
  zero_mem := MVAlgebra_IdealClass.zero_mem'

instance (I : MVAlgebra_Ideal A) : AddMonoid I where
  add := (fun ⟨x,hx⟩ ⟨y,hy⟩ => ⟨x ⊕ y,I.oAdd_mem hx hy⟩)
  add_assoc := by
    intro _ _ _
    ext1
    apply add_assoc
  zero := ⟨0,I.zero_mem⟩
  zero_add := by
    intro _
    ext1
    apply zero_add
  add_zero := by
    intro _
    ext1
    apply add_zero
  nsmul := fun (n : Nat) (⟨x,hx⟩ : I) => ⟨(n • x),nsmul_mem hx n⟩

/-- Might be able to remove this if it isn't used
-/
lemma coe_eq_iff {I J : MVAlgebra_Ideal A} : I = J ↔ (I : Set A) = (J : Set A) := by
  apply Iff.intro
  case mp =>
    tauto
  case mpr =>
    intro h
    ext1
    apply h

/-- Indexed intersection of ideals
-/
@[implicit_reducible]
def iInter {I : Type*} (ι : I → S) : MVAlgebra_Ideal A where
  carrier := Set.iInter (fun i => ι i)
  zero_mem := by
    intro J ⟨i,h⟩
    subst_eqs
    suffices this : 0 ∈ (ι i) from by apply this
    apply zero_mem
  le_mem := by
    intro x y hx h_le _ ⟨i,h⟩
    subst_eqs
    replace hx : ∀ (i : I), x ∈ (ι i) := by
      apply Set.mem_iInter.mp
      exact hx
    exact le_mem (hx i) h_le
  oAdd_mem := by
    intro x y hx hy _ ⟨i,h⟩
    subst_eqs
    replace hx : ∀ (i : I), x ∈ (ι i) := by
      apply Set.mem_iInter.mp
      exact hx
    replace hy : ∀ (i : I), y ∈ (ι i) := by
      apply Set.mem_iInter.mp
      exact hy
    exact oAdd_mem (hx i) (hy i)

@[implicit_reducible]
instance : Inter (MVAlgebra_Ideal A) where
  inter := fun (I J : MVAlgebra_Ideal A) =>
    {carrier := I ∩ J
     zero_mem := ⟨zero_mem I,zero_mem J⟩
     le_mem := by
       intro x y ⟨hxI,hxJ⟩ h_le
       exact ⟨le_mem hxI h_le,le_mem hxJ h_le⟩
     oAdd_mem := by
       intro x y ⟨hxI,hxJ⟩ ⟨hyI,hyJ⟩
       exact ⟨oAdd_mem hxI hyI, oAdd_mem hxJ hyJ⟩ }

open Classical in
 @[implicit_reducible]
 def closure : Set A →  MVAlgebra_Ideal A := fun (W : Set A) =>
  { carrier := {x : A | ∃ (I : Multiset A), x ≤ (I.sum) ∧ (∀ (y : A), y ∈ I → y ∈ W)}
    zero_mem := by
      use {}
      apply And.intro
      case left =>
        rfl
      case right =>
        tauto
    le_mem := by
      intro x y ⟨I,h,h'⟩ h_le
      exact ⟨I,le_trans h_le h,h'⟩
    oAdd_mem := by
      intro x y ⟨Ix,hx,Wx⟩ ⟨Iy,hy,Wy⟩
      use (Ix + Iy)
      apply And.intro
      case left =>
        calc x ⊕ y
        _ ≤ x ⊕ Iy.sum := le_oAdd y Iy.sum x hy
        _ ≤ Ix.sum ⊕ Iy.sum := oAdd_le x Ix.sum Iy.sum hx
        _ = Ix.sum + Iy.sum := rfl
        _ = (Ix + Iy).sum := by rw[Multiset.sum_add]
      case right =>
        intro z h
        replace h : z ∈ Ix ∨ z ∈ Iy := Multiset.mem_add.mp h
        cases h
        case inl h₁ =>
          exact Wx z h₁
        case inr h₁ =>
          exact Wy z h₁ }

@[implicit_reducible]
def sup (I J : MVAlgebra_Ideal A) : MVAlgebra_Ideal A :=
  closure (I ∪ J)

lemma subset_closure (I : Set A) :
  I ⊆ closure I := by
    intro x h
    use ({x} : Multiset A)
    apply And.intro
    case left =>
      rw[←Multiset.sum_toList]
      rw[Multiset.toList_singleton]
      rw[List.sum_singleton]
    case right =>
      intro y hy
      replace hy : y = x := List.mem_singleton.mp hy
      subst_eqs
      exact h

lemma sum_mem {I : S} {L : Multiset A} (h : ∀ (x : A), x ∈ L → x ∈ I) : L.sum ∈ I := by
  apply Multiset.sum_induction
  case p_add =>
    intro _ _
    exact oAdd_mem
  case p_zero => apply zero_mem
  case p_s => exact h

lemma closure_eq (I : MVAlgebra_Ideal A) : closure I = I := by
  symm
  ext1
  apply Set.Subset.antisymm (subset_closure _)
  intro x ⟨L,hle,hin⟩
  suffices this : x ∈ (I : Set A) from by apply this
  exact le_mem (sum_mem hin) hle

instance : PartialOrder (MVAlgebra_Ideal A) where
  le I J := (I : Set A) ⊆ (J : Set A)
  le_refl I := by rfl
  le_antisymm I J := by
    intro h₁ h₂
    rw[coe_eq_iff]
    apply subset_antisymm h₁ h₂
  le_trans I J K := by
    apply subset_trans

lemma closure_mono : Monotone (closure : Set A → MVAlgebra_Ideal A) := by
  intro I J hle x ⟨L,hSum,hin⟩
  use L
  apply And.intro
  case left => exact hSum
  intro y hyL
  exact hle (hin y hyL)

open Classical in
theorem closure_union (I : MVAlgebra_Ideal A) (z : A) :
  closure (I ∪ {z} : Set A) =
  {x : A | ∃ (a : I), ∃ (n : Nat), x ≤ (n • z) ⊕ a} := by
  ext x
  apply Iff.intro
  case mp =>
    intro ⟨L,hle,hin⟩
    let R := Multiset.filter (fun (y : A) => ¬ z = y) L
    let S := Multiset.filter (fun (y : A) => z = y) L
    have hadd : S + R = L := by
      unfold R
      unfold S
      rw[Multiset.filter_add_not]
    replace h₁ : ∀ (y : A), y ∈ R → y ∈ (I ∪ {z} : Set A) := by
      intro y h
      apply hin
      rw[←hadd]
      rw[Multiset.mem_add]
      right
      apply h
    replace h₁ : ∀ (y : A), y ∈ R → y ∈ I := by
      intro y h
      cases h₁ y h
      case inl => assumption
      case inr hz =>
        exfalso
        replace hz : y = z := by apply hz
        suffices this : y ≠ z from by
          exact this hz
        unfold R at h
        replace h := Multiset.of_mem_filter h
        rw[ne_eq]
        intro h'
        exact h h'.symm
    have h₂ : L.count z = S.card := by
      unfold S
      rw[Multiset.filter_eq]
      rw[Multiset.card_replicate]
    use ⟨R.sum,sum_mem h₁⟩
    use S.card
    calc x
    _ ≤ L.sum := hle
    _ = (S + R).sum := by rw[hadd]
    _ = S.sum + R.sum := by rw[Multiset.sum_add]
    _ = (Multiset.filter (fun (y : A) => Eq z y) L).sum + R.sum := by unfold S ; tauto
    _ = (Multiset.replicate (L.count z) z).sum + R.sum := by rw[Multiset.filter_eq]
    _ = ((L.count z) • z) + R.sum := by rw[Multiset.sum_replicate]
    _ = (S.card • z) + R.sum := by rw[h₂]
  case mpr =>
    intro ⟨a,n,hle⟩
    have ⟨a,hI⟩ := a
    use (Multiset.replicate n z + {a} : Multiset A)
    apply And.intro
    case left =>
      calc x
      _ ≤ (n • z) + a := hle
      _ = (Multiset.replicate n z).sum + a := by rw[Multiset.sum_replicate]
      _ = (Multiset.replicate n z).sum + ({a} : Multiset A).sum :=
        by rw[Multiset.sum_singleton]
      _ = (Multiset.replicate n z + {a}).sum := by rw[Multiset.sum_add]
    case right =>
      intro y h
      cases eq_or_ne y z
      case inl heq =>
        subst heq
        apply Set.subset_union_right
        apply Set.mem_singleton
      case inr heq =>
        let p := fun (y : A) => ¬ y = z
        replace heq : p y := by apply heq
        have h₂ : ∀ (y : A), y ∈ Multiset.replicate n z → ¬ ¬ (y = z) := by
          intro y h
          rw[not_not]
          apply (Multiset.mem_replicate.mp h).right
        have h₃ : Multiset.filter p (Multiset.replicate n z + {a}) = if p a then {a} else ∅ := by
          calc Multiset.filter p (Multiset.replicate n z + {a})
          _ = Multiset.filter p (Multiset.replicate n z) +
            Multiset.filter p {a} := by rw[Multiset.filter_add]
          _ = Multiset.filter p (Multiset.replicate n z) +
            if p a then {a} else ∅ := by rw[Multiset.filter_singleton]
          _ = 0 + if p a then {a} else ∅ := by rw[Multiset.filter_eq_nil.mpr h₂]
          _ = if p a then {a} else ∅ := by rw[Multiset.zero_add]
        replace h₃ : y ∈ if (¬ a = z) then ({a} : Multiset A) else ∅ := by
          rw[←h₃]
          apply Multiset.mem_filter.mpr ⟨h,heq⟩
        suffices this : y ∈ ((I : Set A) ∪ {z}) from by
          apply this
        rw[Set.mem_union]
        left
        have h₅ : (if (¬ a = z) then ({a} : Multiset A) else ∅) ⊆ ({a} : Multiset A) := by
          cases eq_or_ne a z
          case inl heq' =>
            rw[ite_not]
            rw[eq_true heq']
            rw[ite_cond_eq_true]
            ·tauto
            tauto
          case inr heq' =>
            rw[ite_not]
            rw[eq_false heq']
            rw[ite_cond_eq_false]
            ·tauto
            tauto
        have hfin : y ∈ ({a} : Multiset A) := by
          apply h₅
          apply h₃
        replace hfin : y = a := Multiset.mem_singleton.mp hfin
        subst hfin
        apply hI

instance : BoundedOrder (MVAlgebra_Ideal A) where
  bot := {  carrier := {0}
            zero_mem := rfl
            le_mem := by
              intro x y hx h_le
              replace hx : x = 0 := by exact hx
              subst_eqs
              suffices this : y = 0 from by exact this
              exact le_zero h_le
            oAdd_mem := by
              intro x y hx hy
              replace hx : x = 0 := by exact hx
              replace hy : y = 0 := by exact hy
              subst_eqs
              rw[oAdd_zero]
              apply Set.mem_singleton }
  top := {  carrier := {x | x : A}
            zero_mem := by use 0
            le_mem := by
              intro x y _ _
              use y
            oAdd_mem := by
              intro x y _ _
              use x ⊕ y}
  le_top I x _ := by
    use x
  bot_le I x h := by
    replace h : x = 0 := by exact h
    subst_eqs
    exact I.zero_mem

lemma mem_bot_iff_zero {x : A} : x ∈ (⊥ : MVAlgebra_Ideal A) ↔ x = 0 := by
  tauto

instance : Lattice (MVAlgebra_Ideal A) where
  inf := fun (I J) => I ∩ J
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := sup
  le_sup_left := by
    intro I J
    calc I.carrier
    _ ⊆ I.carrier ∪ J.carrier := by apply Set.subset_union_left
    _ ⊆ closure (I.carrier ∪ J.carrier) := by
      apply subset_closure (I.carrier ∪ J.carrier)
  le_sup_right := by
    intro I J
    calc J.carrier
    _ ⊆ I.carrier ∪ J.carrier := by apply Set.subset_union_right
    _ ⊆ closure (I.carrier ∪ J.carrier) := by
      apply subset_closure (I.carrier ∪ J.carrier)
  sup_le := by
    intro I J K hIK hJK
    have hle : (I.carrier ∪ J) ≤ K := Set.union_subset hIK hJK
    calc sup I J
    _ = closure (I.carrier ∪ J) := rfl
    _ ≤ closure K := closure_mono hle
    _ = K := closure_eq K

lemma top_iff_mem_one {I : MVAlgebra_Ideal A} :
  I = (⊤ : MVAlgebra_Ideal A) ↔ 1 ∈ I  := by
  apply Iff.intro
  case mpr =>
    intro h
    ext x
    apply Iff.intro
    case mp =>
      intro h'
      use x
    case mpr =>
      intro _
      apply I.le_mem h (le_one x)
  case mp =>
    intro h
    rw[h]
    use 1

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
      replace hle : ((n • x) ⊕ a) = 1 := one_le hle
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
