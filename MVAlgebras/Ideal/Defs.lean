import MVAlgebras.Defs
import MVAlgebras.NaturalOrder
import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Submonoid.Basic

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
class MVAlgebra_Ideal (A : Type*) [MVAlgebra A] extends AddSubmonoid A where
  le_mem {x y : A} : x ∈ carrier → y ≤ x → y ∈ carrier

namespace MVIdeal

variable {A : outParam Type*} {S : semiOutParam Type*} {S' : Type*} [MVAlgebra A]
  [MVAlgebra_IdealClass S A]

@[simp]
lemma le_mem {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I := MVAlgebra_IdealClass.le_mem'

@[simp]
lemma oAdd_mem {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I := MVAlgebra_IdealClass.oAdd_mem'

instance : SetLike (MVAlgebra_Ideal A) A where
  coe := fun I => I.carrier
  coe_injective' := by
    intro I J h
    ext1
    apply h

instance : MVAlgebra_IdealClass (MVAlgebra_Ideal A) A where
  zero_mem' _ := MVAlgebra_Ideal.toAddSubmonoid.zero_mem
  le_mem' := MVAlgebra_Ideal.le_mem
  oAdd_mem' := MVAlgebra_Ideal.toAddSubmonoid.add_mem

instance : AddSubmonoidClass S A where
  add_mem := oAdd_mem
  zero_mem := MVAlgebra_IdealClass.zero_mem'

@[simp]
lemma carrier_coe (I : MVAlgebra_Ideal A) : I.carrier = (I : Set A) := rfl

/-- Indexed intersection of ideals
-/
@[implicit_reducible]
def iInter {I : Type*} (ι : I → S) : MVAlgebra_Ideal A where
  carrier := Set.iInter (fun i => ι i)
  zero_mem' := by
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
  add_mem' := by
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
     zero_mem' := ⟨zero_mem I,zero_mem J⟩
     le_mem := by
       intro x y ⟨hxI,hxJ⟩ h_le
       exact ⟨le_mem hxI h_le,le_mem hxJ h_le⟩
     add_mem' := by
       intro x y ⟨hxI,hxJ⟩ ⟨hyI,hyJ⟩
       exact ⟨oAdd_mem hxI hyI, oAdd_mem hxJ hyJ⟩ }

instance : InfSet (MVAlgebra_Ideal A) where
  sInf K := {
    carrier := sInf {(I : Set A) | I ∈ K}
    add_mem' := by
      intro x y hx hy W ⟨I,hIK,hIeq⟩
      suffices this : (x + y) ∈ I from by
        rw[←SetLike.mem_coe] at this
        rw[hIeq] at this
        apply this
      refine I.add_mem' ?x ?y
      case x =>
        apply hx
        use I
        apply And.intro
        case left => apply hIK
        case right => rfl
      case y =>
        apply hy
        use I
        apply And.intro
        case left => apply hIK
        case right => rfl
    zero_mem' := by
      intro W ⟨I,hIK,hIeq⟩
      rw[←hIeq]
      rw[SetLike.mem_coe]
      apply I.zero_mem'
    le_mem := by
      intro x y hx hle W ⟨I,hIK,hIeq⟩
      rw[←hIeq]
      rw[SetLike.mem_coe]
      refine I.le_mem ?_ hle
      apply hx
      use I
      apply And.intro
      case left => apply hIK
      case right => rfl }

@[implicit_reducible]
def closure (W : Set A) : MVAlgebra_Ideal A := sInf {I : MVAlgebra_Ideal A | W ⊆ ↑I}

@[implicit_reducible]
def closure' (W : Set A) : MVAlgebra_Ideal A where
  carrier := {x : A | ∃ (I : Multiset A), x ≤ (I.sum) ∧ (∀ (y : A), y ∈ I → y ∈ W)}
  zero_mem' := by
      use {}
      apply And.intro
      case left =>
        rfl
      case right =>
        tauto
  le_mem := by
      intro x y ⟨I,h,h'⟩ h_le
      exact ⟨I,le_trans h_le h,h'⟩
  add_mem' := by
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
          exact Wy z h₁

lemma sum_mem {I : S} {L : Multiset A} (h : ∀ (x : A), x ∈ L → x ∈ I) : L.sum ∈ I := by
  apply Multiset.sum_induction
  case p_add =>
    intro _ _
    exact oAdd_mem
  case p_zero => apply zero_mem
  case p_s => exact h

lemma closure_singleton {z : A} : closure' {z} = {y : A | ∃ (n : Nat), y ≤ n • z} := by
  ext x
  apply Iff.intro
  case mp =>
    intro ⟨I,hle,hin⟩
    replace hin : I = Multiset.replicate I.card z := by
      rw[Multiset.eq_replicate]
      apply And.intro
      case left => rfl
      case right =>
        intro a ha
        apply hin a ha
    rw[hin] at hle
    rw[Multiset.sum_replicate] at hle
    use I.card
  case mpr =>
    intro ⟨n,h⟩
    use Multiset.replicate n z
    apply And.intro
    case left =>
      rw[Multiset.sum_replicate]
      apply h
    case right =>
      intro y hy
      rw[Multiset.mem_replicate] at hy
      rw[hy.right]
      rfl

lemma subset_closure (W : Set A) : W ⊆ closure W := by
  intro x hx
  rw[SetLike.mem_coe]
  intro Y ⟨I,hI,heq⟩
  rw[←heq]
  apply hI
  apply hx

lemma subset_closure' (I : Set A) :
  I ⊆ closure' I := by
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

theorem closure_ofSubmonoid (W : Set A) :
  closure' W = closure W := by
    ext x
    apply Iff.intro
    case mp =>
      intro ⟨L,hle,hin⟩
      rw[carrier_coe]
      intro Y ⟨I,hI,hIY⟩
      rw[←hIY]
      rw[SetLike.mem_coe]
      refine I.le_mem ?_ hle
      rw[carrier_coe]
      apply sum_mem
      intro y hy
      apply hI
      apply hin
      apply hy
    case mpr =>
      intro hx
      rw[carrier_coe,SetLike.mem_coe]
      rw[carrier_coe,SetLike.mem_coe] at hx
      apply hx
      use closure' W
      apply And.intro
      case right => rfl
      case left =>
        rw[Set.mem_setOf]
        apply subset_closure'

@[implicit_reducible]
def sup (I J : MVAlgebra_Ideal A) : MVAlgebra_Ideal A :=
  closure (I ∪ J)

lemma closure_eq (I : MVAlgebra_Ideal A) : closure I = I := by
  ext x
  apply Iff.intro
  case mp =>
    intro h
    rw[carrier_coe] at h
    rw[SetLike.mem_coe] at h
    replace h := h I
    apply h
    use ↑I
    apply And.intro
    case right => rfl
    case left =>
      rw[Set.mem_setOf]
  case mpr =>
    intro hx
    rw[carrier_coe]
    rw[SetLike.mem_coe]
    intro Y ⟨J,hJ,heq⟩
    rw[←heq]
    apply hJ
    apply hx

instance : PartialOrder (MVAlgebra_Ideal A) where
  le I J := (I : Set A) ⊆ (J : Set A)
  le_refl I := by rfl
  le_antisymm I J := by
    intro h₁ h₂
    apply SetLike.coe_injective'
    apply subset_antisymm h₁ h₂
  le_trans I J K := by
    apply subset_trans

lemma closure_mono : Monotone (closure : Set A → MVAlgebra_Ideal A) := by
  intro I J hle x hx
  rw[SetLike.mem_coe]
  intro Y ⟨K,hK,heq⟩
  rw[←heq]
  rw[SetLike.mem_coe] at hx
  rw[SetLike.mem_coe]
  have h' := hx (closure J)
  rw[←closure_eq K]
  rw[heq]
  rw[←SetLike.mem_coe]
  apply hx
  use closure Y
  apply And.intro
  case right => rfl
  case left =>
    rw[Set.mem_setOf]
    intro y hI
    apply subset_closure Y
    rw[←heq]
    rw[SetLike.mem_coe]
    apply hK
    apply hle
    apply hI

open Classical in
theorem closure_union (I : MVAlgebra_Ideal A) (z : A) :
  closure (I ∪ {z} : Set A) =
  {x : A | ∃ (a : I), ∃ (n : Nat), x ≤ (n • z) ⊕ a} := by
  rw[←closure_ofSubmonoid]
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
            zero_mem' := rfl
            le_mem := by
              intro x y hx h_le
              replace hx : x = 0 := by exact hx
              subst_eqs
              suffices this : y = 0 from by exact this
              exact le_zero h_le
            add_mem' := by
              intro x y hx hy
              replace hx : x = 0 := by exact hx
              replace hy : y = 0 := by exact hy
              subst_eqs
              rw[add_zero]
              apply Set.mem_singleton }
  top := {  carrier := {x | x : A}
            zero_mem' := by use 0
            le_mem := by
              intro x y _ _
              use y
            add_mem' := by
              intro x y _ _
              use x ⊕ y
              rfl}
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
    intro I J x hI
    rw[SetLike.mem_coe]
    unfold sup
    apply subset_closure
    apply Or.intro_left
    apply hI
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

end MVIdeal
