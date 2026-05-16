import MVAlgebras.Basic
import MVAlgebras.NaturalOrder
import MVAlgebras.MVAlgebraHom
import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.UnionInter

@[ext]
structure MVAlgebra_Ideal (A : Type*) [MVAlgebra A] where
  carrier : Set A
  zero_mem : 0 ∈ carrier
  le_mem {x y : A} : x ∈ carrier → y ≤ x → y ∈ carrier
  oAdd_mem {x y : A} : x ∈ carrier → y ∈ carrier → (x ⊕ y) ∈ carrier

class MVAlgebra_IdealClass (S : Type*) (A : Type*) [MVAlgebra A] extends (SetLike S A) where
  zero_mem' (I : S) : (0 : A) ∈ I
  le_mem' {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I
  oAdd_mem' {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I

variable {A : outParam Type*} {S : Type*} [MVAlgebra A] [MVAlgebra_IdealClass S A]

lemma zero_mem (I : S) : 0 ∈ I := MVAlgebra_IdealClass.zero_mem' I

lemma le_mem {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I := MVAlgebra_IdealClass.le_mem'

lemma oAdd_mem {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I := MVAlgebra_IdealClass.oAdd_mem'

instance : MVAlgebra_IdealClass (MVAlgebra_Ideal A) A where
  coe I := I.carrier
  coe_injective' := by
    intro I J h
    ext1
    exact h
  zero_mem' I := I.zero_mem
  le_mem' := by
    intro I x y
    apply I.le_mem
  oAdd_mem' := by
    intro I x y
    exact I.oAdd_mem

instance : Coe (MVAlgebra_Ideal A) (Set A) where
  coe I := I.carrier

variable {B F T : Type*} [MVAlgebra B] [MVAlgebra_IdealClass S A]
  [MVAlgebra_IdealClass T B] [MVAlgebraHomClass F A B]

@[reducible]
def comap (φ : F) (I : T) : MVAlgebra_Ideal A where
  carrier := ⇑φ ⁻¹' ↑I
  zero_mem := by
    rw[Set.mem_preimage]
    rw[map_zero]
    apply zero_mem I
  le_mem := by
    intro x y hx h_le
    exact le_mem hx (monotone φ h_le)
  oAdd_mem := by
    intro x y
    rw[Set.mem_preimage,Set.mem_preimage,Set.mem_preimage]
    intro hx hy
    rw[map_oAdd]
    exact oAdd_mem hx hy

@[reducible]
def bot : MVAlgebra_Ideal A where
  carrier := {0}
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
    apply Set.mem_singleton

@[reducible]
def top : MVAlgebra_Ideal A where
  carrier := {x | x : A}
  zero_mem := by use 0
  le_mem := by
    intro x y _ _
    use y
  oAdd_mem := by
    intro x y _ _
    use x ⊕ y

@[reducible]
def iInter {I : Type*} (ι : I → MVAlgebra_Ideal A) : MVAlgebra_Ideal A where
  carrier := Set.iInter (fun i => ι i)
  zero_mem := by
    intro J ⟨i,h⟩
    subst_eqs
    suffices this : 0 ∈ (ι i) from by apply this
    exact (ι i).zero_mem
  le_mem := by
    intro x y hx h_le _ ⟨i,h⟩
    subst_eqs
    replace hx : ∀ (i : I), x ∈ (ι i) := by
      apply Set.mem_iInter.mp
      exact hx
    exact (ι i).le_mem (hx i) h_le
  oAdd_mem := by
    intro x y hx hy _ ⟨i,h⟩
    subst_eqs
    replace hx : ∀ (i : I), x ∈ (ι i) := by
      apply Set.mem_iInter.mp
      exact hx
    replace hy : ∀ (i : I), y ∈ (ι i) := by
      apply Set.mem_iInter.mp
      exact hy
    exact (ι i).oAdd_mem (hx i) (hy i)

@[reducible]
def inter (I J : MVAlgebra_Ideal A) : MVAlgebra_Ideal A where
  carrier := I ∩ J
  zero_mem := ⟨I.zero_mem,J.zero_mem⟩
  le_mem := by
    intro x y ⟨hxI,hxJ⟩ h_le
    exact ⟨I.le_mem hxI h_le,J.le_mem hxJ h_le⟩
  oAdd_mem := by
    intro x y ⟨hxI,hxJ⟩ ⟨hyI,hyJ⟩
    exact ⟨I.oAdd_mem hxI hyI, J.oAdd_mem hxJ hyJ⟩

@[reducible]
def ker (f : F) : MVAlgebra_Ideal A := comap f (bot : MVAlgebra_Ideal B)

open Classical in
def closure' (W : Set A) : MVAlgebra_Ideal A where
  carrier := {x : A | ∃ (I : Multiset A), x ≤ (I.sum) ∧ (∀ (y : A), y ∈ I → y ∈ W)}
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
        exact Wy z h₁

def sup (I : MVAlgebra_Ideal A) (J : MVAlgebra_Ideal A) : MVAlgebra_Ideal A := closure' (I ∪ J)

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

lemma closed_sum {I : MVAlgebra_Ideal A} {L : Multiset A} (h : ∀ (x : A), x ∈ L → x ∈ I) :
  L.sum ∈ I := by
  apply Multiset.sum_induction
  case p_add =>
    intro _ _
    exact I.oAdd_mem
  case p_zero => exact I.zero_mem
  case p_s => exact h

lemma closure_eq (I : MVAlgebra_Ideal A) : closure' I = I := by
  symm
  ext1
  apply Set.Subset.antisymm (subset_closure' I.carrier)
  intro x ⟨L,hle,hin⟩
  suffices this : L.sum ∈ I from I.le_mem this hle
  apply closed_sum hin

instance : PartialOrder (MVAlgebra_Ideal A) where
  le I J := Subset I.carrier J.carrier
  le_refl I := by rfl
  le_antisymm I J := by
    intro h₁ h₂
    ext1
    apply subset_antisymm h₁ h₂
  le_trans I J K := by
    apply subset_trans

lemma closure_mono' : Monotone (closure' : Set A → MVAlgebra_Ideal A) := by
  intro I J hle x ⟨L,hSum,hin⟩
  use L
  apply And.intro
  case left => exact hSum
  intro y hyL
  exact hle (hin y hyL)

open Classical in
theorem closure_ideal_union (I : MVAlgebra_Ideal A) (z : A) :
  closure' (I ∪ {z}) = {x : A | ∃ (a : I), ∃ (n : Nat), x ≤ (n • z) ⊕ a} := by
  ext x
  apply Iff.intro
  case mp =>
    intro ⟨L,hle,hin⟩
    let R := Multiset.filter (fun (y : A) => ¬ Eq z y) L
    let S := Multiset.filter (fun (y : A) => Eq z y) L
    have hadd : S + R = L := by
      unfold R
      unfold S
      rw[Multiset.filter_add_not]
    replace h₁ : ∀ (y : A), y ∈ R → y ∈ I.carrier ∪ {z} := by
      intro y h
      apply hin
      rw[←hadd]
      rw[Multiset.mem_add]
      right
      apply h
    replace h₁ : ∀ (y : A), y ∈ R → y ∈ I.carrier := by
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
    use ⟨R.sum,closed_sum h₁⟩
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
        have hn : (Multiset.replicate n z).card = n := Multiset.card_replicate n z
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
        rw[Set.mem_union]
        left
        have h₅ : (if (¬ a = z) then ({a} : Multiset A) else ∅) ⊆ ({a} : Multiset A) := by
          cases eq_or_ne a z
          case inl heq' =>
            rw[ite_not]
            rw[eq_true heq']
            rw[ite_cond_eq_true]
            tauto ; tauto
          case inr heq' =>
            rw[ite_not]
            rw[eq_false heq']
            rw[ite_cond_eq_false]
            tauto ; tauto
        have hfin : y ∈ ({a} : Multiset A) := by
          apply h₅
          apply h₃
        replace hfin : y = a := Multiset.mem_singleton.mp hfin
        subst hfin
        apply hI


instance : BoundedOrder (MVAlgebra_Ideal A) where
  bot := bot
  top := top
  le_top I x _ := by
    use x
  bot_le I x h := by
    replace h : x = 0 := by exact h
    subst_eqs
    exact I.zero_mem

instance : Lattice (MVAlgebra_Ideal A) where
  inf := inter
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := sup
  le_sup_left := by
    intro I J
    calc I.carrier
    _ ⊆ I.carrier ∪ J.carrier := by apply Set.subset_union_left
    _ ⊆ closure' (I.carrier ∪ J.carrier) := by apply subset_closure'
  le_sup_right := by
    intro I J
    calc J.carrier
    _ ⊆ I.carrier ∪ J.carrier := by apply Set.subset_union_right
    _ ⊆ closure' (I.carrier ∪ J.carrier) := by apply subset_closure'
  sup_le := by
    intro I J K hIK hJK
    have hle : (I.carrier ∪ J) ≤ K := Set.union_subset hIK hJK
    calc sup I J
    _ = closure' (I ∪ J) := rfl
    _ ≤ closure' K := closure_mono' hle
    _ = K := closure_eq K

def isMaximal (I : MVAlgebra_Ideal A) : Prop := ∀ (J : MVAlgebra_Ideal A), I < J → J = ⊤

theorem max_iff (J : MVAlgebra_Ideal A) : isMaximal J ↔
  (∀ (x : A), ¬ x ∈ J ↔ ∃ (n : Nat), -(n • x) ∈ J) := by
  apply Iff.intro
  case mp =>
    intro hmax x
    apply Iff.intro
    case mp =>
      intro hnJ
      let K := closure' ({x} ∪ J)
      have htop : K = ⊤ := by
        apply hmax
        rw[Preorder.lt_iff_le_not_ge]
        apply And.intro
        case a.left =>
          apply Set.le_iff_subset.mpr
          calc J.carrier
          _ ⊆ {x} ∪ J.carrier := Set.subset_union_right
          _ ⊆ closure' ({x} ∪ J) := subset_closure' _
          _ = K := rfl
        case a.right =>
          intro h
          have hxK : x ∈ K := by
            unfold K
            apply subset_closure'
            left
            rfl
          exact hnJ (h hxK)
