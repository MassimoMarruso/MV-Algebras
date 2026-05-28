import MVAlgebras.Basic
import MVAlgebras.NaturalOrder
import Mathlib.Data.Set.Basic
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.RelClasses

@[ext]
class MVAlgebra_Ideal (A : Type*) [MVAlgebra A] where
  carrier : Set A
  zero_mem : 0 ∈ carrier
  le_mem {x y : A} : x ∈ carrier → y ≤ x → y ∈ carrier
  oAdd_mem {x y : A} : x ∈ carrier → y ∈ carrier → (x ⊕ y) ∈ carrier

@[ext]
class MVAlgebra_IdealClass (S : Type*) (A : outParam Type*) [MVAlgebra A] extends
  (SetLike S A) where
  zero_mem' (I : S) : (0 : A) ∈ I
  le_mem' {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I
  oAdd_mem' {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I

variable {A : outParam Type*} {S : semiOutParam Type*} [MVAlgebra A]
  [MVAlgebra_IdealClass S A]

lemma le_mem' {I : S} {x y : A} : x ∈ I → y ≤ x → y ∈ I := MVAlgebra_IdealClass.le_mem'

lemma oAdd_mem' {I : S} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I := MVAlgebra_IdealClass.oAdd_mem'

instance : CoeSort (MVAlgebra_Ideal A) (Set A) where
  coe := fun I => I.carrier

instance : Coe (MVAlgebra_Ideal A) (Set A) where
  coe := fun I => I.carrier

lemma coe_eq (I : MVAlgebra_Ideal A) : I.carrier = (I : Set A) := rfl

lemma le_mem {I : MVAlgebra_Ideal A} {x y : A} :
  x ∈ (I : Set A) → y ≤ x → y ∈ (I : Set A) := I.le_mem

lemma oAdd_mem {I : MVAlgebra_Ideal A} {x y : A} :
  x ∈ (I : Set A) → y ∈ (I : Set A) → (x ⊕ y) ∈ (I : Set A) := I.oAdd_mem

lemma zero_mem {I : MVAlgebra_Ideal A} : 0 ∈ (I : Set A) := I.zero_mem

instance : ZeroMemClass S A where
  zero_mem := MVAlgebra_IdealClass.zero_mem'

instance (I : MVAlgebra_Ideal A) : AddSubmonoid A where
  carrier := I.carrier
  add_mem' := by
    intro x y
    apply I.oAdd_mem
  zero_mem' := by
    apply I.zero_mem

instance : AddSubmonoidClass S A where
  add_mem := oAdd_mem'
  zero_mem := zero_mem

lemma coe_eq_iff {I J : MVAlgebra_Ideal A} : I = J ↔ (I : Set A) = (J : Set A) := by
  apply Iff.intro
  case mp =>
    tauto
  case mpr =>
    intro h
    ext1
    apply h

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
    suffices this : 0 ∈ ((ι i) : Set A) from by apply this
    exact zero_mem
  le_mem := by
    intro x y hx h_le _ ⟨i,h⟩
    subst_eqs
    replace hx : ∀ (i : I), x ∈ ((ι i) : Set A) := by
      apply Set.mem_iInter.mp
      exact hx
    exact le_mem (hx i) h_le
  oAdd_mem := by
    intro x y hx hy _ ⟨i,h⟩
    subst_eqs
    replace hx : ∀ (i : I), x ∈ ((ι i) : Set A) := by
      apply Set.mem_iInter.mp
      exact hx
    replace hy : ∀ (i : I), y ∈ ((ι i) : Set A) := by
      apply Set.mem_iInter.mp
      exact hy
    exact oAdd_mem (hx i) (hy i)

@[reducible]
def inter (I J : MVAlgebra_Ideal A)
  : MVAlgebra_Ideal A where
  carrier := I ∩ J
  zero_mem := ⟨zero_mem,zero_mem⟩
  le_mem := by
    intro x y ⟨hxI,hxJ⟩ h_le
    exact ⟨le_mem hxI h_le,le_mem hxJ h_le⟩
  oAdd_mem := by
    intro x y ⟨hxI,hxJ⟩ ⟨hyI,hyJ⟩
    exact ⟨oAdd_mem hxI hyI, oAdd_mem hxJ hyJ⟩

open Classical in
 @[reducible]
 def ideal_closure (W : Set A) : MVAlgebra_Ideal A where
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

@[reducible]
def sup (I J : MVAlgebra_Ideal A) : MVAlgebra_Ideal A :=
  ideal_closure ((I : Set A) ∪ J)

lemma subset_ideal_closure (I : Set A) :
  (I : Set A) ⊆ ideal_closure I := by
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

lemma sum_mem' {I : MVAlgebra_Ideal A} {L : Multiset A}
  (h : ∀ (x : A), x ∈ L → x ∈ (I : Set A)) : L.sum ∈ (I : Set A) := by
  apply Multiset.sum_induction
  case p_add =>
    intro _ _
    exact oAdd_mem
  case p_zero => exact zero_mem
  case p_s => exact h

lemma smul_mem {I : MVAlgebra_Ideal A} {n : Nat} {x : A} :
  x ∈ (I : Set A) → n • x ∈ (I : Set A) := by
  intro h
  let L := Multiset.replicate n x
  have h₁ : n • x = L.sum := by
    induction n
    case zero =>
      unfold L
      rw[Multiset.replicate_zero]
      rfl
    case succ n h₂ =>
      calc (n + 1) • x
      _ = (n • x) + (1 • x) := by rw[add_smul]
      _ = (Multiset.replicate n x).sum + x := by rw[h₂,one_smul]
      _ = (Multiset.replicate n x).sum + ({x} : Multiset A).sum :=
        by rw[Multiset.sum_singleton]
      _ = (Multiset.replicate n x).sum + (Multiset.replicate 1 x).sum :=
        by rw[Multiset.replicate_one]
      _ = (Multiset.replicate n x + Multiset.replicate 1 x).sum :=
        by rw[Multiset.sum_add]
      _ = (Multiset.replicate (n + 1) x).sum :=
        by rw[Multiset.replicate_add]
  rw[h₁]
  apply sum_mem'
  intro y h₃
  unfold L at h₃
  rw[Multiset.mem_replicate] at h₃
  have ⟨_,heq⟩ := h₃
  subst heq
  apply h

lemma ideal_closure_eq (I : MVAlgebra_Ideal A) :
  ideal_closure (I : Set A) = I := by
  symm
  ext1
  apply Set.Subset.antisymm (subset_ideal_closure _)
  intro x ⟨L,hle,hin⟩
  suffices this : x ∈ (I : Set A) from by apply this
  exact le_mem (sum_mem' hin) hle

instance : PartialOrder (MVAlgebra_Ideal A) where
  le I J := (I : Set A) ⊆ (J : Set A)
  le_refl I := by rfl
  le_antisymm I J := by
    intro h₁ h₂
    rw[coe_eq_iff]
    apply subset_antisymm h₁ h₂
  le_trans I J K := by
    apply subset_trans

lemma ideal_closure_mono : Monotone (ideal_closure : Set A → MVAlgebra_Ideal A) := by
  intro I J hle x ⟨L,hSum,hin⟩
  use L
  apply And.intro
  case left => exact hSum
  intro y hyL
  exact hle (hin y hyL)

open Classical in
theorem ideal_closure_union (I : MVAlgebra_Ideal A) (z : A) :
  ideal_closure ((I : Set A) ∪ {z} : Set A) =
  {x : A | ∃ (a : (I : Set A)), ∃ (n : Nat), x ≤ (n • z) ⊕ a} := by
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
    replace h₁ : ∀ (y : A), y ∈ R → y ∈ (I : Set A) ∪ {z} := by
      intro y h
      apply hin
      rw[←hadd]
      rw[Multiset.mem_add]
      right
      apply h
    replace h₁ : ∀ (y : A), y ∈ R → y ∈ (I : Set A) := by
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
    use ⟨R.sum,sum_mem' h₁⟩
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
  bot := bot
  top := top
  le_top I x _ := by
    use x
  bot_le I x h := by
    replace h : x = 0 := by exact h
    subst_eqs
    exact I.zero_mem

lemma mem_bot_iff_zero {x : A} : x ∈ ((⊥ : MVAlgebra_Ideal A) : Set A) ↔ x = 0 := by
  tauto

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
    _ ⊆ ideal_closure (I.carrier ∪ J.carrier) := by
      apply subset_ideal_closure (I.carrier ∪ J.carrier)
  le_sup_right := by
    intro I J
    calc J.carrier
    _ ⊆ I.carrier ∪ J.carrier := by apply Set.subset_union_right
    _ ⊆ ideal_closure (I.carrier ∪ J.carrier) := by
      apply subset_ideal_closure (I.carrier ∪ J.carrier)
  sup_le := by
    intro I J K hIK hJK
    have hle : (I.carrier ∪ J) ≤ K := Set.union_subset hIK hJK
    calc sup I J
    _ = ideal_closure (I.carrier ∪ J) := rfl
    _ ≤ ideal_closure K := ideal_closure_mono hle
    _ = K := ideal_closure_eq K

lemma top_iff_mem_one {I : MVAlgebra_Ideal A} : 1 ∈ (I : Set A) ↔ I = (⊤ : MVAlgebra_Ideal A) := by
  apply Iff.intro
  case mp =>
    intro h
    ext x
    apply Iff.intro
    case mp =>
      intro h'
      use x
    case mpr =>
      intro _
      apply I.le_mem h (le_one x)
  case mpr =>
    intro h
    rw[h]
    use 1

def isMaximal (I : MVAlgebra_Ideal A) : Prop := I ≠ ⊤ ∧ ∀ (J : MVAlgebra_Ideal A), I < J → J = ⊤

theorem ideal_maximal_iff (J : MVAlgebra_Ideal A) : isMaximal J ↔
  (∀ (x : A), ¬ x ∈ (J : Set A) ↔ ∃ (n : Nat), -(n • x) ∈ (J : Set A)) := by
  apply Iff.intro
  case mp =>
    intro ⟨hntop,hmax⟩ x
    let K := ideal_closure ((J : Set A) ∪ {x})
    have htop (hxJ : x ∉ (J : Set A)) : K = ⊤ := by
      apply hmax
      apply (Preorder.lt_iff_le_not_ge _ _).mpr
      apply And.intro
      case a.left =>
        apply Set.le_iff_subset.mpr
        calc (J : Set A)
        _ ⊆ J ∪ {x}:= Set.subset_union_left
        _ ⊆ ideal_closure ((J : Set A) ∪ {x}) :=
          subset_ideal_closure ((J : Set A) ∪ {x})
        _ = K := rfl
      case a.right =>
        intro h
        have hxK : x ∈ (K : Set A) := by
          unfold K
          apply subset_ideal_closure
          right
          rfl
        exact hxJ (h hxK)
    apply Iff.intro
    case mp =>
      intro hxJ
      have hK : K = ⊤ := htop hxJ
      replace hK (y : A) : y ∈ (K : Set A) := by
        rw[hK]
        use y
      unfold K at hK
      replace hK (y : A) : y ∈ {y : A | ∃ (a : ↑J), ∃ (n : Nat), y ≤ (n • x) ⊕ a} := by
        rw[←ideal_closure_union]
        apply hK
      replace hK (y : A) : ∃ (a : ↑J), ∃ (n : Nat), y ≤ (n • x) ⊕ a := by
        apply hK
      have ⟨a,n,hle⟩ := hK 1
      replace ⟨a,haJ⟩ := a
      use n
      replace hle : ((n • x) ⊕ a) = 1 := one_le' hle
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
      let K := ideal_closure ((J : Set A) ∪ {x})
      have heq : J = K := by
        calc (J : MVAlgebra_Ideal A)
        _ = ideal_closure ((J : Set A)) := by rw[ideal_closure_eq]
        _ = ideal_closure ((J : Set A) ∪ {x}) := by
          rw[Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hxJ)]
        _ = (K : MVAlgebra_Ideal A) := by rfl
      apply hntop
      apply top_iff_mem_one.mp
      rw[←oAdd_canc (n • x)]
      refine oAdd_mem ?_ h
      apply smul_mem hxJ
  case mpr =>
    intro h
    apply And.intro
    case left =>
      intro h₂
      replace h₂ := top_iff_mem_one.mpr h₂
      suffices this : 1 ∉ (J : Set A) from by
        exact this h₂
      apply (h 1).mpr
      use 1
      rw[one_smul]
      rw[not_one]
      exact zero_mem
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
      apply top_iff_mem_one.mp
      have hny : y ∉ (J : Set A) := by
        unfold K at hy
        rw[Set.mem_diff] at hy
        apply hy.right
      have ⟨n,h₃⟩ := (h y).mp hny
      replace h₃ := hle.subset h₃
      rw[←oAdd_canc (n • y)]
      refine I.oAdd_mem ?_ h₃
      apply smul_mem
      unfold K at hy
      apply ((Set.mem_diff y).mp hy).left

def isPrime (I : MVAlgebra_Ideal A) : Prop :=
  ∀ {x y : A}, x ⊖ y ∈ (I : Set A) ∨ y ⊖ x ∈ (I : Set A)

class Prime_Ideal A [MVAlgebra A] extends MVAlgebra_Ideal A where
  isPrime' : ∀ {x y : A}, x ⊖ y ∈ carrier ∨ y ⊖ x ∈ carrier

instance (I : MVAlgebra_Ideal A) (h : isPrime I) : Prime_Ideal A where
  isPrime' := h
