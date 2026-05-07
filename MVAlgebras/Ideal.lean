import MVAlgebras.Basic
import MVAlgebras.NaturalOrder
import MVAlgebras.MVAlgebraHom

@[ext]
class MVAlgebra_Ideal (A : Type*) [MVAlgebra A] where
  carrier : Set A
  zero_mem : 0 ∈ carrier
  le_mem {x y : A} : x ∈ carrier → y ≤ x → y ∈ carrier
  oAdd_mem {x y : A} : x ∈ carrier → y ∈ carrier → (x ⊕ y) ∈ carrier

class MVAlgebra_IdealClass (K : Type*) (A : Type*) [MVAlgebra A] extends (SetLike K A) where
  zero_mem' (I : K) : (0 : A) ∈ I
  le_mem' {I : K} {x y : A} : x ∈ I → y ≤ x → y ∈ I
  oAdd_mem' {I : K} {x y : A} : x ∈ I → y ∈ I → (x ⊕ y) ∈ I

open MVAlgebra_Ideal
open MVAlgebra_IdealClass

variable {A B F S T : Type*} [MVAlgebra A] [MVAlgebra B] [MVAlgebra_IdealClass S A]
  [MVAlgebra_IdealClass T B] [MVAlgebraHomClass F A B]

attribute [coe] MVAlgebra_Ideal.carrier

instance : Coe (MVAlgebra_Ideal A) (Set A) where
  coe := (fun (I : MVAlgebra_Ideal A) => I.carrier)

@[reducible]
def MVAlgebra.Ideal.comap (φ : F) (I : T) : MVAlgebra_Ideal A where
  carrier := ⇑φ ⁻¹' ↑I
  zero_mem := by
    rw[Set.mem_preimage]
    rw[map_zero]
    apply zero_mem'
  le_mem := by
    intro x y hx h_le
    exact le_mem' hx (monotone φ h_le)
  oAdd_mem := by
    intro x y
    rw[Set.mem_preimage,Set.mem_preimage,Set.mem_preimage]
    intro hx hy
    rw[map_oAdd]
    exact oAdd_mem' hx hy

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
def inter (I J : MVAlgebra_Ideal A) : MVAlgebra_Ideal A where
  carrier := I ∩ J
  zero_mem := ⟨I.zero_mem,J.zero_mem⟩
  le_mem := by
    intro x y ⟨hxI,hxJ⟩ h_le
    exact ⟨I.le_mem hxI h_le,J.le_mem hxJ h_le⟩
  oAdd_mem := by
    intro x y ⟨hxI,hxJ⟩ ⟨hyI,hyJ⟩
    exact ⟨I.oAdd_mem hxI hyI, J.oAdd_mem hxJ hyJ⟩

instance : PartialOrder (MVAlgebra_Ideal A) where
  le I J := Subset I.carrier J.carrier
  le_refl I := by rfl
  le_antisymm I J := by
    intro h₁ h₂
    ext1
    apply subset_antisymm h₁ h₂
  le_trans I J K := by
    apply subset_trans

instance : BoundedOrder (MVAlgebra_Ideal A) where
  bot := bot
  top := top
  le_top := by
    intro I x _
    use x
  bot_le := by
    intro I x h
    replace h : x = 0 := by exact h
    subst_eqs
    exact I.zero_mem

instance : SemilatticeInf (MVAlgebra_Ideal A) where
  inf := inter
  inf_le_left := by
    intro _ _
    apply Set.inter_subset_left
  inf_le_right := by
    intro _ _
    apply Set.inter_subset_right
  le_inf := by
    intro _ _ _
    apply Set.subset_inter
