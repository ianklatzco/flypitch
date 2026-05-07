/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/cantor_space.lean (446 lines). -/

import Flypitch4.RegularOpenAlgebra
import Mathlib.Topology.Clopen
import Mathlib.Topology.Constructions
import Mathlib.Topology.Bases
import Mathlib.SetTheory.Cardinal.Basic

open Set TopologicalSpace

universe u v

/-! ## Global topology on `Set α` -/

/-- Discrete topology on `Prop` (⊥ = discrete in Lean 4 = all sets open). -/
@[implicit_reducible] instance Prop_space : TopologicalSpace Prop := ⊥

instance discrete_Prop : DiscreteTopology Prop := ⟨rfl⟩

/-- The product (Pi) topology on `Set α = α → Prop`,
using the discrete topology on each `Prop` factor. -/
@[implicit_reducible] instance product_topology {α : Type*} : TopologicalSpace (Set α) :=
  Pi.topologicalSpace

lemma eq_true_of_provable {p : Prop} (h : p) : p = True :=
  propext (Iff.intro (fun _ => trivial) (fun _ => h))

lemma eq_false_of_provable_neg {p : Prop} (h : ¬p) : p = False :=
  propext (Iff.intro h False.elim)

@[reducible, simp] noncomputable def Prop_to_bool (p : Prop) : Bool :=
  haveI := Classical.propDecidable p; decide p

@[simp] lemma Prop_to_bool_true : Prop_to_bool True = true := by
  simp [Prop_to_bool]

@[simp] lemma Prop_to_bool_false : Prop_to_bool False = false := by
  simp [Prop_to_bool]

noncomputable def equiv_Prop_bool : Equiv Prop Bool where
  toFun := Prop_to_bool
  invFun := fun b => b = true
  left_inv := fun p => by
    simp only [Prop_to_bool]
    haveI := Classical.propDecidable p
    by_cases h : p <;> simp [h]
  right_inv := fun b => by
    cases b <;> simp [Prop_to_bool]

noncomputable instance Prop_encodable : Encodable Prop :=
  Encodable.ofEquiv Bool equiv_Prop_bool

instance Prop_separable : SeparableSpace Prop where
  exists_countable_dense := ⟨Set.univ, Set.countable_univ, dense_univ⟩

lemma is_open_of_compl_closed {α : Type*} [TopologicalSpace α] {S : Set α}
    (H : IsClosed Sᶜ) : IsOpen S := by
  rw [← compl_compl S]; exact isOpen_compl_iff.mpr H

lemma is_closed_of_compl_open {α : Type*} [TopologicalSpace α] {S : Set α}
    (H : IsOpen Sᶜ) : IsClosed S :=
  isOpen_compl_iff.mp H

/-- The type of clopen sets in a topological space. -/
def Clopens (α : Type u) [TopologicalSpace α] : Type u := {S : Set α // IsClopen S}

instance clopens_lattice {α : Type u} [TopologicalSpace α] : Lattice (Clopens α) where
  sup := fun S₁ S₂ => ⟨S₁.1 ∪ S₂.1, S₁.2.union S₂.2⟩
  le := fun S₁ S₂ => S₁.1 ⊆ S₂.1
  le_refl := fun _ => Set.Subset.refl _
  le_trans := fun _ _ _ h1 h2 => Set.Subset.trans h1 h2
  le_antisymm := fun a b h1 h2 => Subtype.ext (Set.Subset.antisymm h1 h2)
  le_sup_left := fun S₁ _ _ hx => Set.mem_union_left _ hx
  le_sup_right := fun _ S₂ _ hx => Set.mem_union_right _ hx
  sup_le := fun _ _ _ h1 h2 _ hx => hx.elim (h1 ·) (h2 ·)
  inf := fun S₁ S₂ => ⟨S₁.1 ∩ S₂.1, S₁.2.inter S₂.2⟩
  inf_le_left := fun _ _ _ hx => hx.1
  inf_le_right := fun _ _ _ hx => hx.2
  le_inf := fun _ _ _ h1 h2 _ hx => ⟨h1 hx, h2 hx⟩

instance clopens_order_top {α : Type u} [TopologicalSpace α] : OrderTop (Clopens α) where
  top := ⟨Set.univ, isClopen_univ⟩
  le_top := fun _ _ _ => trivial

instance clopens_order_bot {α : Type u} [TopologicalSpace α] : OrderBot (Clopens α) where
  bot := ⟨∅, isClopen_empty⟩
  bot_le := fun _ _ hx => False.elim hx

/-- A finite intersection of clopen sets (via Finset.inf and a function) is clopen. -/
lemma is_clopen_finite_inter' {α : Type u} [TopologicalSpace α]
    {α' : Type v} {X : Finset α'} {f : α' → Set α}
    (H_f : ∀ x ∈ X, IsClopen (f x)) : IsClopen (X.inf f) := by
  classical
  revert H_f
  induction X using Finset.induction with
  | empty => intro _; simp only [Finset.inf_empty]; exact isClopen_univ
  | insert _ _ =>
    rename_i a A ha ih
    intro H_f
    rw [Finset.inf_insert]
    apply IsClopen.inter
    · exact H_f _ (Finset.mem_insert_self _ _)
    · apply ih; intro x hx; exact H_f x (Finset.mem_insert_of_mem hx)

lemma is_clopen_finite_inter {α : Type u} [TopologicalSpace α] {X : Finset (Set α)}
    (H_X : ∀ S ∈ X, IsClopen S) : IsClopen (X.inf id) :=
  is_clopen_finite_inter' H_X

/-! ## CantorSpace namespace -/

namespace CantorSpace

variable {α : Type u}

/-- The basic open set: all sets containing a given element. -/
def principalOpen (x : α) : Set (Set α) := {S | x ∈ S}

/-- The basic open set: all sets not containing a given element. -/
def coPrincipalOpen (x : α) : Set (Set α) := {S | x ∉ S}

@[simp] lemma neg_principalOpen {x : α} : coPrincipalOpen x = (principalOpen x)ᶜ := by
  ext S; simp [principalOpen, coPrincipalOpen]

@[simp] lemma neg_coPrincipalOpen {x : α} : (coPrincipalOpen x)ᶜ = principalOpen x := by
  ext S; simp [principalOpen, coPrincipalOpen]

/-- The four-element subbasis for the topology at projection `x`. -/
def opensOver (x : α) : Set (Set (Set α)) :=
  {principalOpen x, coPrincipalOpen x, Set.univ, ∅}

@[simp] lemma principalOpen_mem_opensOver {x : α} : principalOpen x ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

@[simp] lemma coPrincipalOpen_mem_opensOver {x : α} : coPrincipalOpen x ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

@[simp] lemma univ_mem_opensOver {x : α} : Set.univ ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

@[simp] lemma empty_mem_opensOver {x : α} : (∅ : Set (Set α)) ∈ opensOver x := by
  simp [opensOver, Set.mem_insert_iff]

/-- The topology induced by pulling back the discrete topology on Prop along the `a`-th projection. -/
@[reducible] def τ (a : α) : TopologicalSpace (Set α) :=
  @TopologicalSpace.induced (Set α) Prop (fun S => a ∈ S) Prop_space

lemma fiber_over_false {a : α} :
    (fun x : Set α => a ∈ x) ⁻¹' {False} = {y | a ∉ y} := by
  ext; simp [Set.mem_preimage, Set.mem_setOf_eq]

lemma fiber_over_true {a : α} :
    (fun x : Set α => a ∈ x) ⁻¹' {True} = {y | a ∈ y} := by
  ext; simp [Set.mem_preimage, Set.mem_setOf_eq]

/-- The four basic open sets of `opensOver a` are open in `τ a`. -/
lemma opensOver_sub_τ (a : α) : opensOver a ⊆ {S | (τ a).IsOpen S} := by
  intro S HS
  simp only [opensOver, Set.mem_insert_iff, Set.mem_singleton_iff] at HS
  rcases HS with rfl | rfl | rfl | rfl
  · -- principalOpen a: preimage of {True} under (a ∈ ·)
    show @IsOpen (Set α) (@TopologicalSpace.induced (Set α) Prop (fun S => a ∈ S) Prop_space)
      (principalOpen a)
    rw [isOpen_induced_iff]
    exact ⟨{True}, isOpen_discrete _, Set.ext (fun _ => by simp [principalOpen])⟩
  · -- coPrincipalOpen a: preimage of {False}
    show @IsOpen (Set α) (@TopologicalSpace.induced (Set α) Prop (fun S => a ∈ S) Prop_space)
      (coPrincipalOpen a)
    rw [isOpen_induced_iff]
    exact ⟨{False}, isOpen_discrete _, Set.ext (fun _ => by simp [coPrincipalOpen])⟩
  · exact @isOpen_univ _ (τ a)
  · exact @isOpen_empty _ (τ a)

/-- `τ a` is coarser than the topology generated by `opensOver a` (since opensOver ⊆ opens of τ a). -/
lemma opensOver_le_τ (a : α) : τ a ≤ generateFrom (opensOver a) := by
  rw [le_generateFrom_iff_subset_isOpen]
  exact opensOver_sub_τ a

/-- The product topology on `Set α` is coarser than each factor topology `τ a`. -/
lemma τ_le_product_topology (a : α) :
    (product_topology : TopologicalSpace (Set α)) ≤ τ a := by
  show (Pi.topologicalSpace : TopologicalSpace (Set α)) ≤ τ a
  unfold τ Pi.topologicalSpace
  exact iInf_le (fun i => @TopologicalSpace.induced (Set α) Prop
    (fun S => i ∈ S) Prop_space) a

/-- `generateFrom (opensOver a)` is coarser than `τ a` (they are actually equal). -/
lemma τ_le_opensOver (a : α) : generateFrom (opensOver a) ≤ τ a := by
  sorry -- TODO: port from src/cantor_space.lean:178

@[simp] lemma isOpen_generated_from_basic {β : Type*} [TopologicalSpace β]
    {s : Set (Set β)} {x : Set β} (hx : x ∈ s) : (generateFrom s).IsOpen x :=
  isOpen_generateFrom_of_mem hx

/-- `principalOpen a` is open in the product topology. -/
lemma isOpen_principalOpen {a : α} : IsOpen (principalOpen a) := by
  -- principalOpen a ∈ opensOver a ⊆ opens(τ a)
  -- τ a ≤ generateFrom(opensOver a)
  -- product_topology ≤ τ a
  -- so product_topology ≤ generateFrom(opensOver a)
  -- and principalOpen a ∈ generateFrom(opensOver a) (it's a basic open)
  -- so it's open in product_topology (which has more opens in Lean 4's order)
  apply (le_trans (τ_le_product_topology _) (opensOver_le_τ a))
  exact isOpen_generateFrom_of_mem (principalOpen_mem_opensOver)

/-- `coPrincipalOpen a` is open in the product topology. -/
lemma isOpen_coPrincipalOpen {a : α} : IsOpen (coPrincipalOpen a) := by
  apply (le_trans (τ_le_product_topology _) (opensOver_le_τ a))
  exact isOpen_generateFrom_of_mem (coPrincipalOpen_mem_opensOver)

lemma isClosed_principalOpen {a : α} : IsClosed (principalOpen a) :=
  is_closed_of_compl_open (neg_principalOpen ▸ isOpen_coPrincipalOpen)

lemma isClosed_coPrincipalOpen {a : α} : IsClosed (coPrincipalOpen a) :=
  is_closed_of_compl_open (neg_coPrincipalOpen ▸ isOpen_principalOpen)

lemma isClopen_principalOpen {a : α} : IsClopen (principalOpen a) :=
  ⟨isClosed_principalOpen, isOpen_principalOpen⟩

lemma isClopen_coPrincipalOpen {a : α} : IsClopen (coPrincipalOpen a) :=
  ⟨isClosed_coPrincipalOpen, isOpen_coPrincipalOpen⟩

@[reducible] def principalOpenFinset (F : Finset α) : Set (Set α) :=
  {S | (↑F : Set α) ⊆ S}

lemma mem_principalOpenFinset_iff {F : Finset α} {x : Set α} :
    x ∈ principalOpenFinset F ↔ (↑F : Set α) ⊆ x := Iff.rfl

@[simp] lemma principalOpenFinset_insert [DecidableEq α] {F : Finset α} {a : α} :
    principalOpenFinset (insert a F) = principalOpenFinset {a} ∩ principalOpenFinset F := by
  ext x
  simp only [principalOpenFinset, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_insert, Set.insert_subset_iff]

lemma principalOpenFinset_eq_inter [DecidableEq α] (F : Finset α) :
    principalOpenFinset F = F.inf principalOpen := by
  induction F using Finset.induction with
  | empty => ext x; simp [principalOpenFinset, Finset.inf_empty]
  | insert _ _ =>
    rename_i a A ha ih
    rw [Finset.inf_insert, ← ih]
    ext x
    simp only [principalOpenFinset, principalOpen, Set.mem_setOf_eq,
      Finset.coe_insert, Set.insert_subset_iff]
    simp [Set.mem_inter_iff, Set.mem_setOf_eq]

@[reducible] def coPrincipalOpenFinset (F : Finset α) : Set (Set α) :=
  {S | (↑F : Set α) ⊆ Sᶜ}

@[simp] lemma coPrincipalOpenFinset_insert [DecidableEq α] {F : Finset α} {a : α} :
    coPrincipalOpenFinset (insert a F) = coPrincipalOpenFinset {a} ∩ coPrincipalOpenFinset F := by
  ext x
  simp only [coPrincipalOpenFinset, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_insert, Set.insert_subset_iff]

lemma coPrincipalOpenFinset_eq_inter [DecidableEq α] (F : Finset α) :
    coPrincipalOpenFinset F = F.inf coPrincipalOpen := by
  induction F using Finset.induction with
  | empty => ext x; simp [coPrincipalOpenFinset, Finset.inf_empty]
  | insert _ _ =>
    rename_i a A ha ih
    rw [Finset.inf_insert, ← ih]
    ext x
    simp only [coPrincipalOpenFinset, coPrincipalOpen, Set.mem_setOf_eq,
      Finset.coe_insert, Set.insert_subset_iff]
    simp [Set.mem_inter_iff, Set.mem_setOf_eq]

lemma isClopen_principalOpenFinset [DecidableEq α] (F : Finset α) :
    IsClopen (principalOpenFinset F) := by
  rw [principalOpenFinset_eq_inter]
  exact is_clopen_finite_inter' (fun _ _ => isClopen_principalOpen)

lemma isClopen_coPrincipalOpenFinset [DecidableEq α] (F : Finset α) :
    IsClopen (coPrincipalOpenFinset F) := by
  rw [coPrincipalOpenFinset_eq_inter]
  exact is_clopen_finite_inter' (fun _ _ => isClopen_coPrincipalOpen)

lemma product_topology_generate_from :
    (product_topology : TopologicalSpace (Set α)) = generateFrom (⋃ a : α, opensOver a) := by
  sorry -- TODO: port from src/cantor_space.lean:274

/-- The standard basis for the product topology on `Set α`. -/
def standardBasis : Set (Set (Set α)) :=
  {T : Set (Set α) | ∃ p_ins p_out : Finset α,
    T = (p_ins.inf principalOpen) ∩ (p_out.inf coPrincipalOpen) ∧
    Disjoint p_ins p_out} ∪ {∅}

lemma ins₁_out₂_disjoint [DecidableEq α] {x : Set α}
    {p_ins₁ p_out₁ p_ins₂ p_out₂ : Finset α}
    (H_mem₁ : x ∈ p_ins₁.inf principalOpen ∩ p_out₁.inf coPrincipalOpen)
    (H_mem₂ : x ∈ p_ins₂.inf principalOpen ∩ p_out₂.inf coPrincipalOpen)
    (H_disjoint₁ : Disjoint p_ins₁ p_out₁)
    (H_disjoint₂ : Disjoint p_ins₂ p_out₂)
    {a : α} (Ha_left : a ∈ p_ins₁) (Ha_right : a ∈ p_out₂) : False := by
  rw [← principalOpenFinset_eq_inter, ← coPrincipalOpenFinset_eq_inter] at H_mem₁ H_mem₂
  have hmem₁ := (Set.mem_inter_iff _ _ _).mp H_mem₁
  have hmem₂ := (Set.mem_inter_iff _ _ _).mp H_mem₂
  exact hmem₂.2 Ha_right (hmem₁.1 Ha_left)

@[simp] lemma principalOpen_mem_standardBasis {a : α} :
    principalOpen a ∈ @standardBasis α := by
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  left
  classical
  exact ⟨{a}, ∅, by simp [Finset.inf_singleton], by simp⟩

@[simp] lemma coPrincipalOpen_mem_standardBasis {a : α} :
    coPrincipalOpen a ∈ @standardBasis α := by
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  left
  classical
  exact ⟨∅, {a}, by simp [Finset.inf_singleton], by simp⟩

lemma univ_mem_standardBasis : Set.univ ∈ @standardBasis α := by
  simp only [standardBasis, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  left
  exact ⟨∅, ∅, by simp [Finset.inf_empty], by simp⟩

lemma intersection_standardBasis_nonempty' [DecidableEq α] {p_ins p_out : Finset α}
    (H : Disjoint p_ins p_out) :
    ∃ X, X ∈ p_ins.inf principalOpen ∩ p_out.inf coPrincipalOpen := by
  use (↑p_ins : Set α)
  rw [← principalOpenFinset_eq_inter, ← coPrincipalOpenFinset_eq_inter]
  simp only [principalOpenFinset, coPrincipalOpenFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨Set.Subset.refl _, ?_⟩
  -- Need: ↑p_out ⊆ (↑p_ins)ᶜ
  -- i.e., for all y ∈ p_out, y ∉ p_ins
  -- This follows from Disjoint p_ins p_out
  intro y hy_out hy_ins
  exact Finset.disjoint_right.mp H (Finset.mem_coe.mp hy_out) (Finset.mem_coe.mp hy_ins)

lemma intersection_standardBasis_nonempty {T : Set (Set α)} {p_ins p_out : Finset α}
    {H_eq : T = p_ins.inf principalOpen ∩ p_out.inf coPrincipalOpen}
    {H : Disjoint p_ins p_out} :
    ¬⋂₀ (↑(p_ins.image principalOpen ∪ p_out.image coPrincipalOpen) :
      Set (Set (Set α))) = ∅ := by
  sorry -- TODO: port from src/cantor_space.lean:318

lemma standard_basis_reindex {T : Set (Set α)} {p_ins p_out : Finset α}
    {H_eq : T = p_ins.inf principalOpen ∩ p_out.inf coPrincipalOpen}
    {H : Disjoint p_ins p_out} :
    ⋂₀ (↑(p_ins.image principalOpen ∪ p_out.image coPrincipalOpen) :
      Set (Set (Set α))) = T := by
  sorry -- TODO: port from src/cantor_space.lean:329

lemma is_topological_basis_standardBasis :
    @IsTopologicalBasis (Set α) _ standardBasis := by
  sorry -- TODO: port from src/cantor_space.lean:346

open Cardinal

lemma countable_chain_condition_set {α : Type u} :
    countable_chain_condition (Set α) := by
  apply countable_chain_condition_pi
  intro s hs
  apply countable_chain_condition_of_countable
  apply le_of_lt
  -- |∀ x : s, Set α| = |∀ x : s, α → Prop| which for finite s is ≤ 2^|s| < ω
  sorry -- TODO: port from src/cantor_space.lean:434

end CantorSpace
