/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/set_theory.lean -/

import Flypitch4.ToMathlib
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Overview

This file ports `src/set_theory.lean` (713 lines).

The **only** symbol used by the sole downstream file (`src/regular_open_algebra.lean`) is:
- `countable_chain_condition` — a `def` in `section CCC`

Everything else in this file is either:
- Internal infrastructure for the delta-system lemma, or
- Infrastructure for the `pi` section used only inside this file.

### Renames (Lean 3 → Lean 4)

1. `is_delta_system` → `IsDeltaSystem`
2. `root_subset` → `rootSubset`
3. `finite_root` → `finiteRoot`
4. `is_delta_system_preimage` → `isDeltaSystem_preimage`
5. `is_delta_system_image` → `isDeltaSystem_image`
6. `is_delta_system_preimage_iff` → `isDeltaSystem_preimage_iff`
7. `is_delta_system_precompose` → `isDeltaSystem_precompose`
8. `is_delta_system_precompose_iff` → `isDeltaSystem_precompose_iff`
9. `set.eq_on'` → `Set.EqOn'`
10. `pairwise_disjoint s` (Lean 3: set-valued) → `s.PairwiseDisjoint id`

### Drops

- `subrel.is_well_order'` was already commented out in the Lean 3 source.
- `set.finite_of_finite_image_of_inj_on` → prefer `Set.Finite.subset`
- `set.countable_of_embedding` → prefer `Set.Countable.mono`

### TODO (sorry-deferred)

The delta-system lemma proofs (`delta_system_lemma_2`, `delta_system_lemma_1`,
`delta_system_lemma`, `delta_system_lemma_uncountable`) involve complex ordinal/cardinal
arithmetic tactics. See `src/set_theory.lean:92-327`.

The `pi` section proofs are also sorry-deferred. See `src/set_theory.lean:442-713`.

`countable_chain_condition_of_separable_space` is sorry-deferred due to API changes in
how dense sets are accessed. See `src/set_theory.lean:416`.

`countable_chain_condition_of_topological_basis` is sorry-deferred due to complex
injection argument. See `src/set_theory.lean:389`.
-/

universe u v w w'

open Set TopologicalSpace Cardinal

noncomputable section

/-! ## Section: delta_system -/

section delta_system

variable {ι : Type w} {ι' : Type w'} {α : Type u} {β : Type v} {A : ι → Set α}

/-- A family of sets `A` is a delta-system (sunflower) if every two distinct sets
    intersect in the same "root" set. -/
def IsDeltaSystem (A : ι → Set α) : Prop :=
  ∃ root : Set α, ∀ ⦃x y⦄, x ≠ y → A x ∩ A y = root

open Cardinal in
def rootSubset (hι : 2 ≤ #ι) {root : Set α} (x : ι)
    (h : ∀ ⦃x y⦄, x ≠ y → A x ∩ A y = root) : root ⊆ A x := by
  rcases (Cardinal.two_le_iff' x).mp hι with ⟨y, hy⟩
  -- hy : y ≠ x, so h hy : A y ∩ A x = root
  have heq : A y ∩ A x = root := h hy
  rw [← heq]; exact inter_subset_right

open Cardinal in
def finiteRoot (hι : 2 ≤ #ι) {root : Set α} (h2A : ∀ x : ι, (A x).Finite)
    (h : ∀ ⦃x y⦄, x ≠ y → A x ∩ A y = root) : root.Finite := by
  rcases Cardinal.two_le_iff.mp hι with ⟨t, u, htu⟩
  have := h htu  -- this : A t ∩ A u = root
  rw [← this]
  exact (h2A t).subset inter_subset_left

open Function in
lemma isDeltaSystem_preimage (f : β → α) (h : IsDeltaSystem A) :
    IsDeltaSystem (preimage f ∘ A) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨f ⁻¹' r, fun x y hxy => ?_⟩
  simp only [Function.comp]
  rw [← preimage_inter]
  exact congr_arg (preimage f) (hr hxy)

open Function in
lemma isDeltaSystem_image {f : α → β} (hf : Function.Injective f) :
    IsDeltaSystem (image f ∘ A) ↔ IsDeltaSystem A := by
  constructor
  · intro h
    have := isDeltaSystem_preimage f h
    convert this using 1
    funext x; simp [preimage_image_eq _ hf]
  · rintro ⟨r, hr⟩
    refine ⟨f '' r, fun x y hxy => ?_⟩
    simp only [Function.comp]
    rw [← image_inter hf]
    exact congr_arg (image f) (hr hxy)

open Function in
lemma isDeltaSystem_preimage_iff {f : β → α} (hf : Function.Injective f)
    (hf₂ : ∀ i, A i ⊆ range f) :
    IsDeltaSystem (preimage f ∘ A) ↔ IsDeltaSystem A := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨f '' r, fun i j hij => ?_⟩
    have hpreimage : f ⁻¹' A i ∩ f ⁻¹' A j = r := by
      have := hr hij
      simpa only [Function.comp] using this
    -- A i ∩ A j = f '' r
    rw [show A i = f '' (f ⁻¹' A i) from (image_preimage_eq_of_subset (hf₂ i)).symm,
        show A j = f '' (f ⁻¹' A j) from (image_preimage_eq_of_subset (hf₂ j)).symm,
        ← image_inter hf, hpreimage]
  · exact isDeltaSystem_preimage f

lemma isDeltaSystem_precompose (f : ι' → ι) (hf : Function.Injective f) (h : IsDeltaSystem A) :
    IsDeltaSystem (A ∘ f) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun x y hxy => hr (fun h => hxy (hf h))⟩

lemma isDeltaSystem_precompose_iff (f : ι' ≃ ι) : IsDeltaSystem A ↔ IsDeltaSystem (A ∘ f) := by
  constructor
  · exact isDeltaSystem_precompose f f.bijective.injective
  · intro h
    have := isDeltaSystem_precompose f.symm f.symm.bijective.injective h
    convert this using 1
    funext i; simp

end delta_system

/-! ## Namespace: delta_system (main theorems) -/

namespace delta_system

open Cardinal Ordinal Order

/-- The core inductive step of the delta-system lemma.
    TODO: port from src/set_theory.lean:92 -/
lemma delta_system_lemma_2 {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    {θ : Type u} (θr : θ → θ → Prop) [θwo : IsWellOrder θ θr] (hκθ : κ < #θ)
    (hθ : Cardinal.IsRegular #θ) (θtype_eq : Cardinal.ord #θ = Ordinal.type θr)
    (hθ_le : ∀ β < #θ, β ^< κ < #θ)
    {ρ : Type u} (ρr : ρ → ρ → Prop) [ρwo : IsWellOrder ρ ρr] (hρ : #ρ < κ)
    {ι : Type u} {A : ι → Set θ} (h2A : ∀ i, ρr ≃r Subrel θr (A i))
    (h3A : Set.Unbounded θr (⋃ i, A i)) :
    ∃ t : Set ι, #t = #θ ∧ IsDeltaSystem (Set.restrict t A) := by
  sorry -- TODO: port from src/set_theory.lean:92

/-- Intermediate step in the delta-system lemma.
    TODO: port from src/set_theory.lean:231 -/
lemma delta_system_lemma_1 {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    {θ : Type u} (θr : θ → θ → Prop) [θwo : IsWellOrder θ θr] (hκθ : κ < #θ)
    (hθ : Cardinal.IsRegular #θ) (θtype_eq : Cardinal.ord #θ = Ordinal.type θr)
    (hθ_le : ∀ β < #θ, β ^< κ < #θ)
    {ρ : Type u} (ρr : ρ → ρ → Prop) [ρwo : IsWellOrder ρ ρr] (hρ : #ρ < κ)
    {ι : Type u} {A : ι → Set θ} (h2A : ∀ i, ρr ≃r Subrel θr (A i)) (hι : #θ = #ι) :
    ∃ t : Set ι, #t = #θ ∧ IsDeltaSystem (Set.restrict t A) := by
  sorry -- TODO: port from src/set_theory.lean:231

/-- The delta-system lemma. [Kunen 1980, Theorem 1.6, p49]
    TODO: port from src/set_theory.lean:258 -/
theorem delta_system_lemma {α ι : Type u} {κ θ : Cardinal} (hκ : ℵ₀ ≤ κ) (hκθ : κ < θ)
    (hθ : Cardinal.IsRegular θ) (hθ_le : ∀ c < θ, c ^< κ < θ) (A : ι → Set α)
    (hA : θ ≤ #ι) (h2A : ∀ i, #(A i) < κ) :
    ∃ t : Set ι, #t = θ ∧ IsDeltaSystem (Set.restrict t A) := by
  sorry -- TODO: port from src/set_theory.lean:258

/-- Uncountable version of the delta-system lemma.
    TODO: port from src/set_theory.lean:308 -/
theorem delta_system_lemma_uncountable {α : Type u} {ι : Type v}
    (A : ι → Set α) (h : ℵ₀ < #ι) (h2A : ∀ i, (A i).Finite) :
    ∃ t : Set ι, ℵ₀ < #t ∧ IsDeltaSystem (Set.restrict t A) := by
  sorry -- TODO: port from src/set_theory.lean:308

end delta_system

/-! ## Namespace: set (helpers) -/

namespace Set

variable {α β : Type u}

/-- Equality on a dependent function restricted to a set. Lean 3: `set.eq_on'`. -/
def EqOn' {α : Type*} {β : α → Type*} (f g : ∀ x, β x) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x = g x

lemma eqOn'_iff {α : Type*} {β : α → Type*} (f g : ∀ x, β x) (s : Set α) :
    EqOn' f g s ↔ Set.restrict s f = Set.restrict s g := by
  constructor
  · intro h; funext ⟨x, hx⟩; exact h hx
  · intro h x hx; exact congr_fun h ⟨x, hx⟩

end Set

/-! ## Section: CCC (Countable Chain Condition) -/

section CCC

variable (α : Type u) [TopologicalSpace α]

/-- The countable chain condition: every pairwise disjoint family of open sets is countable.
    Lean 3 `pairwise_disjoint s` (for `s : Set (Set α)`) maps to `s.PairwiseDisjoint id`. -/
def countable_chain_condition : Prop :=
  ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → IsOpen o) → s.PairwiseDisjoint id → s.Countable

variable {α}

lemma countable_chain_condition_of_nonempty
    (h : ∀ s : Set (Set α), (∀ ⦃o⦄, o ∈ s → o ≠ ∅) → (∀ ⦃o⦄, o ∈ s → IsOpen o) →
      s.PairwiseDisjoint id → s.Countable) : countable_chain_condition α := by
  intro s open_s hs
  let s' : Set (Set α) := s \ {∅}
  have hs' : ∀ ⦃o : Set α⦄, o ∈ s' → o ≠ ∅ := fun o ho h2o => ho.2 (by rw [mem_singleton_iff, h2o])
  have open_s' : ∀ ⦃o : Set α⦄, o ∈ s' → IsOpen o := fun o ho => open_s ho.1
  have h2s' : s'.PairwiseDisjoint id := hs.subset diff_subset
  have hcountable : s'.Countable := h s' hs' open_s' h2s'
  exact (hcountable.insert ∅).mono (by rw [insert_diff_singleton]; exact subset_insert _ _)

/-- TODO: fill in proof; relies on injectivity argument for topological basis.
    See src/set_theory.lean:389. -/
lemma countable_chain_condition_of_topological_basis (B : Set (Set α))
    (hB : IsTopologicalBasis B)
    (h : ∀ s : Set (Set α), s ⊆ B → s.PairwiseDisjoint id → s.Countable) :
    countable_chain_condition α := by
  sorry -- TODO: port from src/set_theory.lean:389

/-- In a separable space, the CCC holds.
    Proof sketch: use dense countable set D to pick one d ∈ D ∩ o for each open nonempty o ∈ s,
    giving an injection s \ {∅} ↪ D. Full port is TODO.
    See src/set_theory.lean:416. -/
lemma countable_chain_condition_of_separable_space [SeparableSpace α] :
    countable_chain_condition α := by
  sorry -- TODO: port from src/set_theory.lean:416

lemma countable_chain_condition_of_countable (h : #α ≤ ℵ₀) : countable_chain_condition α := by
  haveI : Countable α := Cardinal.mk_le_aleph0_iff.mp h
  haveI : SeparableSpace α := inferInstance
  exact countable_chain_condition_of_separable_space

end CCC

/-! ## Section: pi (product topology) -/

section pi

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]

/-- A basic open set in the product topology depending only on coordinate `i`. -/
def standard_open {i : α} (o : TopologicalSpace.Opens (β i)) : Set (∀ x, β x) :=
  {f : ∀ x, β x | f i ∈ o}

variable (β)

/-- The subbasis of the product topology. -/
def pi_subbasis : Set (Set (∀ x, β x)) :=
  range (fun x : Σ i : α, TopologicalSpace.Opens (β i) => standard_open x.2)

variable {β}

variable (β)

lemma is_subbasis_pi : Pi.topologicalSpace = generateFrom (pi_subbasis β) := by
  sorry -- TODO: port from src/set_theory.lean:457

/-- The basis of the product topology consisting of finite intersections of subbasis elements. -/
def pi_basis : Set (Set (∀ x, β x)) :=
  (fun f => ⋂₀ f) '' {f : Set (Set (∀ x, β x)) | f.Finite ∧ f ⊆ pi_subbasis β ∧ ⋂₀ f ≠ ∅}

lemma pi_basis_eq : pi_basis β =
    {g | ∃ (s : ∀ x, Set (β x)) (i : Finset α), (∀ x ∈ i, IsOpen (s x)) ∧ g = Set.pi ↑i s} \ {∅} := by
  sorry -- TODO: port from src/set_theory.lean:469

variable {β}

lemma nonempty_of_mem_pi_basis {o : Set (∀ x, β x)} (h : o ∈ pi_basis β) : o.Nonempty := by
  rcases h with ⟨_, ho, rfl⟩
  exact nonempty_iff_ne_empty.mpr ho.2.2

variable (β)

lemma is_topological_basis_pi : IsTopologicalBasis (pi_basis β) := by
  sorry -- TODO: port from src/set_theory.lean:552
  -- In Lean 3: is_topological_basis_of_subbasis (is_subbasis_pi β)
  -- In Lean 4: isTopologicalBasis_of_subbasis generates a different set, needs adjustment

variable {β}

lemma is_open_map_apply (i : α) : IsOpenMap (fun f : ∀ i, β i => f i) := by
  sorry -- TODO: port from src/set_theory.lean:558

lemma restrict_image_pi (t : Set α) (s : Set α) (s' : ∀ i, Set (β i))
    (h : (Set.pi t s').Nonempty) :
    (fun f : ∀ i, β i => Set.restrict s f) '' Set.pi t s' =
      Set.pi (Subtype.val ⁻¹' t) (fun i => s' i.1) := by
  sorry -- TODO: port from src/set_theory.lean:568

lemma is_open_map_restrict (s : Set α) : IsOpenMap (fun f : ∀ i, β i => Set.restrict s f) := by
  sorry -- TODO: port from src/set_theory.lean:583

/-- The support of a set `o` in the product topology: the indices that actually matter. -/
def support (o : Set (∀ x, β x)) : Set α :=
  ⋂₀ {s : Set α | ∀ ⦃f g : ∀ i, β i⦄, Set.EqOn' f g s → f ∈ o → g ∈ o}

lemma support_pi (i : Set α) (s : ∀ x, Set (β x)) (h : (Set.pi i s).Nonempty) :
    support (Set.pi i s) = {x ∈ i | s x ≠ Set.univ} := by
  sorry -- TODO: port from src/set_theory.lean:605

lemma support_elim {o : Set (∀ x, β x)} {f g : ∀ x, β x} (ho : o ∈ pi_basis β)
    (h : Set.EqOn' f g (support o)) (hf : f ∈ o) : g ∈ o := by
  sorry -- TODO: port from src/set_theory.lean:625

lemma finite_support_of_pi_subbasis {o : Set (∀ x, β x)} (h : o ∈ pi_subbasis β) :
    (support o).Finite := by
  sorry -- TODO: port from src/set_theory.lean:635

lemma finite_support_of_pi_basis {o : Set (∀ x, β x)} (h : o ∈ pi_basis β) :
    (support o).Finite := by
  sorry -- TODO: port from src/set_theory.lean:644

/-- Extend a function `g₁` on `s` and `g₂` off `s`. -/
noncomputable def extend (g₁ g₂ : ∀ x, β x) (s : Set α) (x : α) : β x :=
  haveI : Decidable (x ∈ s) := Classical.dec _
  if x ∈ s then g₁ x else g₂ x

open delta_system in
theorem countable_chain_condition_pi
    (h : ∀ s : Set α, s.Finite → countable_chain_condition (∀ x : s, β x)) :
    countable_chain_condition (∀ x, β x) := by
  sorry -- TODO: port from src/set_theory.lean:662

end pi

end -- noncomputable section
