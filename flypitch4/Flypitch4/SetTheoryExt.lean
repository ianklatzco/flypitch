/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/set_theory.lean -/

import Flypitch4.ToMathlib
import Mathlib.Topology.Bases

/-! ## Lean 3 → Lean 4 Port: scope-narrowed slice of `src/set_theory.lean`

The original Lean 3 `set_theory.lean` (713 lines) bundles two largely independent
chunks of infrastructure:

1. **The delta-system lemma** and its supporting machinery (lines 1–388).
2. **CCC (Countable Chain Condition)** plus the **product topology** section
   (lines 389–713).

Cross-flypitch grep confirms only **two** symbols from this file are used by any
other Lean 3 source:

- `countable_chain_condition` — used by `src/regular_open_algebra.lean`.
- `countable_chain_condition_pi` — called once at `src/cantor_space.lean:436`.

Everything else (`is_delta_system` and friends, the `delta_system_lemma_*`
theorems, `pi_basis`, `pi_subbasis`, `support`, `extend`, `eq_on'`, …) is
internal scaffolding that the Lean 3 authors wrote but never ended up using on
the path to `independence_of_CH`. It has been dropped from the port.

If a future port needs the dropped material, the Lean 3 source remains
verbatim in `src/set_theory.lean` as a reference.

### Renames (Lean 3 → Lean 4)

- `pairwise_disjoint s` (set-valued, Lean 3) → `s.PairwiseDisjoint id`

### TODO (sorry-deferred, on the critical path)

- `countable_chain_condition_pi` — needed by the port of `cantor_space.lean`.
  Statement is uncontroversial; the proof requires the (dropped) `pi_basis`/
  `support` infrastructure. Either reconstruct that infrastructure or rebind
  to a mathlib4 equivalent at the time `cantor_space` is ported.
-/

universe u v

open Set TopologicalSpace Cardinal

/-! ## CCC: Countable Chain Condition -/

section CCC

variable (α : Type u) [TopologicalSpace α]

/-- The countable chain condition: every pairwise disjoint family of open sets is countable. -/
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

/-- In a separable space, the CCC holds. -/
lemma countable_chain_condition_of_separable_space [SeparableSpace α] :
    countable_chain_condition α := by
  intro s open_s hs
  suffices h : (s \ {(∅ : Set α)}).Countable by
    have hsub : s ⊆ insert (∅ : Set α) (s \ {∅}) := by
      intro o ho
      rcases eq_or_ne o ∅ with rfl | hne
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨ho, fun h => hne (Set.mem_singleton_iff.mp h)⟩)
    exact (h.insert ∅).mono hsub
  apply Set.PairwiseDisjoint.countable_of_isOpen (s := id) (a := s \ {(∅ : Set α)})
  · intro o ⟨ho, _⟩ o' ⟨ho', _⟩ hne
    exact hs ho ho' hne
  · intro o ⟨ho, _⟩; exact open_s ho
  · intro o ⟨_, hne⟩
    exact Set.nonempty_iff_ne_empty.mpr (fun h => hne (Set.mem_singleton_iff.mpr h))

lemma countable_chain_condition_of_countable (h : #α ≤ ℵ₀) : countable_chain_condition α := by
  haveI : Countable α := Cardinal.mk_le_aleph0_iff.mp h
  haveI : SeparableSpace α := inferInstance
  exact countable_chain_condition_of_separable_space

/-- CCC is preserved when we can witness it on a topological basis. -/
lemma countable_chain_condition_of_topological_basis (B : Set (Set α))
    (hB : IsTopologicalBasis B)
    (h : ∀ s : Set (Set α), s ⊆ B → s.PairwiseDisjoint id → s.Countable) :
    countable_chain_condition α := by
  apply countable_chain_condition_of_nonempty
  intro s s_nonempty s_open hs
  -- For each x ∈ s, choose a non-empty basis element b ⊆ x.
  have hpick : ∀ x : s, ∃ b : Set α, b ∈ B ∧ b ≠ ∅ ∧ b ⊆ x.1 := by
    rintro ⟨x, hx⟩
    have hxne : x.Nonempty := Set.nonempty_iff_ne_empty.mpr (s_nonempty hx)
    obtain ⟨y, hy⟩ := hxne
    obtain ⟨b, hbB, hyb, hbx⟩ := hB.isOpen_iff.mp (s_open hx) y hy
    refine ⟨b, hbB, ?_, hbx⟩
    intro hbe; rw [hbe] at hyb; exact hyb
  choose f hfB hfne hfsub using hpick
  -- s' = range of f.
  let s' : Set (Set α) := Set.range f
  have hs'B : s' ⊆ B := by rintro _ ⟨x, rfl⟩; exact hfB x
  have hs'pd : s'.PairwiseDisjoint id := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    have hxy' : x ≠ y := by
      rintro rfl; exact hne rfl
    have h1 : (x : Set α) ≠ y := fun h => hxy' (Subtype.ext h)
    exact (hs x.2 y.2 h1).mono (hfsub x) (hfsub y)
  have hs'count : s'.Countable := h s' hs'B hs'pd
  -- Now f : s → s' is injective: f x non-empty subset of both x.1 and y.1
  -- forces x.1 = y.1 (else they would be disjoint).
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hxy' : (x : Set α) ≠ y := fun h => hne (Subtype.ext h)
    have hd : Disjoint (x : Set α) (y : Set α) := hs x.2 y.2 hxy'
    have : (f x).Nonempty := Set.nonempty_iff_ne_empty.mpr (hfne x)
    obtain ⟨z, hz⟩ := this
    have hzx : z ∈ (x : Set α) := hfsub x hz
    have hzy : z ∈ (y : Set α) := hfsub y (hxy ▸ hz)
    have : ¬ Disjoint (x : Set α) (y : Set α) := by
      rw [Set.not_disjoint_iff]; exact ⟨z, hzx, hzy⟩
    exact this hd
  -- Therefore s.Countable, since f : s → s' is injective.
  have hs_count : s.Countable := by
    have hsub : Countable (Set.range f) := hs'count.to_subtype
    have : Countable s := by
      have hf' : Function.Injective (fun x : s => (⟨f x, Set.mem_range_self x⟩ : Set.range f)) := by
        intro x y hxy
        exact hf_inj (Subtype.ext_iff.mp hxy)
      exact hf'.countable
    exact Set.countable_coe_iff.mp this
  exact hs_count

end CCC

/-! ## CCC for product topologies (sorry-deferred — fill in when porting `cantor_space.lean`) -/

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]

theorem countable_chain_condition_pi
    (h : ∀ s : Set α, s.Finite → countable_chain_condition (∀ x : s, β x)) :
    countable_chain_condition (∀ x, β x) := by
  -- TODO: port from src/set_theory.lean:662.
  -- The Lean 3 proof depends on a large body of dropped infrastructure
  -- (`pi_basis`, `pi_subbasis`, `support`, `extend`, `eq_on'`,
  -- `delta_system_lemma_uncountable`, `finite_root`, …) — roughly
  -- src/set_theory.lean lines 92–660. Reconstructing all of it is a
  -- multi-day port (the Δ-system lemma alone is ~200 lines of nontrivial
  -- well-founded combinatorics). A grep of mathlib4 (as of 2026-05-08)
  -- finds no equivalents for `Sunflower`/`DeltaSystem` or for a CCC-pi
  -- theorem under any naming, so there is no short path through mathlib.
  -- Until the infrastructure is reconstructed, this lemma is sorry-deferred;
  -- the only downstream consumer is `CantorSpace.countable_chain_condition_set`
  -- (and through it `Forcing.lean:243`).
  sorry
