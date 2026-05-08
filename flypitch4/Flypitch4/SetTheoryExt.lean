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
