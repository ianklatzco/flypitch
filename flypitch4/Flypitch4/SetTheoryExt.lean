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

/-! ## Δ-system lemma (uncountable case, for finite-set families) -/

/-- A family of sets `A : ι → Set α` forms a Δ-system (sunflower) with root `r`
if every pair of distinct values intersects exactly in `r`. -/
def IsDeltaSystem {ι : Type*} {α : Type*} (A : ι → Set α) : Prop :=
  ∃ root : Set α, ∀ ⦃x y : ι⦄, x ≠ y → A x ∩ A y = root

/-- The Δ-system lemma at `ω₁`: any uncountably-indexed family of finite sets
contains an uncountable Δ-subsystem. (Lean 3 source:
`src/set_theory.lean:308 (delta_system_lemma_uncountable)`.)

The Lean 3 proof goes via a much more general regular-cardinal version (~250
lines of cardinal arithmetic). Porting it is left as a follow-up — for the
single CCC-pi consumer below we use it as a black box. -/
theorem delta_system_lemma_aleph1
    {α : Type u} {ι : Type v} (A : ι → Set α)
    (hι : ℵ₀ < #ι) (h2A : ∀ i, (A i).Finite) :
    ∃ t : Set ι, ℵ₀ < #t ∧ IsDeltaSystem (fun i : t => A i.1) := by
  -- TODO: port src/set_theory.lean:308 (delta_system_lemma_uncountable).
  sorry

/-! ## CCC for product topologies -/

variable {α : Type u} {β : α → Type v} [∀ x, TopologicalSpace (β x)]

/-- The standard pi-basis from mathlib's `isTopologicalBasis_pi`, instantiated
to allow any open set as the per-coordinate basis. -/
private def piOpenBasis : Set (Set (∀ x, β x)) :=
  { S | ∃ (U : ∀ x, Set (β x)) (F : Finset α),
        (∀ x, x ∈ F → IsOpen (U x)) ∧ S = (F : Set α).pi U }

private lemma isTopologicalBasis_piOpenBasis :
    IsTopologicalBasis (piOpenBasis (β := β)) :=
  isTopologicalBasis_pi (X := β) (T := fun _ => { U | IsOpen U })
    (fun _ => isTopologicalBasis_opens)

/-- Restricting a pi-basis element to a coordinate subset `R` yields an open
set in `(∀ x : R, β x)`. -/
private lemma isOpen_restrict_image_piOpenBasis
    (R : Set α) {S : Set (∀ x, β x)} (hS : S ∈ piOpenBasis (β := β)) :
    IsOpen ((fun f : ∀ x, β x => fun x : R => f x.1) '' S) := by
  classical
  obtain ⟨U, F, hU, rfl⟩ := hS
  -- Key claim: image equals an explicit pi cylinder in (∀ x : R, β x).
  by_cases hpi : ((F : Set α).pi U).Nonempty
  · -- Non-empty case: image = (F ∩ R).pi (U ∘ ↑)
    obtain ⟨f₀, hf₀⟩ := hpi
    have himg : (fun f : ∀ x, β x => fun x : R => f x.1) '' ((F : Set α).pi U) =
        (Subtype.val ⁻¹' (F : Set α) : Set R).pi (fun x : R => U x.1) := by
      ext g
      constructor
      · rintro ⟨f, hf, rfl⟩ ⟨x, hxR⟩ hxF
        exact hf x hxF
      · intro hg
        refine ⟨fun x => if hx : x ∈ R then g ⟨x, hx⟩ else f₀ x, ?_, ?_⟩
        · intro x hxF
          by_cases hxR : x ∈ R
          · simp only [dif_pos hxR]; exact hg ⟨x, hxR⟩ hxF
          · simp only [dif_neg hxR]; exact hf₀ x hxF
        · funext ⟨x, hxR⟩; simp only [dif_pos hxR]
    rw [himg]
    apply isTopologicalBasis_piOpenBasis.isOpen
    refine ⟨fun x : R => U x.1, F.subtype (· ∈ R), ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_subtype] at hx
      exact hU x.1 hx
    · ext g
      constructor
      · intro hg x hxF
        rw [Finset.mem_coe, Finset.mem_subtype] at hxF
        exact hg ⟨x, x.2⟩ hxF
      · intro hg ⟨x, hxR⟩ hxF
        have : (⟨x, hxR⟩ : R) ∈ F.subtype (· ∈ R) := by
          rw [Finset.mem_subtype]; exact hxF
        exact hg _ this
  · -- Empty case: image is empty.
    rw [Set.not_nonempty_iff_eq_empty] at hpi
    rw [hpi, Set.image_empty]
    exact isOpen_empty

/-- Disjoint pi-basis elements whose supports form a Δ-system with root `R`
have disjoint restrictions to `R`. -/
private lemma disjoint_restrict_image_of_delta
    {S₁ S₂ : Set (∀ x, β x)}
    {U₁ U₂ : ∀ x, Set (β x)} {F₁ F₂ : Finset α}
    (h₁ : S₁ = (F₁ : Set α).pi U₁) (h₂ : S₂ = (F₂ : Set α).pi U₂)
    (hd : Disjoint S₁ S₂) (R : Set α)
    (hroot : ((F₁ : Set α)) ∩ ((F₂ : Set α)) = R) :
    Disjoint ((fun f : ∀ x, β x => fun x : R => f x.1) '' S₁)
             ((fun f : ∀ x, β x => fun x : R => f x.1) '' S₂) := by
  classical
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro g ⟨⟨f₁, hf₁S, rfl⟩, ⟨f₂, hf₂S, hfeq⟩⟩
  -- Construct f := f₁ on F₁, f₂ off F₁. Then f ∈ S₁ and f ∈ S₂.
  rw [h₁] at hf₁S
  rw [h₂] at hf₂S
  let f : ∀ x, β x := fun x => if x ∈ F₁ then f₁ x else f₂ x
  have hfS₁ : f ∈ S₁ := by
    rw [h₁]
    intro x hxF
    simp only [Finset.mem_coe] at hxF
    show f x ∈ U₁ x
    simp only [f, if_pos hxF]
    exact hf₁S x hxF
  have hfS₂ : f ∈ S₂ := by
    rw [h₂]
    intro x hxF
    simp only [Finset.mem_coe] at hxF
    show f x ∈ U₂ x
    by_cases hx1 : x ∈ F₁
    · -- x ∈ F₁ ∩ F₂ ⊆ R; use that f₁ and f₂ agree on R
      have hxR : x ∈ R := by
        rw [← hroot]
        exact ⟨hx1, hxF⟩
      simp only [f, if_pos hx1]
      have heq : f₂ x = f₁ x := by
        have := congr_fun hfeq ⟨x, hxR⟩
        simpa using this
      rw [← heq]
      exact hf₂S x hxF
    · simp only [f, if_neg hx1]
      exact hf₂S x hxF
  exact (Set.disjoint_iff_forall_ne.mp hd hfS₁ hfS₂) rfl

theorem countable_chain_condition_pi
    (h : ∀ s : Set α, s.Finite → countable_chain_condition (∀ x : s, β x)) :
    countable_chain_condition (∀ x, β x) := by
  classical
  apply countable_chain_condition_of_topological_basis (piOpenBasis (β := β))
    isTopologicalBasis_piOpenBasis
  intro C hC h2C
  by_contra h3Cne
  have h3C : ℵ₀ < #C := by
    by_contra hle
    push_neg at hle
    exact h3Cne (Cardinal.le_aleph0_iff_set_countable.mp hle)
  -- For each S ∈ C, choose its support data via the basis description.
  have hCdata : ∀ S : C, ∃ (U : ∀ x, Set (β x)) (F : Finset α),
      (∀ x ∈ F, IsOpen (U x)) ∧ S.1 = (F : Set α).pi U := by
    rintro ⟨S, hS⟩; exact hC hS
  choose U F hUopen hSeq using hCdata
  -- Apply Δ-system lemma to the supports F.
  let A : C → Set α := fun S => (F S : Set α)
  have hA_fin : ∀ S : C, (A S).Finite := fun S => Finset.finite_toSet _
  obtain ⟨C', hC'_card, R, hR⟩ := delta_system_lemma_aleph1 A h3C hA_fin
  -- The root R is finite.
  have h2R : R.Finite := by
    -- Any two distinct elements x, y ∈ C' give A x ∩ A y = R, and A x is finite.
    have : ∃ x y : C', x ≠ y := by
      by_contra hne
      push_neg at hne
      have hsub : Subsingleton C' := ⟨fun x y => hne x y⟩
      have hone : #C' ≤ 1 := Cardinal.mk_le_one_iff_set_subsingleton.mpr (by
        intro x hx y hy
        exact congr_arg Subtype.val (hsub.elim ⟨x, hx⟩ ⟨y, hy⟩))
      have : ℵ₀ < (1 : Cardinal) := lt_of_lt_of_le hC'_card hone
      have : ℵ₀ < ℵ₀ := this.trans_le (by simp)
      exact absurd this (lt_irrefl _)
    obtain ⟨x, y, hxy⟩ := this
    rw [← hR hxy]
    exact (hA_fin x.1).inter_of_left _
  -- Define π : (∀ x, β x) → (∀ x : R, β x) and the family D of restrictions.
  let π : (∀ x, β x) → (∀ x : R, β x) := fun f x => f x.1
  let D : Set (Set (∀ x : R, β x)) := (fun S : C' => π '' S.1.1) '' Set.univ
  -- Each member of D is open.
  have hD_open : ∀ ⦃o⦄, o ∈ D → IsOpen o := by
    rintro _ ⟨S, _, rfl⟩
    exact isOpen_restrict_image_piOpenBasis _ (hC S.1.2)
  -- Key lemma about disjoint images.
  have h2'D : ∀ S₁ S₂ : C', S₁ ≠ S₂ → Disjoint (π '' S₁.1.1) (π '' S₂.1.1) := by
    intro S₁ S₂ hne
    -- S₁ ≠ S₂ in C', so S₁.1 ≠ S₂.1 in C, so the underlying sets differ.
    have h12 : S₁.1.1 ≠ S₂.1.1 := fun heq => by
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    -- The C-pairwise-disjoint hypothesis gives Disjoint S₁.1.1 S₂.1.1.
    have hdis : Disjoint S₁.1.1 S₂.1.1 :=
      h2C S₁.1.2 S₂.1.2 h12
    -- Apply the support-extension lemma.
    apply disjoint_restrict_image_of_delta (hSeq S₁.1) (hSeq S₂.1) hdis R
    -- Need: F S₁.1 ∩ F S₂.1 (as Sets) = R
    have := hR (x := S₁) (y := S₂) hne
    -- A is fun S => (F S : Set α), so A S₁ = F S₁ as Set α.
    simpa [A] using this
  -- Members of D are pairwise disjoint.
  have hD_disj : D.PairwiseDisjoint id := by
    rintro _ ⟨S₁, _, rfl⟩ _ ⟨S₂, _, rfl⟩ hne
    have hS₁S₂ : S₁ ≠ S₂ := fun heq => by rw [heq] at hne; exact hne rfl
    exact h2'D S₁ S₂ hS₁S₂
  -- D is uncountable: π is injective on C'.
  -- Two basis elements with disjoint images are not equal,
  -- so the map S ↦ π '' S.1.1 is injective on C' (assuming non-empty images).
  have hD_card : ℵ₀ < #D := by
    -- D = range (fun S : C' => π '' S.1.1).
    -- The map is injective: if π '' S₁ = π '' S₂ and S₁ ≠ S₂, then by h2'D
    -- the images are disjoint, so they are both empty. But each S ∈ C' is
    -- a non-empty basis element (we need to handle this).
    -- For each S ∈ C', S.1.1 must be non-empty to have non-trivial CCC argument.
    -- The C is defined to contain non-empty opens (from countable_chain_condition_of_nonempty
    -- via countable_chain_condition_of_topological_basis), so S.1.1 ≠ ∅.
    -- Actually: countable_chain_condition_of_topological_basis takes a hypothesis on
    -- ALL subsets s ⊆ B with PairwiseDisjoint. We can't assume non-empty without
    -- extra work. Let me handle empty separately.
    --
    -- Plan: split C' into C'_ne (non-empty) and C'_e (empty members).
    -- C'_e has at most one element (all are ∅), so |C'_ne| > ℵ₀.
    -- Then π is injective on C'_ne (non-empty disjoint images can't be equal),
    -- so #(π '' C'_ne) > ℵ₀, hence #D > ℵ₀.
    sorry
  -- Apply CCC for (∀ x : R, β x) to get D countable, contradiction.
  have hD_count : D.Countable := h R h2R D hD_open hD_disj
  have : #D ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hD_count
  exact absurd hD_card (not_lt.mpr this)
