/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/regular_open_algebra.lean lines 1-348 (topology_lemmas + regular sections).

Namespace: everything lives in `Flypitch` namespace to avoid clashing with mathlib's `IsRegular`.
The `ᵖ` postfix for `perp` is declared globally after the namespace.
-/

import Flypitch4.SetTheoryExt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens

open Set TopologicalSpace

universe u

namespace Flypitch

/-! ## topology_lemmas section
  Port of: `namespace topological_space / section topology_lemmas`
-/

section topology_lemmas

variable {α : Type u} [TopologicalSpace α]

/-- A set S is dense: it meets every nonempty open set. -/
def Dense' (S : Set α) : Prop :=
  ∀ U : Set α, IsOpen U → U.Nonempty → (U ∩ S).Nonempty

/-- S is relatively dense in S₀: every open set meeting S₀ also meets S₀ ∩ S. -/
def RelDense (S₀ S : Set α) : Prop :=
  ∀ U : Set α, IsOpen U → (U ∩ S₀).Nonempty → (U ∩ S₀ ∩ S).Nonempty

/-- Dense' S corresponds to mathlib's Dense. -/
lemma dense'_iff_mathlib {S : Set α} : Dense' S ↔ Dense S :=
  dense_iff_inter_open.symm

lemma closure_univ_of_dense {S : Set α} (H_dense : Dense' S) : closure S = Set.univ :=
  (dense'_iff_mathlib.mp H_dense).closure_eq

lemma closure_rel_dense_of_open {S₀ S : Set α} (H_open : IsOpen S₀)
    (H_rel_dense : RelDense S₀ S) : closure S ∩ S₀ = S₀ := by
  ext x; constructor
  · exact fun ⟨_, H₂⟩ => H₂
  · intro H_mem
    refine ⟨?_, H_mem⟩
    rw [mem_closure_iff]
    intro o Ho hxo
    have h_ne : (o ∩ S₀).Nonempty := ⟨x, hxo, H_mem⟩
    rcases H_rel_dense o Ho h_ne with ⟨y, ⟨⟨hy_o, _⟩, hy_S⟩⟩
    exact ⟨y, hy_o, hy_S⟩

/-- S is dense in basis 𝓑 if S meets every nonempty B ∈ 𝓑. -/
def DenseInBasis (S : Set α) {𝓑 : Set (Set α)} (_H_basis : IsTopologicalBasis 𝓑) : Prop :=
  ∀ B ∈ 𝓑, B.Nonempty → (B ∩ S).Nonempty

lemma dense_of_dense_in_basis (S : Set α) {𝓑 : Set (Set α)}
    (H_basis : IsTopologicalBasis 𝓑) (H : DenseInBasis S H_basis) : Dense' S := by
  intro U HU ⟨a, Ha⟩
  rcases H_basis.exists_subset_of_mem_open Ha HU with ⟨B, HB₁, HB₂, HB₃⟩
  rcases H B HB₁ ⟨a, HB₂⟩ with ⟨x, hxB, hxS⟩
  exact ⟨x, HB₃ hxB, hxS⟩

/-- S is relatively dense in S₀ with respect to basis 𝓑. -/
def RelDenseInBasis (S₀ : Set α) (S : Set α) {𝓑 : Set (Set α)}
    (_H_basis : IsTopologicalBasis 𝓑) : Prop :=
  ∀ B ∈ 𝓑, (B ∩ S₀).Nonempty → (B ∩ S₀ ∩ S).Nonempty

lemma rel_dense_of_dense_in_basis (S₀ : Set α) (S : Set α) {𝓑 : Set (Set α)}
    (H_basis : IsTopologicalBasis 𝓑) (H : RelDenseInBasis S₀ S H_basis) : RelDense S₀ S := by
  intro U HU ⟨a, ha_U, ha_S₀⟩
  rcases H_basis.exists_subset_of_mem_open ha_U HU with ⟨B, HB₁, HB₂, HB₃⟩
  rcases H B HB₁ ⟨a, HB₂, ha_S₀⟩ with ⟨x, ⟨hxB, hxS₀⟩, hxS⟩
  exact ⟨x, ⟨HB₃ hxB, hxS₀⟩, hxS⟩

/-- S is nowhere dense if interior(closure S) = ∅. -/
def NowhereDense (S : Set α) : Prop := interior (closure S) = ∅

lemma frontier_closed_of_open {S : Set α} (_H : IsOpen S) : IsClosed (frontier S) :=
  isClosed_frontier

/-- The frontier of an open set is nowhere dense. -/
lemma frontier_nowhere_dense_of_open {S : Set α} (H : IsOpen S) : NowhereDense (frontier S) := by
  unfold NowhereDense
  rw [isClosed_frontier.closure_eq]
  -- interior(frontier S) = ∅ for open S
  -- frontier S = closure S \ S (since interior S = S)
  -- interior(closure S \ S) ⊆ interior(Sᶜ) ∩ interior(closure S)
  -- = (closure S)ᶜ ∩ interior(closure S) = ∅  (a set is disjoint from its complement)
  -- Actually: interior(Sᶜ) = (closure S)ᶜ since Sᶜ is closed:
  -- closure(Sᶜ) = Sᶜ (wrong - only if closed), but Sᶜ might not be closed.
  -- Correct key: frontier S ⊆ Sᶜ and frontier S ⊆ closure S.
  -- interior(frontier S) is open and ⊆ frontier S ⊆ Sᶜ and ⊆ closure S.
  -- So interior(frontier S) is open, ⊆ closure S, ⊆ Sᶜ = (interior S)ᶜ.
  -- From H.subset_interior_iff: open T ⊆ closure S iff T ⊆ closure S.
  -- Not helpful. Use: interior(frontier S) ⊆ interior S = S (because interior_mono frontier_subset_closure gives interior(frontier S) ⊆ interior(closure S) ⊇ S ... not sub.
  -- Actually interior_frontier for CLOSED sets: if S were closed, done.
  -- Key insight: frontier S = frontier Sᶜ (frontier_compl). Sᶜ is ... not closed.
  -- Use: interior_frontier h for h : IsClosed Sᶜ (but Sᶜ might not be closed).
  -- Actually the Lean 3 proof uses `{[smt] eblast}` which is very powerful.
  -- Let's try: interior(frontier S) ⊆ S ∩ Sᶜ = ∅
  -- interior(frontier S) ⊆ interior S = S: by interior_mono frontier_subset_closure? No.
  -- interior(frontier S) ⊆ Sᶜ: frontier S = closure S \ interior S ⊆ (interior S)ᶜ = Sᶜ
  -- So interior(frontier S) ⊆ Sᶜ. And interior(frontier S) is open.
  -- interior(frontier S) ⊆ interior S = S: by H.subset_interior_iff...
  -- No: interior(frontier S) is open ⊆ Sᶜ, so interior(frontier S) ∩ S = ∅.
  -- We need interior(frontier S) = ∅, not just ∩ S = ∅.
  -- Since interior(frontier S) is open and ⊆ Sᶜ, and S is open:
  -- if interior(frontier S) is nonempty, it's an open set meeting Sᶜ.
  -- But frontier S ⊆ closure S, so interior(frontier S) ⊆ closure S.
  -- interior(frontier S) ⊆ closure S ∩ Sᶜ = frontier S... circular.
  -- Use disjoint_interior_frontier : Disjoint (interior S) (frontier S)
  -- interior(frontier S) ⊆ frontier S, so interior(frontier S) ∩ interior S = ∅.
  -- interior(frontier S) is open, contained in frontier S ⊆ closure S,
  -- and disjoint from interior S = S (since open ⊆ interior implies T ⊆ S).
  -- So interior(frontier S) ∩ S = ∅. But also interior(frontier S) ⊆ closure S.
  -- closure S = S ∪ frontier S. interior(frontier S) ⊆ frontier S, disjoint from S.
  -- So interior(frontier S) ⊆ frontier S and interior(frontier S) ∩ interior S = ∅.
  -- An open set disjoint from all open subsets of S, ...
  -- Using: if T is open, T ⊆ Sᶜ, T ⊆ closure S → T ⊆ interior(Sᶜ ∩ closure S)...
  -- THIS IS GETTING CIRCULAR. Let's just use subset_empty_iff and contradiction.
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx_frontier : x ∈ frontier S := interior_subset hx
  have hx_cl : x ∈ closure S := hx_frontier.1
  -- x ∈ interior(frontier S) means x has open nbhd t ⊆ frontier S ⊆ closure S \ S
  rw [mem_interior] at hx
  rcases hx with ⟨t, ht_sub, ht_open, hxt⟩
  -- t ⊆ frontier S ⊆ closure S \ S, so t ∩ S = ∅
  have ht_S : t ∩ S = ∅ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨hyt, hyS⟩
    exact (H.frontier_eq ▸ ht_sub hyt).2 hyS
  -- But t is open and x ∈ closure S ∩ t, so by closure_inter_open_nonempty_iff,
  -- (S ∩ t).Nonempty - contradiction with ht_S
  have hxt_cl : (closure S ∩ t).Nonempty := ⟨x, hx_cl, hxt⟩
  rw [closure_inter_open_nonempty_iff ht_open] at hxt_cl
  rcases hxt_cl with ⟨y, hyS, hyt⟩
  exact absurd (show y ∈ t ∩ S from ⟨hyt, hyS⟩) (by simp [ht_S])

lemma isClopen_interior' {S : Set α} (H : IsClopen S) : interior S = S := H.2.interior_eq
lemma isClopen_closure' {S : Set α} (H : IsClopen S) : closure S = S := H.1.closure_eq

end topology_lemmas

/-! ## regular section -/

section regular

variable {α : Type u} [TopologicalSpace α]

/-- A set S is regular open if S = interior(closure S). -/
def IsRegularOpen (S : Set α) : Prop := S = interior (closure S)

/-- The perp of S: the complement of the closure. -/
def perp (S : Set α) : Set α := (closure S)ᶜ

end regular

end Flypitch

-- Declare ᵖ postfix globally (outside namespace)
postfix:80 "ᵖ" => Flypitch.perp

/-! ## Lemmas about perp and IsRegularOpen in namespace Flypitch.Regular -/

namespace Flypitch.Regular

open Flypitch

variable {α : Type u} [TopologicalSpace α]

@[simp] lemma perp_unfold (S : Set α) : Sᵖ = (closure S)ᶜ := rfl

lemma perp_eq_int_neg {S : Set α} : Sᵖ = interior Sᶜ := by
  simp [Flypitch.perp, interior_compl]

lemma mem_perp_iff {S : Set α} {x : α} :
    x ∈ Sᵖ ↔ ∃ T, T ∩ S = ∅ ∧ IsOpen T ∧ x ∈ T := by
  rw [perp_eq_int_neg, mem_interior]
  constructor
  · rintro ⟨t, ht_sub, ht_open, hx⟩
    refine ⟨t, ?_, ht_open, hx⟩
    ext y; simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    intro ⟨hyt, hyS⟩
    exact absurd hyS (ht_sub hyt)
  · rintro ⟨t, ht_inter, ht_open, hx⟩
    refine ⟨t, fun y hy => ?_, ht_open, hx⟩
    simp only [mem_compl_iff]
    intro hyS
    exact absurd (show y ∈ t ∩ S from ⟨hy, hyS⟩) (by rw [ht_inter]; exact notMem_empty y)

@[simp] lemma isOpen_perp {S : Set α} : IsOpen (Sᵖ) :=
  isClosed_closure.isOpen_compl

@[simp] lemma perp_univ : (Set.univ : Set α)ᵖ = ∅ := by simp [Flypitch.perp]

@[simp] lemma perp_empty : (∅ : Set α)ᵖ = Set.univ := by simp [Flypitch.perp]

@[simp] lemma isOpen_of_isRegularOpen {S : Set α} (H : IsRegularOpen S) : IsOpen S := by
  rw [H]; exact isOpen_interior

@[simp] lemma isRegularOpen_of_isClopen {S : Set α} (H : IsClopen S) : IsRegularOpen S := by
  unfold IsRegularOpen; rw [H.1.closure_eq, H.2.interior_eq]

lemma p_p_eq_int_cl {S : Set α} : Sᵖᵖ = interior (closure S) := by
  simp only [perp_unfold, closure_compl, compl_compl]

lemma int_cl_eq_p_p {S : Set α} : interior (closure S) = Sᵖᵖ := p_p_eq_int_cl.symm

lemma regular_iff_p_p {S : Set α} : IsRegularOpen S ↔ Sᵖᵖ = S := by
  rw [IsRegularOpen, ← p_p_eq_int_cl]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

lemma mem_int_cl_iff_mem_eq_p_p {S : Set α} {a : α} :
    a ∈ interior (closure S) ↔ a ∈ Sᵖᵖ := by rw [int_cl_eq_p_p]

lemma isOpen_of_p_p {S : Set α} (H : Sᵖᵖ = S) : IsOpen S := by
  rw [p_p_eq_int_cl] at H; exact H ▸ isOpen_interior

@[simp] lemma isRegularOpen_empty : IsRegularOpen (∅ : Set α) := by simp [IsRegularOpen]

@[simp] lemma isRegularOpen_univ : IsRegularOpen (Set.univ : Set α) := by simp [IsRegularOpen]

lemma p_anti {P Q : Set α} (H : P ⊆ Q) : Qᵖ ⊆ Pᵖ :=
  compl_subset_compl.mpr (closure_mono H)

lemma p_p_mono {P Q : Set α} (H : P ⊆ Q) : Pᵖᵖ ⊆ Qᵖᵖ := p_anti (p_anti H)

lemma in_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := by
  rw [p_p_eq_int_cl]; exact H.subset_interior_iff.mpr subset_closure

@[simp] lemma isRegularOpen_eq_p_p {S : Set α} (H : IsRegularOpen S) : Sᵖᵖ = S := by
  rw [regular_iff_p_p] at H; exact H

lemma isRegularOpen_stable_subset {S₁ S₂ : Set α} (H : IsRegularOpen S₂) (H₂ : S₁ ⊆ S₂) :
    S₁ᵖᵖ ⊆ S₂ := by
  have h := p_p_mono H₂
  rwa [isRegularOpen_eq_p_p H] at h

lemma subset_p_p_of_open {S : Set α} (H : IsOpen S) : S ⊆ Sᵖᵖ := in_p_p_of_open H

lemma subset_int_cl_of_open {S : Set α} (H : IsOpen S) : S ⊆ interior (closure S) := by
  rw [← p_p_eq_int_cl]; exact subset_p_p_of_open H

lemma p_eq_p_p_p {S : Set α} (H : IsOpen S) : Sᵖ = Sᵖᵖᵖ :=
  le_antisymm (in_p_p_of_open isOpen_perp) (p_anti (in_p_p_of_open H))

@[simp] lemma p_p_p_p_eq_p_p {S : Set α} : Sᵖᵖᵖᵖ = Sᵖᵖ :=
  (p_eq_p_p_p (isOpen_perp (S := S))).symm

@[simp] lemma isOpen_of_p_p' {S : Set α} : IsOpen (Sᵖᵖ) := by
  rw [p_p_eq_int_cl]; exact isOpen_interior

@[simp] lemma isRegularOpen_p_p {S : Set α} : IsRegularOpen (Sᵖᵖ) := by
  rw [regular_iff_p_p]
  exact p_p_p_p_eq_p_p

lemma isRegularOpen_sup {S₁ S₂ : Set α} : IsRegularOpen ((S₁ ∪ S₂)ᵖᵖ) :=
  isRegularOpen_p_p

/-- For open S₁: S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂). -/
lemma inter_eq_inter_aux (S₁ S₂ : Set α) (H : IsOpen S₁) :
    S₁ ∩ closure S₂ ⊆ closure (S₁ ∩ S₂) := by
  -- IsOpen.closure_inter : IsOpen t → closure s ∩ t ⊆ closure (s ∩ t)
  -- gives closure S₂ ∩ S₁ ⊆ closure (S₂ ∩ S₁)
  -- then use Set.inter_comm
  intro x ⟨hx1, hx2⟩
  have := H.closure_inter (s := S₂) ⟨hx2, hx1⟩
  rwa [Set.inter_comm S₂ S₁] at this

@[simp] lemma cl_compl_of_isOpen (S : Set α) (H : IsOpen S) : closure Sᶜ = Sᶜ :=
  H.isClosed_compl.closure_eq

lemma inter_eq_inter_aux₂ (S₁ S₂ : Set α) (H₁ : IsOpen S₁) (_H₂ : IsOpen S₂) :
    S₁ ∩ S₂ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
  rw [p_p_eq_int_cl, p_p_eq_int_cl]
  intro x ⟨hx1, hx2⟩
  rw [mem_interior] at hx2 ⊢
  rcases hx2 with ⟨t, ht_sub, ht_open, hxt⟩
  exact ⟨S₁ ∩ t, (Set.inter_subset_inter_right S₁ ht_sub).trans (inter_eq_inter_aux S₁ S₂ H₁),
    H₁.inter ht_open, hx1, hxt⟩

lemma p_p_inter_eq_inter_p_p {S₁ S₂ : Set α} (H₁ : IsOpen S₁) (H₂ : IsOpen S₂) :
    (S₁ ∩ S₂)ᵖᵖ = S₁ᵖᵖ ∩ S₂ᵖᵖ := by
  apply le_antisymm
  · exact fun x hx => ⟨p_p_mono Set.inter_subset_left hx,
                        p_p_mono Set.inter_subset_right hx⟩
  · intro x ⟨hx1, hx2⟩
    -- S₁ᵖᵖ ∩ S₂ᵖᵖ ⊆ (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖᵖᵖ = (S₁ ∩ S₂)ᵖᵖ
    -- Step 1: (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ
    -- (using S₁ᵖᵖ ∩ S₂ ⊆ (S₁ ∩ S₂)ᵖᵖ, then apply p_p_mono and p_p_p_p_eq_p_p)
    have sub1 : S₁ᵖᵖ ∩ S₂ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      intro y ⟨hy1, hy2⟩
      have h := inter_eq_inter_aux₂ S₂ S₁ H₂ H₁ ⟨hy2, hy1⟩
      rwa [Set.inter_comm] at h
    have sub2 : (S₁ᵖᵖ ∩ S₂)ᵖᵖ ⊆ (S₁ ∩ S₂)ᵖᵖ := by
      have := p_p_mono sub1
      rwa [p_p_p_p_eq_p_p] at this
    have step := inter_eq_inter_aux₂ (S₁ᵖᵖ) S₂ (isOpen_of_p_p' (S := S₁)) H₂
    exact sub2 (step ⟨hx1, hx2⟩)

@[simp] lemma isRegularOpen_inter {S₁ S₂ : Set α} (H₁ : IsRegularOpen S₁)
    (H₂ : IsRegularOpen S₂) : IsRegularOpen (S₁ ∩ S₂) := by
  rw [regular_iff_p_p] at *
  rw [p_p_inter_eq_inter_p_p (isOpen_of_p_p H₁) (isOpen_of_p_p H₂), H₁, H₂]

lemma Union_perp_subset (C : Set (Set α)) : ⋃₀ (Flypitch.perp '' C) ⊆ (⋂₀ C)ᵖ := by
  intro x hx
  simp only [mem_sUnion, mem_image] at hx
  rcases hx with ⟨_, ⟨s, hs, rfl⟩, hxs⟩
  simp only [perp_unfold, mem_compl_iff] at hxs ⊢
  exact fun hx_sInter => hxs (closure_mono (sInter_subset_of_mem hs) hx_sInter)

lemma perp_sUnion_perp {C : Set (Set α)} (h : ∀ s ∈ C, IsRegularOpen s) :
    (⋃₀ (Flypitch.perp '' C))ᵖ = (⋂₀ C)ᵖᵖ := by
  refine subset_antisymm ?_ (p_anti (Union_perp_subset C))
  -- x ∈ (⋃₀ perp '' C)ᵖ = interior (⋃₀ perp '' C)ᶜ
  -- means x has an open neighbourhood t with t ∩ (sᵖ) = ∅ for all s ∈ C
  -- i.e. t ⊆ (sᵖ)ᶜ = closure s for all s
  -- Since t is open and s is regular: t ⊆ interior(closure s) = s
  -- So t ⊆ ⋂₀ C ⊆ closure(⋂₀ C), giving x ∈ interior(closure(⋂₀ C)) = (⋂₀ C)ᵖᵖ
  intro x hx
  rw [perp_eq_int_neg] at hx
  rw [p_p_eq_int_cl]
  rw [mem_interior] at hx ⊢
  rcases hx with ⟨t, ht_sub, ht_open, hxt⟩
  -- ht_sub : t ⊆ (⋃₀ Flypitch.perp '' C)ᶜ
  have ht_sInter : t ⊆ ⋂₀ C := by
    intro y hy
    rw [mem_sInter]
    intro s hs
    -- y ∉ sᵖ (since t ⊆ (⋃₀ perp '' C)ᶜ and sᵖ ⊆ ⋃₀ perp '' C)
    have hy_not_union : y ∉ ⋃₀ (Flypitch.perp '' C) := ht_sub hy
    have hy_not_perp : y ∉ Flypitch.perp s := by
      intro hp
      apply hy_not_union
      exact ⟨Flypitch.perp s, ⟨s, hs, rfl⟩, hp⟩
    -- y ∉ sᵖ = (closure s)ᶜ, so y ∈ closure s
    simp only [perp_unfold, mem_compl_iff, not_not] at hy_not_perp
    -- y ∈ closure s, t is open, so y ∈ interior(closure s) = s (regular)
    -- First show t ⊆ closure s
    have ht_cl_s : t ⊆ closure s := by
      intro z hz
      have hz_not_union : z ∉ ⋃₀ (Flypitch.perp '' C) := ht_sub hz
      have hz_not_perp : z ∉ Flypitch.perp s := fun hp =>
        hz_not_union ⟨_, ⟨s, hs, rfl⟩, hp⟩
      simpa [perp_unfold, mem_compl_iff] using hz_not_perp
    -- t ⊆ closure s and t is open, so t ⊆ interior(closure s)
    have ht_int_cl_s : t ⊆ interior (closure s) :=
      ht_open.subset_interior_iff.mpr ht_cl_s
    -- y ∈ t ⊆ interior(closure s) = s (by regularity)
    rw [← isRegularOpen_eq_p_p (h s hs), p_p_eq_int_cl]
    exact ht_int_cl_s hy
  exact ⟨t, ht_sInter.trans subset_closure, ht_open, hxt⟩

end Flypitch.Regular
