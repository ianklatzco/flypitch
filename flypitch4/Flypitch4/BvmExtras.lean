/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/bvm_extras.lean lines 1-700 — Task 14a -/

import Flypitch4.Bvm

open scoped Flypitch
open Lattice

universe u

namespace bSet

section extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Singleton instance for bSet so that `{x}` notation works -/
instance singleton_bSet : Singleton (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun x => bSet.insert1 x ∅⟩

/-- Rewrite `{x}` to `bSet.insert1 x ∅` for membership -/
@[simp] lemma mem_singleton_bSet {x y : bSet 𝔹} :
    x ∈ᴮ ({y} : bSet 𝔹) = x =ᴮ y ⊔ x ∈ᴮ (∅ : bSet 𝔹) :=
  show x ∈ᴮ bSet.insert1 y ∅ = _ from mem_insert1

-- src/bvm_extras.lean:24
@[simp] lemma insert1_bval_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).bval none = ⊤ := rfl

-- src/bvm_extras.lean:27
@[simp] lemma insert1_bval_some {u v : bSet 𝔹} {i} :
    (bSet.insert1 u ({v})).bval (some i) = (bval ({v} : bSet 𝔹)) i := rfl

-- src/bvm_extras.lean:30
@[simp] lemma insert1_func_none {u v : bSet 𝔹} : (bSet.insert1 u ({v})).func none = u := rfl

-- src/bvm_extras.lean:33
@[simp] lemma insert1_func_some {u v : bSet 𝔹} {i} :
    (bSet.insert1 u ({v})).func (some i) = (func ({v} : bSet 𝔹)) i := rfl

-- src/bvm_extras.lean:36
@[simp] lemma mem_singleton {x : bSet 𝔹} : ⊤ ≤ x ∈ᴮ ({x} : bSet 𝔹) := by
  simp [mem_singleton_bSet, bv_eq_refl]

-- src/bvm_extras.lean:39
lemma eq_of_mem_singleton' {x y : bSet 𝔹} : y ∈ᴮ ({x} : bSet 𝔹) ≤ x =ᴮ y := by
  simp only [mem_singleton_bSet]
  exact sup_le (le_of_eq bv_eq_symm) (le_trans (bot_of_mem_empty le_rfl) bot_le)

-- src/bvm_extras.lean:42
lemma eq_of_mem_singleton {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ y ∈ᴮ ({x} : bSet 𝔹)) : c ≤ x =ᴮ y :=
  le_trans h eq_of_mem_singleton'

-- src/bvm_extras.lean:45
lemma eq_mem_singleton {x y : bSet 𝔹} {Γ : 𝔹} (h : Γ ≤ y ∈ᴮ ({x} : bSet 𝔹)) : Γ ≤ y =ᴮ x :=
  le_trans (eq_of_mem_singleton h) (le_of_eq bv_eq_symm)

-- src/bvm_extras.lean:48
lemma eq_zero_of_mem_one {x : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ (1 : bSet 𝔹)) : Γ ≤ x =ᴮ 0 := by
  sorry -- TODO: one_eq_singleton_zero pending in Bvm.lean (src/bvm_extras.lean:48)

-- src/bvm_extras.lean:56
lemma mem_singleton_of_eq {x y : bSet 𝔹} {c : 𝔹} (h : c ≤ x =ᴮ y) : c ≤ y ∈ᴮ ({x} : bSet 𝔹) := by
  simp only [mem_singleton_bSet]
  exact le_trans (le_trans h (le_of_eq bv_eq_symm)) le_sup_left

-- src/bvm_extras.lean:62
lemma eq_inserted_of_eq_singleton {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ y := by
  -- From bv_eq_unfold, the second (⊆ LHS) component gives: at index none in insert1 y {z}:
  -- bval none = ⊤, func none = y → y ∈ {x}. And y ∈ {x} = y =ᴮ x, so x =ᴮ y.
  -- From the first (⊆ RHS) component at none in {x}: x ∈ insert1 y {z} = x =ᴮ y ⊔ x =ᴮ z.
  -- Combined: (x =ᴮ y ⊔ x =ᴮ z) ⊓ y =ᴮ x ≤ x =ᴮ y.
  -- bval none for insert1 u v is ⊤ by insert1_unfold
  -- func none for insert1 u v is u by insert1_unfold
  -- Extract: {x} =ᴮ insert1 y {z} ≤ y ∈ {x} (from RHS ⊆ LHS at index none)
  -- bv_eq_unfold gives ⨅ a : (bSet.insert1 y {z}).type, bval a ⟹ func a ∈ {x}
  -- (bSet.insert1 y {z}).type = Option ({z}).type = Option (Option PEmpty)
  -- At a = (none : Option (Option PEmpty)): bval none = ⊤, func none = y
  have hR : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ y ∈ᴮ ({x} : bSet 𝔹) := by
    have h1 : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤
        ⨅ (a : (bSet.insert1 y ({z} : bSet 𝔹)).type),
          (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
          (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹) := by
      rw [bv_eq_unfold]; exact inf_le_right
    have h2 : (⨅ (a : (bSet.insert1 y ({z} : bSet 𝔹)).type),
          (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
          (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹)) ≤
        y ∈ᴮ ({x} : bSet 𝔹) := by
      -- Specialize at none; definitionally .bval none = ⊤ and .func none = y
      have step := iInf_le (f := fun (a : (bSet.insert1 y ({z} : bSet 𝔹)).type) =>
        (bSet.insert1 y ({z} : bSet 𝔹)).bval a ⟹
        (bSet.insert1 y ({z} : bSet 𝔹)).func a ∈ᴮ ({x} : bSet 𝔹)) (none)
      -- (bSet.insert1 y {z}).bval none = ⊤ and .func none = y by definition
      have hbval : (bSet.insert1 y ({z} : bSet 𝔹)).bval (none : (bSet.insert1 y ({z} : bSet 𝔹)).type) = ⊤ := rfl
      have hfunc : (bSet.insert1 y ({z} : bSet 𝔹)).func (none : (bSet.insert1 y ({z} : bSet 𝔹)).type) = y := rfl
      rw [hbval, hfunc, top_imp] at step
      exact step
    exact le_trans h1 h2
  -- y ∈ {x} = y =ᴮ x, so we get x =ᴮ y from symmetry
  have hmem_R : y ∈ᴮ ({x} : bSet 𝔹) = y =ᴮ x := by
    show y ∈ᴮ insert x (∅ : bSet 𝔹) = _
    rw [mem_insert1]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  rw [hmem_R] at hR
  -- hR: {x} =ᴮ insert1 y {z} ≤ y =ᴮ x
  exact hR.trans (le_of_eq bv_eq_symm)

-- src/bvm_extras.lean:69
lemma insert1_symm (y z : bSet 𝔹) : ⊤ ≤ bSet.insert1 y ({z} : bSet 𝔹) =ᴮ bSet.insert1 z ({y} : bSet 𝔹) := by
  -- w ∈ insert1 y {z} = w =ᴮ y ⊔ w =ᴮ z = w ∈ insert1 z {y}
  have hmem : ∀ (a b w : bSet 𝔹),
      w ∈ᴮ bSet.insert1 a ({b} : bSet 𝔹) = w =ᴮ a ⊔ w =ᴮ b := fun a b w => by
    show w ∈ᴮ insert a ({b} : bSet 𝔹) = _
    rw [mem_insert1]
    have : w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show w =ᴮ a ⊔ w ∈ᴮ insert b (∅ : bSet 𝔹) = _
    rw [mem_insert1, this, sup_bot_eq]
  apply mem_ext
  · apply le_iInf; intro w; rw [← deduction, hmem y z w, hmem z y w, top_inf_eq]
    exact le_of_eq (sup_comm _ _)
  · apply le_iInf; intro w; rw [← deduction, hmem z y w, hmem y z w, top_inf_eq]
    exact le_of_eq (sup_comm _ _)

-- src/bvm_extras.lean:78
lemma eq_inserted_of_eq_singleton' {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ z := by
  -- {x} =ᴮ insert1 y {z} and insert1 y {z} =ᴮ insert1 z {y} (by insert1_symm)
  -- so {x} =ᴮ insert1 z {y} ≤ x =ᴮ z (by eq_inserted_of_eq_singleton with y ↔ z)
  -- use bv_eq_trans: {x} =ᴮ insert1 y {z} ⊓ insert1 y {z} =ᴮ insert1 z {y} ≤ {x} =ᴮ insert1 z {y}
  have step1 : ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹)
      ≤ ({x} : bSet 𝔹) =ᴮ bSet.insert1 z ({y} : bSet 𝔹) :=
    le_trans (le_inf le_rfl (le_top.trans (insert1_symm y z))) bv_eq_trans
  exact le_trans step1 eq_inserted_of_eq_singleton

-- src/bvm_extras.lean:81
def binary_union (x y : bSet 𝔹) : bSet 𝔹 := bv_union ({x, y} : bSet 𝔹)

-- src/bvm_extras.lean:84
def binary_inter (x y : bSet 𝔹) : bSet 𝔹 :=
  ⟨x.type, x.func, fun i => x.bval i ⊓ (x.func i) ∈ᴮ y⟩

scoped infix:81 " ∩ᴮ " => bSet.binary_inter

-- src/bvm_extras.lean:88
@[simp] lemma binary_inter_bval {x y : bSet 𝔹} {i : x.type} :
    (x ∩ᴮ y).bval i = x.bval i ⊓ (x.func i) ∈ᴮ y := rfl

-- src/bvm_extras.lean:90
@[simp] lemma binary_inter_type {x y : bSet 𝔹} : (x ∩ᴮ y).type = x.type := rfl

-- src/bvm_extras.lean:92
@[simp] lemma binary_inter_func {x y : bSet 𝔹} {i} : (x ∩ᴮ y).func i = x.func i := rfl

-- src/bvm_extras.lean:94
lemma mem_binary_inter_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ∈ᴮ (x ∩ᴮ y) ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ z ∈ᴮ y) := by
  -- (x ∩ᴮ y).bval i = x.bval i ⊓ (x.func i ∈ᴮ y)
  -- (x ∩ᴮ y).func i = x.func i
  -- z ∈ᴮ (x ∩ᴮ y) = ⨆ i, (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
  constructor
  · intro H
    constructor
    · -- z ∈ᴮ x: strip the x.func i ∈ᴮ y part
      rw [mem_unfold] at H ⊢
      apply le_trans H; apply iSup_le; intro i
      apply le_iSup_of_le i
      simp only [binary_inter_bval, binary_inter_func]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · -- z ∈ᴮ y: from x.func i ∈ᴮ y and z =ᴮ x.func i
      -- Use subst_congr_mem_left' with u=x.func i, v=z, w=y
      -- need: Γ_1 ≤ x.func i =ᴮ z and Γ_1 ≤ x.func i ∈ᴮ y
      rw [mem_unfold] at H
      apply le_trans H; apply iSup_le; intro i
      simp only [binary_inter_bval, binary_inter_func]
      -- Γ_1 = (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
      exact subst_congr_mem_left' (bv_symm inf_le_right) (inf_le_left.trans inf_le_right)
  · intro ⟨H₁, H₂⟩
    -- Use H₁ : Γ ≤ z ∈ᴮ x and H₂ : Γ ≤ z ∈ᴮ y
    -- z ∈ᴮ x = ⨆ i, x.bval i ⊓ z =ᴮ x.func i
    -- We need ⨆ i, (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
    -- Augment with H₂: Γ ≤ (⨆ i, x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y
    -- Then: (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y ≤ (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
    rw [mem_unfold] at H₁ ⊢
    calc Γ ≤ (⨆ i : x.type, x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y := le_inf H₁ H₂
      _ ≤ ⨆ i : x.type, (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y := by
              rw [iSup_inf_eq]
      _ ≤ ⨆ i : (x ∩ᴮ y).type, (x ∩ᴮ y).bval i ⊓ z =ᴮ (x ∩ᴮ y).func i := by
              apply iSup_le; intro i; apply le_iSup_of_le i
              simp only [binary_inter_bval, binary_inter_func]
              -- (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y ≤ (x.bval i ⊓ x.func i ∈ᴮ y) ⊓ z =ᴮ x.func i
              refine le_inf (le_inf ?_ ?_) ?_
              · exact inf_le_left.trans inf_le_left
              · -- (x.bval i ⊓ z =ᴮ x.func i) ⊓ z ∈ᴮ y ≤ x.func i ∈ᴮ y
                -- Use subst_congr_mem_left: z =ᴮ x.func i ⊓ z ∈ᴮ y ≤ x.func i ∈ᴮ y
                exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
                               subst_congr_mem_left
              · exact inf_le_left.trans inf_le_right

-- src/bvm_extras.lean:112
lemma subset_binary_inter_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ⊆ᴮ x ∩ᴮ y ↔ (Γ ≤ z ⊆ᴮ x ∧ Γ ≤ z ⊆ᴮ y) := by
  constructor
  · intro H
    constructor
    · -- z ⊆ x: every w ∈ z is in x ∩ y hence in x
      rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
      have hmem : Γ ⊓ w ∈ᴮ z ≤ w ∈ᴮ (x ∩ᴮ y) := mem_of_mem_subset (le_trans inf_le_left H) inf_le_right
      exact (mem_binary_inter_iff.mp hmem).1
    · -- z ⊆ y: every w ∈ z is in x ∩ y hence in y
      rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
      have hmem : Γ ⊓ w ∈ᴮ z ≤ w ∈ᴮ (x ∩ᴮ y) := mem_of_mem_subset (le_trans inf_le_left H) inf_le_right
      exact (mem_binary_inter_iff.mp hmem).2
  · intro ⟨H₁, H₂⟩
    rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
    apply mem_binary_inter_iff.mpr
    exact ⟨mem_of_mem_subset (le_trans inf_le_left H₁) inf_le_right, mem_of_mem_subset (le_trans inf_le_left H₂) inf_le_right⟩

-- src/bvm_extras.lean:126
lemma binary_inter_symm {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y =ᴮ y ∩ᴮ x := by
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.2, h.1⟩
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (y ∩ᴮ x) ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ (y ∩ᴮ x) ≤ z ∈ᴮ x :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.2, h.1⟩

-- src/bvm_extras.lean:132
lemma B_congr_binary_inter_left {y : bSet 𝔹} : B_congr (fun x => x ∩ᴮ y) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (x₁ ∩ᴮ y) ≤ z ∈ᴮ x₁ ∧ Γ ⊓ z ∈ᴮ (x₁ ∩ᴮ y) ≤ z ∈ᴮ y :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨bv_rw'' (le_trans inf_le_left H_eq) h.1 B_ext_mem_right, h.2⟩
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (x₂ ∩ᴮ y) ≤ z ∈ᴮ x₂ ∧ Γ ⊓ z ∈ᴮ (x₂ ∩ᴮ y) ≤ z ∈ᴮ y :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨bv_rw'' (le_trans inf_le_left (bv_symm H_eq)) h.1 B_ext_mem_right, h.2⟩

-- src/bvm_extras.lean:139
lemma B_congr_binary_inter_right {y : bSet 𝔹} : B_congr (fun x => y ∩ᴮ x) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (y ∩ᴮ x₁) ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ (y ∩ᴮ x₁) ≤ z ∈ᴮ x₁ :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.1, bv_rw'' (le_trans inf_le_left H_eq) h.2 B_ext_mem_right⟩
  · apply le_iInf; intro z; rw [← deduction]
    have h : Γ ⊓ z ∈ᴮ (y ∩ᴮ x₂) ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ (y ∩ᴮ x₂) ≤ z ∈ᴮ x₂ :=
      mem_binary_inter_iff.mp inf_le_right
    exact mem_binary_inter_iff.mpr ⟨h.1, bv_rw'' (le_trans inf_le_left (bv_symm H_eq)) h.2 B_ext_mem_right⟩

-- src/bvm_extras.lean:146
lemma binary_inter_subset_left {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ x := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
    mem_binary_inter_iff.mp inf_le_right
  exact h.1

-- src/bvm_extras.lean:150
lemma binary_inter_subset_right {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ y := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have h : Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ x ∧ Γ ⊓ z ∈ᴮ (x ∩ᴮ y) ≤ z ∈ᴮ y :=
    mem_binary_inter_iff.mp inf_le_right
  exact h.2

-- src/bvm_extras.lean:158
lemma unordered_pair_symm (x y : bSet 𝔹) {Γ : 𝔹} : Γ ≤ ({x, y} : bSet 𝔹) =ᴮ {y, x} := by
  -- z ∈ᴮ {x, y} = z =ᴮ x ⊔ z =ᴮ y, z ∈ᴮ {y, x} = z =ᴮ y ⊔ z =ᴮ x
  have mem_bot : ∀ (w : bSet 𝔹), w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := fun w => by
    rw [mem_unfold]; exact exists_over_empty _
  apply mem_ext
  all_goals {
    apply le_iInf; intro z; rw [← deduction]
    simp only [mem_insert1, mem_singleton_bSet, mem_bot, sup_bot_eq]
    exact le_trans inf_le_right (le_of_eq (sup_comm _ _))
  }

-- src/bvm_extras.lean:166
lemma binary_union_symm {x y : bSet 𝔹} {Γ} : Γ ≤ binary_union x y =ᴮ binary_union y x := by
  unfold binary_union
  exact B_congr_bv_union (unordered_pair_symm x y)

-- src/bvm_extras.lean:179
/-- The successor operation on sets (in particular von Neumann ordinals) -/
@[reducible] def succ (x : bSet 𝔹) := bSet.insert1 x x

-- src/bvm_extras.lean:182
@[simp] lemma subset_succ {x : bSet 𝔹} {Γ} : Γ ≤ x ⊆ᴮ (succ x) := by
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  have : z ∈ᴮ x.insert1 x = z =ᴮ x ⊔ z ∈ᴮ x := mem_insert1
  rw [this]; exact le_trans inf_le_right le_sup_right

-- src/bvm_extras.lean:185
lemma succ_eq_binary_union {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union ({x} : bSet 𝔹) x := by
  -- succ x = insert1 x x, z ∈ succ x = z =ᴮ x ⊔ z ∈ x
  -- binary_union {x} x = bv_union (insert ({x}:bSet 𝔹) {x})
  -- Elements of the pair: {x} (singleton) and x. z ∈ bv_union iff (z ∈ {x}) ⊔ (z ∈ x) = (z =ᴮ x) ⊔ (z ∈ x).
  have hbu : binary_union ({x} : bSet 𝔹) x = bv_union (insert ({x} : bSet 𝔹) {x}) := rfl
  have hmem_pair : ∀ (y : bSet 𝔹),
      y ∈ᴮ insert ({x} : bSet 𝔹) ({x} : bSet 𝔹) = y =ᴮ ({x} : bSet 𝔹) ⊔ y =ᴮ x := by
    intro y; rw [mem_insert1, mem_singleton_bSet]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have hz : Γ ⊓ z ∈ᴮ succ x ≤ z =ᴮ x ⊔ z ∈ᴮ x := inf_le_right.trans (le_of_eq mem_insert1)
    apply le_trans hz
    rw [show binary_union ({x} : bSet 𝔹) x = bv_union (insert ({x} : bSet 𝔹) ({x} : bSet 𝔹)) from hbu]
    apply sup_le
    · apply (bv_union_spec_split _ z).mpr
      apply le_iSup_of_le ({x} : bSet 𝔹)
      refine le_inf ?_ ?_
      · -- {x} ∈ insert {x} {x} = {x} =ᴮ {x} ⊔ {x} =ᴮ x ≥ z =ᴮ x since {x}=ᴮ{x}=⊤
        rw [hmem_pair]; simp [bv_eq_refl]
      · -- z ∈ {x} from z =ᴮ x (using mem_singleton_of_eq)
        exact mem_singleton_of_eq (le_of_eq bv_eq_symm)
    · apply (bv_union_spec_split _ z).mpr
      apply le_iSup_of_le x
      refine le_inf ?_ le_rfl
      · -- x ∈ insert {x} {x} = x =ᴮ {x} ⊔ x =ᴮ x ≥ ⊤ from x =ᴮ x = ⊤
        rw [hmem_pair]; simp [bv_eq_refl]
  · apply le_iInf; intro z; rw [← deduction]
    rw [show z ∈ᴮ succ x = z =ᴮ x ⊔ z ∈ᴮ x from mem_insert1]
    rw [show binary_union ({x} : bSet 𝔹) x = bv_union (insert ({x} : bSet 𝔹) ({x} : bSet 𝔹)) from hbu]
    apply le_trans ((bv_union_spec_split _ z).mp inf_le_right)
    apply iSup_le; intro y
    rw [hmem_pair, inf_sup_right]
    apply sup_le
    · -- y =ᴮ {x} ⊓ z ∈ y ≤ z =ᴮ x ⊔ z ∈ x: z ∈ {x} → z =ᴮ x
      have h1 : y =ᴮ ({x} : bSet 𝔹) ⊓ z ∈ᴮ y ≤ z ∈ᴮ ({x} : bSet 𝔹) :=
        subst_congr_mem_right
      exact le_trans h1 (le_trans (le_trans eq_of_mem_singleton' (le_of_eq bv_eq_symm)) le_sup_left)
    · -- y =ᴮ x ⊓ z ∈ y ≤ z =ᴮ x ⊔ z ∈ x: z ∈ x via subst_congr_mem_right
      exact le_trans subst_congr_mem_right le_sup_right

-- src/bvm_extras.lean:204
lemma succ_eq_binary_union' {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union x ({x} : bSet 𝔹) :=
  bv_trans succ_eq_binary_union binary_union_symm

-- src/bvm_extras.lean:207
@[reducible] def pair (x y : bSet 𝔹) : bSet 𝔹 := ({{x}, {x, y}} : bSet 𝔹)

-- src/bvm_extras.lean:209
@[simp] lemma subst_congr_pair_left {x z y : bSet 𝔹} : x =ᴮ z ≤ pair x y =ᴮ pair z y := by
  unfold pair
  -- pair x y = insert1 {x} (insert1 {x,y} ∅), pair z y = insert1 {z} (insert1 {z,y} ∅)
  -- Change {x} to {z} in head, then {x,y} to {z,y} in tail
  exact bv_trans
    (subst_congr_insert1_left' (subst_congr_insert1_left (v := (∅ : bSet 𝔹))))
    (subst_congr_insert1_left'' subst_congr_insert1_left)

-- src/bvm_extras.lean:216
@[simp] lemma subst_congr_pair_left' {x z y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x =ᴮ z → Γ ≤ pair x y =ᴮ pair z y :=
  poset_yoneda_inv Γ subst_congr_pair_left

-- src/bvm_extras.lean:219
lemma subst_congr_pair_right {x y z : bSet 𝔹} : y =ᴮ z ≤ pair x y =ᴮ pair x z := by
  unfold pair
  -- pair x y = {{x},{x,y}}, pair x z = {{x},{x,z}}
  -- y =ᴮ z → {x,y} =ᴮ {x,z}: subst_congr_insert1_left'' le_refl
  -- y =ᴮ z → {{x},{x,y}} =ᴮ {{x},{x,z}}: apply again
  exact subst_congr_insert1_left'' (subst_congr_insert1_left'' (le_refl _))

-- src/bvm_extras.lean:222
lemma subst_congr_pair_right' {Γ} {x y z : bSet 𝔹} (H : Γ ≤ y =ᴮ z) :
    Γ ≤ pair x y =ᴮ pair x z :=
  poset_yoneda_inv Γ subst_congr_pair_right H

-- src/bvm_extras.lean:225
lemma pair_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) :
    Γ ≤ pair x₁ x₂ =ᴮ pair y₁ y₂ :=
  bv_trans (subst_congr_pair_left' H₁) (subst_congr_pair_right' H₂)

-- src/bvm_extras.lean:240
@[simp] lemma B_congr_insert1_left {y : bSet 𝔹} : B_congr (fun x => bSet.insert1 x y) :=
  fun h => poset_yoneda_inv _ subst_congr_insert1_left h

-- src/bvm_extras.lean:243
@[simp] lemma B_congr_insert1_right {y : bSet 𝔹} : B_congr (fun x => bSet.insert1 y x) :=
  fun h => poset_yoneda_inv _ subst_congr_insert1_right h

-- src/bvm_extras.lean:246
@[simp] lemma B_congr_succ : B_congr (succ : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ h_eq; unfold succ
  exact bv_trans (B_congr_insert1_right h_eq) (B_congr_insert1_left h_eq)

-- src/bvm_extras.lean:257
@[simp] lemma B_congr_pair_left {y : bSet 𝔹} : B_congr (fun x => pair x y) :=
  fun h => poset_yoneda_inv _ subst_congr_pair_left h

-- src/bvm_extras.lean:260
@[simp] lemma B_congr_pair_right {y : bSet 𝔹} : B_congr (fun x => pair y x) :=
  fun h => poset_yoneda_inv _ subst_congr_pair_right h

-- src/bvm_extras.lean:263
@[simp] lemma B_ext_pair_left {ϕ : bSet 𝔹 → 𝔹} (H : B_ext ϕ) {x} :
    B_ext (fun z => ϕ (pair z x)) := B_ext_term ϕ (fun z => pair z x) H B_congr_pair_left

-- src/bvm_extras.lean:265
@[simp] lemma B_ext_pair_right {ϕ : bSet 𝔹 → 𝔹} (H : B_ext ϕ) {x} :
    B_ext (fun z => ϕ (pair x z)) := B_ext_term ϕ (fun z => pair x z) H B_congr_pair_right

-- src/bvm_extras.lean:270
@[simp] lemma B_ext_pair_mem_left {x y : bSet 𝔹} : B_ext (fun z => pair z x ∈ᴮ y) :=
  B_ext_term (fun w => w ∈ᴮ y) (fun z => pair z x) B_ext_mem_left B_congr_pair_left

-- src/bvm_extras.lean:273
@[simp] lemma B_ext_pair_mem_right {x y : bSet 𝔹} : B_ext (fun z => pair x z ∈ᴮ y) :=
  B_ext_term (fun w => w ∈ᴮ y) (fun z => pair x z) B_ext_mem_left B_congr_pair_right

-- src/bvm_extras.lean:276
lemma eq_of_eq_pair'_left {x z y : bSet 𝔹} : pair x y =ᴮ pair z y ≤ x =ᴮ z := by
  -- pair x y =ᴮ pair z y → {x} ∈ pair z y (from bv_eq_unfold at index none)
  -- {x} ∈ pair z y = {x} =ᴮ {z} ⊔ {x} =ᴮ {z,y}
  -- Both cases give x =ᴮ z: first by eq_of_eq_singleton, second by eq_inserted_of_eq_singleton
  have hL : pair x y =ᴮ pair z y ≤ ({x} : bSet 𝔹) ∈ᴮ pair z y := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (none : (pair x y).type)
    -- (pair x y).bval none = ⊤, (pair x y).func none = {x}
    simp only [show (pair x y).bval (none : (pair x y).type) = ⊤ from rfl,
               show (pair x y).func (none : (pair x y).type) = ({x} : bSet 𝔹) from rfl,
               top_imp, le_refl]
  -- {x} ∈ pair z y = {x} =ᴮ {z} ⊔ ({x} ∈ (insert ({z,y}) ∅)) = {x} =ᴮ {z} ⊔ {x} =ᴮ {z,y}
  have hmem : ({x} : bSet 𝔹) ∈ᴮ pair z y = ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({z, y} : bSet 𝔹) := by
    show ({x} : bSet 𝔹) ∈ᴮ insert ({z} : bSet 𝔹) (insert ({z, y} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) ∈ᴮ insert ({z, y} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem] at hL
  -- hL: pair x y =ᴮ pair z y ≤ {x} =ᴮ {z} ⊔ {x} =ᴮ {z,y}
  calc pair x y =ᴮ pair z y
      ≤ ({x} : bSet 𝔹) =ᴮ ({z} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({z, y} : bSet 𝔹) := hL
    _ ≤ x =ᴮ z := by
          apply sup_le
          · exact eq_of_eq_singleton le_rfl
          · exact eq_inserted_of_eq_singleton

-- src/bvm_extras.lean:287
lemma inserted_eq_of_insert_eq {y v w : bSet 𝔹} :
    ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y =ᴮ w := by
  -- From bv_eq_unfold at 'some none' in {v,y} and {v,w}:
  -- Left: {v,y} =ᴮ {v,w} ≤ y ∈ {v,w} = y =ᴮ v ⊔ y =ᴮ w
  -- Right: {v,y} =ᴮ {v,w} ≤ w ∈ {v,y} = w =ᴮ v ⊔ w =ᴮ y
  -- Both cases: (y=v ∨ y=w) ∧ (w=v ∨ w=y) → y=w
  have hL : ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y ∈ᴮ ({v, w} : bSet 𝔹) := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : ({v, y} : bSet 𝔹).type)
    -- Definitionally: bval (some none) = ⊤, func (some none) = y
    show (⊤ : 𝔹) ⟹ y ∈ᴮ ({v, w} : bSet 𝔹) ≤ y ∈ᴮ ({v, w} : bSet 𝔹)
    rw [top_imp]
  have hR : ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ w ∈ᴮ ({v, y} : bSet 𝔹) := by
    rw [bv_eq_unfold]
    apply inf_le_right.trans
    apply iInf_le_of_le (some none : ({v, w} : bSet 𝔹).type)
    show (⊤ : 𝔹) ⟹ w ∈ᴮ ({v, y} : bSet 𝔹) ≤ w ∈ᴮ ({v, y} : bSet 𝔹)
    rw [top_imp]
  -- y ∈ {v,w} = y =ᴮ v ⊔ y =ᴮ w
  have hmem_yw : y ∈ᴮ ({v, w} : bSet 𝔹) = y =ᴮ v ⊔ y =ᴮ w := by
    show y ∈ᴮ insert v ({w} : bSet 𝔹) = _
    rw [mem_insert1, mem_singleton_bSet]
    have : y ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  -- w ∈ {v,y} = w =ᴮ v ⊔ w =ᴮ y
  have hmem_wvy : w ∈ᴮ ({v, y} : bSet 𝔹) = w =ᴮ v ⊔ w =ᴮ y := by
    show w ∈ᴮ insert v ({y} : bSet 𝔹) = _
    rw [mem_insert1, mem_singleton_bSet]
    have : w ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    rw [this, sup_bot_eq]
  rw [hmem_yw] at hL; rw [hmem_wvy] at hR
  calc ({v, y} : bSet 𝔹) =ᴮ {v, w}
      ≤ (y =ᴮ v ⊔ y =ᴮ w) ⊓ (w =ᴮ v ⊔ w =ᴮ y) := le_inf hL hR
    _ ≤ y =ᴮ w := by
          -- (y=v ⊔ y=w) ⊓ (w=v ⊔ w=y) ≤ y=w
          -- Step 1: distribute via inf_sup_right: (y=v ⊓ (w=v⊔w=y)) ⊔ (y=w ⊓ (w=v⊔w=y)) ≤ y=w
          have step : (y =ᴮ v ⊔ y =ᴮ w) ⊓ (w =ᴮ v ⊔ w =ᴮ y)
              ≤ (y =ᴮ v ⊓ (w =ᴮ v ⊔ w =ᴮ y)) ⊔ (y =ᴮ w ⊓ (w =ᴮ v ⊔ w =ᴮ y)) :=
            le_of_eq (inf_sup_right _ _ _)
          apply le_trans step
          apply sup_le
          · -- y=v ⊓ (w=v ⊔ w=y) ≤ y=w
            have step2 : y =ᴮ v ⊓ (w =ᴮ v ⊔ w =ᴮ y)
                ≤ (y =ᴮ v ⊓ w =ᴮ v) ⊔ (y =ᴮ v ⊓ w =ᴮ y) :=
              le_of_eq (inf_sup_left _ _ _)
            apply le_trans step2
            apply sup_le
            · -- y=v ⊓ w=v ≤ y=w: y=v, w=v → w=y, then y=w
              rw [inf_comm]
              exact le_trans (inf_le_inf_left _ (le_of_eq bv_eq_symm))
                (le_trans bv_eq_trans (le_of_eq bv_eq_symm))
            · -- y=v ⊓ w=y ≤ y=w: w=y → y=w
              exact inf_le_right.trans (le_of_eq bv_eq_symm)
          · exact inf_le_left

-- src/bvm_extras.lean:297
lemma eq_of_eq_pair'_right {x z y : bSet 𝔹} : pair y x =ᴮ pair y z ≤ x =ᴮ z := by
  -- Approach: pair y x =ᴮ pair y z → {y,x} ∈ pair y z (from left bv_eq at some none)
  -- {y,x} ∈ pair y z = {y,x} =ᴮ {y} ⊔ {y,x} =ᴮ {y,z}
  -- Also pair y x =ᴮ pair y z → {y,z} ∈ pair y x (from right bv_eq at some none)
  -- {y,z} ∈ pair y x = {y,z} =ᴮ {y} ⊔ {y,z} =ᴮ {y,x}
  -- From {y,x}=ᴮ{y}: x=ᴮy (specialize at some none of {y,x})
  -- From {y,x}=ᴮ{y,z}: x=ᴮz (by inserted_eq_of_insert_eq)
  -- From {y,z}=ᴮ{y}: z=ᴮy
  -- From {y,z}=ᴮ{y,x}: z=ᴮx=bv_eq_symm→x=ᴮz (by inserted_eq_of_insert_eq)
  -- Helper: {v,u} =ᴮ {v} ≤ u =ᴮ v (from left bv_eq at some none)
  have pair_eq_sing_le : ∀ (u v : bSet 𝔹), (insert v ({u} : bSet 𝔹) : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ≤ u =ᴮ v := by
    intro u v
    -- From left bv_eq at 'some none': bval(some none) = ⊤, func(some none) = u
    -- So pair_eq_sing_le extracts u ∈ {v} which gives u=v by eq_of_mem_singleton'
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : (insert v ({u} : bSet 𝔹) : bSet 𝔹).type)
    -- Goal: {v,u}.bval(some none) ⟹ {v,u}.func(some none) ∈ {v} ≤ u =ᴮ v
    -- {v,u} = bSet.insert1 v {u}, so:
    -- .bval(some none) = ({u}).bval none = ⊤ by insert1_bval_some + singleton_bval_none
    -- .func(some none) = ({u}).func none = u by insert1_func_some + singleton_func
    -- {v,u}.bval(some none) = ⊤ and {v,u}.func(some none) = u: use insert1_bval_some/func_some
    -- but {v,u} = bSet.insert1 v {u} = insert v {u} so rw uses the same expression
    -- Use conv to rewrite inside the imp
    conv_lhs =>
      rw [show ({v, u} : bSet 𝔹).bval (some none : ({v, u} : bSet 𝔹).type) = ⊤ from by
        show (bSet.insert1 v ({u} : bSet 𝔹)).bval (some none) = ⊤
        rw [insert1_bval_some]; exact singleton_bval_none]
      rw [show ({v, u} : bSet 𝔹).func (some none : ({v, u} : bSet 𝔹).type) = u from by
        show (bSet.insert1 v ({u} : bSet 𝔹)).func (some none) = u
        rw [insert1_func_some]; rfl]
    rw [top_imp]
    exact le_trans eq_of_mem_singleton' (le_of_eq bv_eq_symm)
  -- Extract {y,x} ∈ pair y z and {y,z} ∈ pair y x
  have hL : pair y x =ᴮ pair y z ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (some none : (pair y x).type)
    show (⊤ : 𝔹) ⟹ ({y, x} : bSet 𝔹) ∈ᴮ pair y z ≤ ({y, x} : bSet 𝔹) ∈ᴮ pair y z
    rw [top_imp]
  have hR : pair y x =ᴮ pair y z ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x := by
    rw [bv_eq_unfold]
    apply inf_le_right.trans
    apply iInf_le_of_le (some none : (pair y z).type)
    show (⊤ : 𝔹) ⟹ ({y, z} : bSet 𝔹) ∈ᴮ pair y x ≤ ({y, z} : bSet 𝔹) ∈ᴮ pair y x
    rw [top_imp]
  -- Membership in pair y z: {y,x} ∈ pair y z = {y,x} =ᴮ {y} ⊔ {y,x} =ᴮ {y,z}
  have hmem_yz : ({y, x} : bSet 𝔹) ∈ᴮ pair y z = ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, x} : bSet 𝔹) =ᴮ ({y, z} : bSet 𝔹) := by
    show ({y, x} : bSet 𝔹) ∈ᴮ insert ({y} : bSet 𝔹) (insert ({y, z} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({y, x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({y, x} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, x} : bSet 𝔹) ∈ᴮ insert ({y, z} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  have hmem_yx : ({y, z} : bSet 𝔹) ∈ᴮ pair y x = ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, z} : bSet 𝔹) =ᴮ ({y, x} : bSet 𝔹) := by
    show ({y, z} : bSet 𝔹) ∈ᴮ insert ({y} : bSet 𝔹) (insert ({y, x} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({y, z} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({y, z} : bSet 𝔹) =ᴮ ({y} : bSet 𝔹) ⊔ ({y, z} : bSet 𝔹) ∈ᴮ insert ({y, x} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem_yz] at hL; rw [hmem_yx] at hR
  -- hL: Γ ≤ ({y,x}=ᴮ{y} ⊔ {y,x}=ᴮ{y,z})
  -- hR: Γ ≤ ({y,z}=ᴮ{y} ⊔ {y,z}=ᴮ{y,x})
  calc pair y x =ᴮ pair y z
      ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊔ ({y, x} : bSet 𝔹) =ᴮ {y, z}) ⊓
        (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x}) := le_inf hL hR
    _ ≤ x =ᴮ z := by
          -- (A₁⊔A₂) ⊓ (B₁⊔B₂) where A₁={y,x}={y}, A₂={y,x}={y,z}, B₁={y,z}={y}, B₂={y,z}={y,x}
          have step : (({y, x} : bSet 𝔹) =ᴮ {y} ⊔ ({y, x} : bSet 𝔹) =ᴮ {y, z}) ⊓
              (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})
              ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})) ⊔
                (({y, x} : bSet 𝔹) =ᴮ {y, z} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})) :=
            le_of_eq (inf_sup_right _ _ _)
          apply le_trans step
          apply sup_le
          · -- A₁ ⊓ (B₁⊔B₂): {y,x}=ᴮ{y} ⊓ (...)
            have step2 : ({y, x} : bSet 𝔹) =ᴮ {y} ⊓ (({y, z} : bSet 𝔹) =ᴮ {y} ⊔ ({y, z} : bSet 𝔹) =ᴮ {y, x})
                ≤ (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y}) ⊔
                  (({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y, x}) :=
              le_of_eq (inf_sup_left _ _ _)
            apply le_trans step2
            apply sup_le
            · -- {y,x}=ᴮ{y} ⊓ {y,z}=ᴮ{y}: x=y, z=y → x=z
              have hxy := pair_eq_sing_le x y
              have hzy := pair_eq_sing_le z y
              calc ({y, x} : bSet 𝔹) =ᴮ {y} ⊓ ({y, z} : bSet 𝔹) =ᴮ {y}
                  ≤ x =ᴮ y ⊓ z =ᴮ y := le_inf (inf_le_left.trans hxy) (inf_le_right.trans hzy)
                _ ≤ x =ᴮ z := by
                    rw [inf_comm]
                    exact le_trans (inf_le_inf_left _ (le_of_eq bv_eq_symm))
                      (le_trans bv_eq_trans (le_of_eq bv_eq_symm))
            · -- {y,x}=ᴮ{y} ⊓ {y,z}=ᴮ{y,x}: z=x → x=z
              have hzx : ({y, z} : bSet 𝔹) =ᴮ {y, x} ≤ z =ᴮ x := inserted_eq_of_insert_eq
              exact inf_le_right.trans (hzx.trans (le_of_eq bv_eq_symm))
          · -- A₂ ⊓ (B₁⊔B₂): {y,x}=ᴮ{y,z} → x=z
            exact inf_le_left.trans inserted_eq_of_insert_eq

-- src/bvm_extras.lean:316
theorem eq_of_eq_pair_left {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ x =ᴮ v := by
  -- Same as eq_of_eq_pair'_left: extract {x} ∈ pair v w from left bv_eq at none
  have hL : pair x y =ᴮ pair v w ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w := by
    rw [bv_eq_unfold]
    apply inf_le_left.trans
    apply iInf_le_of_le (none : (pair x y).type)
    show (⊤ : 𝔹) ⟹ ({x} : bSet 𝔹) ∈ᴮ pair v w ≤ ({x} : bSet 𝔹) ∈ᴮ pair v w
    rw [top_imp]
  have hmem : ({x} : bSet 𝔹) ∈ᴮ pair v w = ({x} : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) =ᴮ ({v, w} : bSet 𝔹) := by
    show ({x} : bSet 𝔹) ∈ᴮ insert ({v} : bSet 𝔹) (insert ({v, w} : bSet 𝔹) ∅) = _
    rw [mem_insert1]
    have : ({x} : bSet 𝔹) ∈ᴮ (∅ : bSet 𝔹) = ⊥ := by rw [mem_unfold]; exact exists_over_empty _
    show ({x} : bSet 𝔹) =ᴮ ({v} : bSet 𝔹) ⊔ ({x} : bSet 𝔹) ∈ᴮ insert ({v, w} : bSet 𝔹) ∅ = _
    rw [mem_insert1, this, sup_bot_eq]
  rw [hmem] at hL
  exact hL.trans (sup_le (eq_of_eq_singleton le_rfl) eq_inserted_of_eq_singleton)

-- src/bvm_extras.lean:330
lemma eq_of_eq_pair_left' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ x =ᴮ v :=
  poset_yoneda_inv Γ eq_of_eq_pair_left

-- src/bvm_extras.lean:333
theorem eq_of_eq_pair_right {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ y =ᴮ w := by
  -- From pair x y =ᴮ pair v w:
  -- 1. Get x =ᴮ v by eq_of_eq_pair_left
  -- 2. From x =ᴮ v, pair x y =ᴮ pair v y (by subst_congr_pair_left, symm)
  -- 3. pair v y =ᴮ pair v w from transitivity
  -- 4. Use eq_of_eq_pair'_right to get y =ᴮ w
  -- Step: pair x y =ᴮ pair v w ⊓ (pair x y =ᴮ pair v w) ≤ pair v y =ᴮ pair v w
  -- From pair x y =ᴮ pair v w, x =ᴮ v by eq_of_eq_pair_left.
  -- pair x y =ᴮ pair v y from x =ᴮ v (by subst_congr_pair_left with h:= bv_eq_symm).
  -- Then pair v y =ᴮ pair v w by bv_eq_trans of pair x y =ᴮ pair v y (symm) and pair x y =ᴮ pair v w.
  -- Then y =ᴮ w by eq_of_eq_pair'_right.
  calc pair x y =ᴮ pair v w
      ≤ pair v y =ᴮ pair v w := by
          -- From pair x y =ᴮ pair v w, get pair v y =ᴮ pair v w via:
          -- pair x y =ᴮ pair v y (from x =ᴮ v) and pair x y =ᴮ pair v w → pair v y =ᴮ pair v w
          -- pair v y =ᴮ pair v w = symm(pair x y =ᴮ pair v y) ⊓ (pair x y =ᴮ pair v w) → bv_eq_trans
          have hxv : pair x y =ᴮ pair v w ≤ x =ᴮ v := eq_of_eq_pair_left
          have hpair : pair x y =ᴮ pair v w ≤ pair x y =ᴮ pair v y := by
            -- x =ᴮ v → pair v y =ᴮ pair x y (by subst_congr_pair_left with args flipped)
            -- then pair v y =ᴮ pair x y ≤ pair x y =ᴮ pair v y (by bv_eq_symm)
            exact le_trans hxv (le_trans (le_of_eq bv_eq_symm)
              (le_trans subst_congr_pair_left (le_of_eq bv_eq_symm)))
          -- pair v y =ᴮ pair v w from: symm(pair x y =ᴮ pair v y) and (pair x y =ᴮ pair v w)
          apply le_trans (le_inf (le_trans hpair (le_of_eq bv_eq_symm)) le_rfl)
          exact bv_eq_trans
    _ ≤ y =ᴮ w := eq_of_eq_pair'_right

-- src/bvm_extras.lean:342
lemma eq_of_eq_pair_right' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ y =ᴮ w :=
  poset_yoneda_inv Γ eq_of_eq_pair_right

-- src/bvm_extras.lean:345
lemma eq_of_eq_pair {x y z w : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ pair x y =ᴮ pair z w) :
    Γ ≤ x =ᴮ z ∧ Γ ≤ y =ᴮ w :=
  ⟨eq_of_eq_pair_left' H_eq, eq_of_eq_pair_right' H_eq⟩

-- src/bvm_extras.lean:349
lemma pair_eq_pair_iff {x y x' y' : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y =ᴮ pair x' y' ↔ Γ ≤ x =ᴮ x' ∧ Γ ≤ y =ᴮ y' :=
  ⟨fun h => eq_of_eq_pair h, fun ⟨h₁, h₂⟩ => pair_congr h₁ h₂⟩

-- src/bvm_extras.lean:353
@[reducible] def prod (v w : bSet 𝔹) : bSet 𝔹 :=
  ⟨v.type × w.type, fun a => pair (v.func a.1) (w.func a.2), fun a => v.bval a.1 ⊓ w.bval a.2⟩

-- src/bvm_extras.lean:355
@[simp] lemma prod_type {v w : bSet 𝔹} : (prod v w).type = (v.type × w.type) := rfl

-- src/bvm_extras.lean:357
@[simp] lemma prod_func {v w : bSet 𝔹} {pr} :
    (prod v w).func pr = pair (v.func pr.1) (w.func pr.2) := rfl

-- src/bvm_extras.lean:360
@[simp] lemma prod_bval {v w : bSet 𝔹} {a b} :
    (prod v w).bval (a, b) = v.bval a ⊓ w.bval b := rfl

-- src/bvm_extras.lean:362
@[simp] lemma prod_type_forall {v w : bSet 𝔹} {ϕ : (prod v w).type → 𝔹} :
    (⨅ (z : (prod v w).type), ϕ z) = ⨅ (z : v.type × w.type), ϕ z := rfl

-- src/bvm_extras.lean:366
@[simp] lemma prod_check_bval {x y : PSet.{u}} {pr} :
    (prod (check x) (check y) : bSet 𝔹).bval pr = ⊤ := by
  cases pr; simp only [prod_bval, check_bval_top, top_inf_eq]

-- src/bvm_extras.lean:371
lemma prod_mem_old {v w x y : bSet 𝔹} :
    x ∈ᴮ v ⊓ y ∈ᴮ w ≤ pair x y ∈ᴮ prod v w := by
  -- From x ∈ v and y ∈ w, show pair x y ∈ prod v w
  -- prod v w has type v.type × w.type, func (i,j) = pair (v.func i) (w.func j), bval (i,j) = v.bval i ⊓ w.bval j
  rw [mem_unfold, mem_unfold, mem_unfold]
  -- (⨆ i, v.bval i ⊓ x =ᴮ v.func i) ⊓ (⨆ j, w.bval j ⊓ y =ᴮ w.func j)
  -- ≤ ⨆ p : v.type × w.type, (v.bval p.1 ⊓ w.bval p.2) ⊓ pair x y =ᴮ pair (v.func p.1) (w.func p.2)
  rw [iSup_inf_iSup]
  apply iSup_le; intro ⟨i, j⟩
  -- (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ ...
  apply le_iSup_of_le (i, j)
  simp only [prod_bval, prod_func]
  -- Need: (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j)
  --   ≤ (v.bval i ⊓ w.bval j) ⊓ pair x y =ᴮ pair (v.func i) (w.func j)
  refine le_inf (le_inf ?_ ?_) ?_
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right.trans inf_le_left
  · -- pair x y =ᴮ pair (v.func i) (w.func j) from x =ᴮ v.func i and y =ᴮ w.func j
    have hx : (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ x =ᴮ v.func i :=
      inf_le_left.trans inf_le_right
    have hy : (v.bval i ⊓ x =ᴮ v.func i) ⊓ (w.bval j ⊓ y =ᴮ w.func j) ≤ y =ᴮ w.func j :=
      inf_le_right.trans inf_le_right
    exact pair_congr hx hy

-- src/bvm_extras.lean:389
lemma prod_mem {v w x y : bSet 𝔹} {Γ} : Γ ≤ x ∈ᴮ v → Γ ≤ y ∈ᴮ w → Γ ≤ pair x y ∈ᴮ prod v w :=
  fun H₁ H₂ => le_trans (le_inf H₁ H₂) prod_mem_old

-- src/bvm_extras.lean:392
lemma mem_left_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ x ∈ᴮ v := by
  sorry -- TODO: port from src/bvm_extras.lean:392

-- src/bvm_extras.lean:400
lemma mem_right_of_prod_mem {v w x y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair x y ∈ᴮ prod v w → Γ ≤ y ∈ᴮ w := by
  sorry -- TODO: port from src/bvm_extras.lean:400

-- src/bvm_extras.lean:408
@[simp] lemma mem_prod_iff {v w x y : bSet 𝔹} {Γ} :
    Γ ≤ pair x y ∈ᴮ prod v w ↔ (Γ ≤ x ∈ᴮ v ∧ Γ ≤ y ∈ᴮ w) :=
  ⟨fun h => ⟨mem_left_of_prod_mem h, mem_right_of_prod_mem h⟩, fun ⟨h₁, h₂⟩ => prod_mem h₁ h₂⟩

-- src/bvm_extras.lean:411
@[simp] lemma mem_prod {v w x y : bSet 𝔹} {Γ} (H_mem₁ : Γ ≤ x ∈ᴮ v) (H_mem₂ : Γ ≤ y ∈ᴮ w) :
    Γ ≤ pair x y ∈ᴮ prod v w :=
  mem_prod_iff.mpr ⟨H_mem₁, H_mem₂⟩

-- src/bvm_extras.lean:415
@[simp] lemma B_congr_prod_left {y : bSet 𝔹} : B_congr (fun x => prod x y) := by
  intro a b Γ H_eq
  rw [bv_eq_unfold]
  simp only [prod_type, prod_bval, prod_func]
  -- Need two sides: prod a y ⊆ prod b y and prod b y ⊆ prod a y
  refine le_inf (le_iInf fun ⟨i, j⟩ => ?_) (le_iInf fun ⟨i, j⟩ => ?_)
  · -- (prod a y).bval (i,j) ⟹ pair (a.func i) (y.func j) ∈ prod b y
    rw [← deduction]
    -- Context: Γ ⊓ (a.bval i ⊓ y.bval j)
    have hai : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ a.func i ∈ᴮ a :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' a i))
    have hab : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ a.func i ∈ᴮ b :=
      bv_rw' (bv_symm (le_trans inf_le_left H_eq)) (ϕ := fun z => a.func i ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hai)
    have hyj : Γ ⊓ (a.bval i ⊓ y.bval j) ≤ y.func j ∈ᴮ y :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' y j))
    exact prod_mem hab hyj
  · -- (prod b y).bval (i,j) ⟹ pair (b.func i) (y.func j) ∈ prod a y
    rw [← deduction]
    -- Context: Γ ⊓ (b.bval i ⊓ y.bval j)
    have hbi : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ b.func i ∈ᴮ b :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' b i))
    have hba : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ b.func i ∈ᴮ a :=
      bv_rw' (le_trans inf_le_left H_eq) (ϕ := fun z => b.func i ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hbi)
    have hyj : Γ ⊓ (b.bval i ⊓ y.bval j) ≤ y.func j ∈ᴮ y :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' y j))
    exact prod_mem hba hyj

-- src/bvm_extras.lean:428
@[simp] lemma B_congr_prod_right {x : bSet 𝔹} : B_congr (fun y => prod x y) := by
  intro a b Γ H_eq
  rw [bv_eq_unfold]
  simp only [prod_type, prod_bval, prod_func]
  refine le_inf (le_iInf fun ⟨i, j⟩ => ?_) (le_iInf fun ⟨i, j⟩ => ?_)
  · -- (x.bval i ⊓ a.bval j) ⟹ pair (x.func i) (a.func j) ∈ prod x b
    rw [← deduction]
    have hxi : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' x i))
    have haj : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ a.func j ∈ᴮ a :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' a j))
    have hab : Γ ⊓ (x.bval i ⊓ a.bval j) ≤ a.func j ∈ᴮ b :=
      bv_rw' (bv_symm (le_trans inf_le_left H_eq)) (ϕ := fun z => a.func j ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := haj)
    exact prod_mem hxi hab
  · -- (x.bval i ⊓ b.bval j) ⟹ pair (x.func i) (b.func j) ∈ prod x a
    rw [← deduction]
    have hxi : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ x.func i ∈ᴮ x :=
      le_trans inf_le_right (le_trans inf_le_left (mem_mk' x i))
    have hbj : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ b.func j ∈ᴮ b :=
      le_trans inf_le_right (le_trans inf_le_right (mem_mk' b j))
    have hba : Γ ⊓ (x.bval i ⊓ b.bval j) ≤ b.func j ∈ᴮ a :=
      bv_rw' (le_trans inf_le_left H_eq) (ϕ := fun z => b.func j ∈ᴮ z)
        (h_congr := B_ext_mem_right) (H_new := hbj)
    exact prod_mem hxi hba

-- src/bvm_extras.lean:441
lemma prod_congr {x₁ x₂ y₁ y₂ : bSet 𝔹} {Γ} (H₁ : Γ ≤ x₁ =ᴮ x₂) (H₂ : Γ ≤ y₁ =ᴮ y₂) :
    Γ ≤ prod x₁ y₁ =ᴮ prod x₂ y₂ :=
  bv_trans (B_congr_prod_left H₁) (B_congr_prod_right H₂)

-- src/bvm_extras.lean:448
lemma mem_prod_iff₂ {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ∈ᴮ prod x y ↔
    ∃ v, ∃ _hv : Γ ≤ v ∈ᴮ x, ∃ w, ∃ _hw : Γ ≤ w ∈ᴮ y, Γ ≤ z =ᴮ pair v w := by
  constructor
  · intro H; sorry -- TODO: port from src/bvm_extras.lean:448
  · intro ⟨v, Hv, w, Hw, H_eq⟩
    sorry -- TODO: z =ᴮ pair v w and pair v w ∈ prod x y → z ∈ prod x y

-- src/bvm_extras.lean:465
lemma prod_ext {S₁ S₂ x y : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ S₁ ⊆ᴮ prod x y) (H₂ : Γ ≤ S₂ ⊆ᴮ prod x y)
    (H_prod_ext : Γ ≤ ⨅ v, v ∈ᴮ x ⟹ ⨅ w, w ∈ᴮ y ⟹ (pair v w ∈ᴮ S₁ ⇔ pair v w ∈ᴮ S₂)) :
    Γ ≤ S₁ =ᴮ S₂ := by
  sorry -- TODO: port from src/bvm_extras.lean:465

-- src/bvm_extras.lean:489
@[simp] lemma check_singleton {x : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ check ({x} : PSet) =ᴮ ({check x} : bSet 𝔹) := by
  have h : check ({x} : PSet) = ({check x} : bSet 𝔹) := by
    show check (PSet.insert x ∅) = bSet.insert1 (check x) ∅
    rw [check_insert]; simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

-- src/bvm_extras.lean:494
@[simp] lemma check_unordered_pair {x y : PSet.{u}} {Γ} :
    Γ ≤ check ({x, y} : PSet) =ᴮ ({check x, check y} : bSet 𝔹) := by
  have h : check ({x, y} : PSet) = ({check x, check y} : bSet 𝔹) := by
    show check (PSet.insert x (PSet.insert y ∅)) = bSet.insert1 (check x) (bSet.insert1 (check y) ∅)
    rw [check_insert, check_insert]; simp [check_empty_eq_empty]
  rw [h]; exact bv_refl

-- src/bvm_extras.lean:499
@[simp] lemma eq_unordered_pair_of_eq {a b c d : bSet 𝔹} {Γ} (H₁ : Γ ≤ a =ᴮ c)
    (H₂ : Γ ≤ b =ᴮ d) : Γ ≤ ({a, b} : bSet 𝔹) =ᴮ {c, d} :=
  bv_trans (subst_congr_insert1_left' H₁) (subst_congr_insert1_left'' H₂)

-- src/bvm_extras.lean:506
-- (In Lean 4 port, PSet.pair is PSet.pSet_pair from PSetOrdinal.lean)
lemma check_pset_pair {x y : PSet.{u}} {Γ} :
    Γ ≤ check (PSet.pSet_pair x y) =ᴮ pair (check x) (check y : bSet 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:506 (PSet.pSet_pair uses PSetOrdinal defs)

-- src/bvm_extras.lean:514
-- (In Lean 4 port, PSet.prod is PSet.pSet_prod from PSetOrdinal.lean)
lemma check_pset_prod {x y : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ check (PSet.pSet_prod x y) =ᴮ prod (check x) (check y) := by
  sorry -- TODO: port from src/bvm_extras.lean:514

-- src/bvm_extras.lean:535
/-- f is =ᴮ-extensional if for every w₁ w₂ v₁ v₂, if pair (w₁ v₁) and pair (w₂ v₂) ∈ f and
    w₁ =ᴮ w₂, then v₁ =ᴮ v₂ -/
@[reducible] def is_func (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅ w₂, ⨅ v₁, ⨅ v₂, pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)

-- src/bvm_extras.lean:538
@[simp] lemma is_func_subset_of_is_func {f g : bSet 𝔹} {Γ} (H : Γ ≤ is_func f)
    (H_sub : Γ ≤ g ⊆ᴮ f) : Γ ≤ is_func g := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  -- Γ ⊓ (pair w₁ v₁ ∈ g ⊓ pair w₂ v₂ ∈ g) ≤ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  have hspec : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤
      pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂) :=
    le_trans (le_trans inf_le_left H)
      (iInf_le _ w₁ |>.trans (iInf_le _ w₂) |>.trans (iInf_le _ v₁) |>.trans (iInf_le _ v₂))
  have hmem₁ : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤ pair w₁ v₁ ∈ᴮ f :=
    mem_of_mem_subset (le_trans inf_le_left H_sub) (inf_le_right.trans inf_le_left)
  have hmem₂ : Γ ⊓ (pair w₁ v₁ ∈ᴮ g ⊓ pair w₂ v₂ ∈ᴮ g) ≤ pair w₂ v₂ ∈ᴮ f :=
    mem_of_mem_subset (le_trans inf_le_left H_sub) (inf_le_right.trans inf_le_right)
  exact le_trans (le_inf hspec (le_inf hmem₁ hmem₂)) bv_imp_elim

-- src/bvm_extras.lean:548
@[reducible] def is_functional (f : bSet 𝔹) : 𝔹 :=
  ⨅ z, (⨆ w, pair z w ∈ᴮ f) ⟹ (⨆ w', ⨅ w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'')

-- src/bvm_extras.lean:551
lemma is_functional_of_is_func (f : bSet 𝔹) {Γ} (H : Γ ≤ is_func f) : Γ ≤ is_functional f := by
  unfold is_functional
  apply le_iInf; intro z; rw [← deduction]
  -- Γ ⊓ ⨆ w, pair z w ∈ᴮ f ≤ ⨆ w', ⨅ w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w''
  rw [inf_comm]
  calc (⨆ w, pair z w ∈ᴮ f) ⊓ Γ
      ≤ ⨆ w, pair z w ∈ᴮ f ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ w', ⨅ w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'' := by
        apply iSup_le; intro w
        apply le_iSup_of_le w
        apply le_iInf; intro w'; rw [← deduction]
        -- pair z w ∈ f ⊓ Γ ⊓ pair z w' ∈ f ≤ w =ᴮ w'
        -- is_func f says: pair z w ∈ f ⊓ pair z w' ∈ f ⟹ (z =ᴮ z ⟹ w =ᴮ w')
        have hspec : pair z w ∈ᴮ f ⊓ Γ ⊓ pair z w' ∈ᴮ f ≤
            pair z w ∈ᴮ f ⊓ pair z w' ∈ᴮ f ⟹ (z =ᴮ z ⟹ w =ᴮ w') :=
          le_trans (le_trans (inf_le_left.trans inf_le_right) H)
            (iInf_le _ z |>.trans (iInf_le _ z) |>.trans (iInf_le _ w) |>.trans (iInf_le _ w'))
        have hmem : pair z w ∈ᴮ f ⊓ Γ ⊓ pair z w' ∈ᴮ f ≤ pair z w ∈ᴮ f ⊓ pair z w' ∈ᴮ f :=
          le_inf (inf_le_left.trans inf_le_left) inf_le_right
        exact le_trans (le_inf (le_trans (le_inf hspec hmem) bv_imp_elim) bv_refl) bv_imp_elim

-- src/bvm_extras.lean:561
@[reducible] def is_total (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f

-- src/bvm_extras.lean:565
@[reducible] def is_total' (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ i, x.bval i ⟹ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ f

-- src/bvm_extras.lean:568
lemma is_total_iff_is_total' {Γ : 𝔹} {x y f} :
    Γ ≤ is_total x y f ↔ Γ ≤ is_total' x y f := by
  -- Prove is_total = is_total' at the value level, then rewrite
  -- bounded_forall converts ⨅ i, x.bval i ⟹ ψ (x.func i) ↔ ⨅ w, w ∈ x ⟹ ψ w
  -- bounded_exists converts ⨆ j, y.bval j ⊓ ϕ (y.func j) ↔ ⨆ w, w ∈ y ⊓ ϕ w
  -- Prove is_total = is_total' using bounded_forall and bounded_exists
  suffices h : is_total x y f = is_total' x y f by rw [h]
  simp only [is_total, is_total']
  -- Step 1: expand inner ⨆ on LHS via bounded_exists
  have inner_eq : ∀ w₁ : bSet 𝔹, (⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
      (⨆ j : y.type, y.bval j ⊓ pair w₁ (y.func j) ∈ᴮ f) :=
    fun w₁ => (@bounded_exists 𝔹 _ y (fun w₂ => pair w₁ w₂ ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right)).symm
  -- Step 2: expand outer ⨅ via bounded_forall
  rw [show (⨅ w₁ : bSet 𝔹, w₁ ∈ᴮ x ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) =
       (⨅ i : x.type, x.bval i ⟹ ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair (x.func i) w₂ ∈ᴮ f) from
    (@bounded_forall 𝔹 _ x (fun w₁ => ⨆ w₂ : bSet 𝔹, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f)
      (h_congr := fun w₁ w₂ =>
        B_ext_iSup (h := fun w₂ => B_ext_inf B_ext_const B_ext_pair_mem_left) w₁ w₂)).symm]
  congr 1; ext i
  congr 1
  exact inner_eq (x.func i)

-- src/bvm_extras.lean:581
@[simp] lemma is_total_subset_of_is_total {S x y f : bSet 𝔹} {Γ}
    (H_is_total : Γ ≤ is_total x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_total S y f := by
  apply le_iInf; intro z; rw [← deduction]
  exact le_trans (le_inf
    (le_trans (le_trans inf_le_left H_is_total) (iInf_le _ z))
    (mem_of_mem_subset (inf_le_left.trans H_subset) inf_le_right)) bv_imp_elim

/-- f is (more precisely, contains) a function from x to y -/
-- src/bvm_extras.lean:585
@[reducible] def is_func' (x y f : bSet 𝔹) : 𝔹 :=
  is_func f ⊓ is_total x y f

-- src/bvm_extras.lean:588
@[simp] lemma is_func_of_is_func' {x y f : bSet 𝔹} {Γ} (H : Γ ≤ is_func' x y f) :
    Γ ≤ is_func f := le_trans H inf_le_left

-- src/bvm_extras.lean:591
lemma is_total_of_is_func' {x y f : bSet 𝔹} {Γ : 𝔹} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_total x y f := le_trans H_is_func' inf_le_right

-- src/bvm_extras.lean:595
lemma is_func'_empty {Γ : 𝔹} {x} : Γ ≤ is_func' (∅ : bSet 𝔹) x ∅ := by
  apply le_inf
  · apply le_iInf; intro w₁; apply le_iInf; intro w₂; apply le_iInf; intro v₁; apply le_iInf; intro v₂
    rw [← deduction]
    -- pair w₁ v₁ ∈ ∅ ⊓ pair w₂ v₂ ∈ ∅ ≤ ⊥
    exact le_trans (bot_of_mem_empty (inf_le_right.trans inf_le_left)) bot_le
  · exact forall_empty

-- src/bvm_extras.lean:604
-- aka function extensionality
@[simp] lemma eq_of_is_func_of_eq {x y f x' y' : bSet 𝔹} {Γ : 𝔹} (H_is_func : Γ ≤ is_func f)
    (H_eq₁ : Γ ≤ x =ᴮ y) (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) :
    Γ ≤ x' =ᴮ y' := by
  -- is_func f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)
  have hspec := le_trans H_is_func
    (iInf_le _ x |>.trans (iInf_le _ y) |>.trans (iInf_le _ x') |>.trans (iInf_le _ y'))
  -- hspec : Γ ≤ pair x x' ∈ f ⊓ pair y y' ∈ f ⟹ (x =ᴮ y ⟹ x' =ᴮ y')
  exact le_trans (le_inf (le_trans (le_inf hspec (le_inf H_mem₁ H_mem₂)) bv_imp_elim) H_eq₁) bv_imp_elim

-- src/bvm_extras.lean:610
-- aka function extensionality
@[simp] lemma eq_of_is_func'_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (H_is_func' : Γ ≤ is_func' a b f) (H_eq₁ : Γ ≤ x =ᴮ y)
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
  eq_of_is_func_of_eq (is_func_of_is_func' H_is_func') H_eq₁ H_mem₁ H_mem₂

-- src/bvm_extras.lean:614
@[simp] lemma is_func'_subset_of_is_func' {S x y f : bSet 𝔹} {Γ : 𝔹}
    (H_is_func : Γ ≤ is_func' x y f) (H_subset : Γ ≤ S ⊆ᴮ x) : Γ ≤ is_func' S y f :=
  le_inf (is_func_of_is_func' H_is_func)
         (is_total_subset_of_is_total (is_total_of_is_func' H_is_func) H_subset)

-- src/bvm_extras.lean:622
-- bounded image
def image (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun j : y.type => ⨆ z, z ∈ᴮ x ⊓ pair z (y.func j) ∈ᴮ f)

-- src/bvm_extras.lean:625
@[simp] lemma image_subset {x y f : bSet 𝔹} {Γ} : Γ ≤ image x y f ⊆ᴮ y :=
  subset.mk_subset

-- src/bvm_extras.lean:628
@[simp] lemma mem_image {x y a b f : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) :
    Γ ≤ b ∈ᴮ image x y f := by
  -- image x y f = subset.mk (fun j : y.type => ⨆ z, z ∈ x ⊓ pair z (y.func j) ∈ f)
  unfold image
  rw [mem_subset.mk_iff]
  -- Need: Γ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ y.bval i)
  -- Extract index i from b ∈ y, augmenting with Γ to access H_mem and H_mem''
  rw [mem_unfold] at H_mem'
  calc Γ ≤ (⨆ i, y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ := le_inf H_mem' le_rfl
    _ ≤ ⨆ i, (y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f) ⊓ y.bval i) := by
          apply iSup_le; intro i
          apply le_iSup_of_le i
          -- Context: (y.bval i ⊓ b =ᴮ y.func i) ⊓ Γ
          refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))
          -- Need: ... ≤ ⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f
          apply le_iSup_of_le a
          -- Need: ... ≤ a ∈ x ⊓ pair a (y.func i) ∈ f
          refine le_inf (inf_le_right.trans H_mem'') ?_
          -- pair a (y.func i) ∈ f from pair a b ∈ f and b =ᴮ y.func i
          -- bv_rw' with H : y.func i =ᴮ b, H_new : pair a b ∈ f → pair a (y.func i) ∈ f
          exact bv_rw' (bv_symm (inf_le_left.trans inf_le_right)) (ϕ := fun z => pair a z ∈ᴮ f)
            (h_congr := B_ext_pair_mem_right) (H_new := inf_le_right.trans H_mem)

-- src/bvm_extras.lean:638
lemma mem_image_iff {x y b f : bSet 𝔹} {Γ} :
    Γ ≤ b ∈ᴮ image x y f ↔ (Γ ≤ b ∈ᴮ y) ∧ Γ ≤ ⨆ z, z ∈ᴮ x ⊓ pair z b ∈ᴮ f := by
  constructor
  · intro H
    refine ⟨mem_of_mem_subset image_subset H, ?_⟩
    unfold image at H; rw [mem_subset.mk_iff] at H
    -- H: Γ ≤ ⨆ i, b =ᴮ y.func i ⊓ ((⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ y.bval i)
    apply H.trans
    apply iSup_le; intro i
    -- Context: b =ᴮ y.func i ⊓ ((⨆ z, z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ y.bval i)
    set A := b =ᴮ y.func i
    set Chi := ⨆ z, z ∈ᴮ x ⊓ pair z (y.func i) ∈ᴮ f
    -- hbeq : A ⊓ (Chi ⊓ y.bval i) ≤ A
    -- hChi : A ⊓ (Chi ⊓ y.bval i) ≤ Chi
    have hbeq : A ⊓ (Chi ⊓ y.bval i) ≤ A := inf_le_left
    have hChi : A ⊓ (Chi ⊓ y.bval i) ≤ Chi :=
      inf_le_right.trans inf_le_left
    -- Show Chi ⊓ A ≤ ⨆ z, z ∈ x ⊓ pair z b ∈ f
    apply le_trans (le_inf hChi hbeq)
    rw [iSup_inf_eq]
    apply iSup_le; intro z
    apply le_iSup_of_le z
    -- Context: (z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ A  where A = b =ᴮ y.func i
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    -- Context: (z ∈ x ⊓ pair z (y.func i) ∈ f) ⊓ (b =ᴮ y.func i)
    -- H_beq : _ ≤ b =ᴮ y.func i (from inf_le_right)
    -- H_mem : _ ≤ pair z (y.func i) ∈ f (from inf_le_left.trans inf_le_right)
    -- bv_rw' with b =ᴮ y.func i, ϕ = fun w => pair z w ∈ f,
    --   H_new = pair z (y.func i) ∈ f → pair z b ∈ f
    exact bv_rw' (H := inf_le_right) (ϕ := fun w => pair z w ∈ᴮ f)
      (h_congr := B_ext_pair_mem_right) (H_new := inf_le_left.trans inf_le_right)
  · intro ⟨H_mem_y, H_ex⟩
    obtain ⟨a, Ha⟩ := exists_convert H_ex (B_ext_inf B_ext_mem_left B_ext_pair_mem_left)
    exact mem_image (Ha.trans inf_le_right) (Ha.trans inf_le_left) H_mem_y
-- src/bvm_extras.lean:649
@[simp] lemma B_congr_image_left {y f : bSet 𝔹} : B_congr (fun x => image x y f) := by
  intro x₁ x₂ Γ H_eq
  apply mem_ext
  · -- fwd: image x₁ y f ⊆ image x₂ y f
    apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x₁ y f ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x₁ y f ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x₁ y f ≤ ⨆ w, w ∈ᴮ x₁ ⊓ pair w z ∈ᴮ f :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := bv_symm (hΓ.trans H_eq)) (ϕ := fun x => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)) (H_new := hmem.2)⟩
  · -- bwd: image x₂ y f ⊆ image x₁ y f
    apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x₂ y f ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x₂ y f ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x₂ y f ≤ ⨆ w, w ∈ᴮ x₂ ⊓ pair w z ∈ᴮ f :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := hΓ.trans H_eq) (ϕ := fun x => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)) (H_new := hmem.2)⟩

-- src/bvm_extras.lean:658
@[simp] lemma B_congr_image_right {x y : bSet 𝔹} : B_congr (fun f => image x y f) := by
  intro f₁ f₂ Γ H_eq
  apply mem_ext
  · apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x y f₁ ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x y f₁ ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x y f₁ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f₁ :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := bv_symm (hΓ.trans H_eq)) (ϕ := fun f => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)) (H_new := hmem.2)⟩
  · apply le_iInf; intro z; rw [← deduction]
    have hΓ : Γ ⊓ z ∈ᴮ image x y f₂ ≤ Γ := inf_le_left
    have hmem : Γ ⊓ z ∈ᴮ image x y f₂ ≤ z ∈ᴮ y ∧ Γ ⊓ z ∈ᴮ image x y f₂ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f₂ :=
      mem_image_iff.mp (inf_le_right (a := Γ))
    rw [mem_image_iff]
    exact ⟨hmem.1, bv_rw' (H := hΓ.trans H_eq) (ϕ := fun f => ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f)
      (h_congr := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)) (H_new := hmem.2)⟩

-- src/bvm_extras.lean:668
-- bounded preimage
def preimage (x y f : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun i : x.type => ⨆ b, b ∈ᴮ y ⊓ pair (x.func i) b ∈ᴮ f)

-- src/bvm_extras.lean:671
@[simp] lemma preimage_subset {x y f} {Γ : 𝔹} : Γ ≤ preimage x y f ⊆ᴮ x :=
  subset.mk_subset

-- src/bvm_extras.lean:673
@[simp] lemma mem_preimage {x y a b f : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pair a b ∈ᴮ f) (H_mem'' : Γ ≤ a ∈ᴮ x) (H_mem' : Γ ≤ b ∈ᴮ y) :
    Γ ≤ a ∈ᴮ preimage x y f := by
  unfold preimage; rw [mem_subset.mk_iff]
  rw [mem_unfold] at H_mem''
  -- H_mem'' : Γ ≤ ⨆ i, x.bval i ⊓ a =ᴮ x.func i
  -- Goal: Γ ≤ ⨆ i, a =ᴮ x.func i ⊓ ((⨆ b', b' ∈ y ⊓ pair (x.func i) b' ∈ f) ⊓ x.bval i)
  calc Γ ≤ (⨆ i, x.bval i ⊓ a =ᴮ x.func i) ⊓ Γ := le_inf H_mem'' le_rfl
    _ ≤ ⨆ i, (x.bval i ⊓ a =ᴮ x.func i) ⊓ Γ := (iSup_inf_eq _ _).le
    _ ≤ ⨆ i, a =ᴮ x.func i ⊓ ((⨆ b', b' ∈ᴮ y ⊓ pair (x.func i) b' ∈ᴮ f) ⊓ x.bval i) := by
          apply iSup_le; intro i
          apply le_iSup_of_le i
          set A := a =ᴮ x.func i
          -- Context: (x.bval i ⊓ A) ⊓ Γ
          refine le_inf (inf_le_left.trans inf_le_right) (le_inf ?_ (inf_le_left.trans inf_le_left))
          -- Need: _ ≤ ⨆ b', b' ∈ y ⊓ pair (x.func i) b' ∈ f
          apply le_iSup_of_le b
          refine le_inf (inf_le_right.trans H_mem') ?_
          -- pair (x.func i) b ∈ f from pair a b ∈ f and a =ᴮ x.func i
          -- bv_rw' with x.func i =ᴮ a, ϕ = fun w => pair w b ∈ f, H_new = pair a b ∈ f
          exact bv_rw' (bv_symm (inf_le_left.trans inf_le_right)) (ϕ := fun w => pair w b ∈ᴮ f)
            (h_congr := B_ext_pair_mem_left) (H_new := inf_le_right.trans H_mem)

/-- f is a function x → y if it is extensional, total, and is a subset of the product of x and y -/
-- src/bvm_extras.lean:684
@[reducible] def is_function (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ (f ⊆ᴮ prod x y)

-- src/bvm_extras.lean:687
@[simp] lemma B_ext_is_function_left {y f : bSet 𝔹} : B_ext (fun x => is_function x y f) :=
  -- is_function x y f = (is_func f ⊓ is_total x y f) ⊓ f ⊆ prod x y
  -- is_total x y f = ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
  -- f ⊆ prod x y = ⨅ j, f.bval j ⟹ f.func j ∈ prod x y
  B_ext_inf
    (B_ext_inf B_ext_const
      (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
    (B_ext_term (ϕ := fun v => f ⊆ᴮ v) (t := fun x => prod x y)
      (H := B_ext_subset_right) (H' := B_congr_prod_left))

-- src/bvm_extras.lean:690
@[simp] lemma B_ext_is_function_right {x y : bSet 𝔹} : B_ext (fun f => is_function x y f) :=
  -- is_function x y f = (is_func f ⊓ is_total x y f) ⊓ f ⊆ prod x y
  -- is_func f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)
  -- is_total x y f = ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
  -- f ⊆ prod x y = ⨅ j, f.bval j ⟹ f.func j ∈ prod x y (but this uses f's own structure)
  -- B_ext_subset_left : B_ext (fun x => x ⊆ prod x y) (uses x both in domain and range)
  -- Actually need: B_ext (fun f => f ⊆ prod x y)
  -- f ⊆ prod x y as function of f
  B_ext_inf
    (B_ext_inf
      -- is_func f as function of f: ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ ...
      -- B_ext (fun f => pair w₁ v₁ ∈ f) = B_ext_mem_right (x := pair w₁ v₁)
      (B_ext_iInf (h := fun w₁ => B_ext_iInf (h := fun w₂ => B_ext_iInf (h := fun v₁ => B_ext_iInf (h := fun v₂ =>
        B_ext_imp (h₁ := B_ext_inf B_ext_mem_right B_ext_mem_right)
          (h₂ := B_ext_imp (h₁ := B_ext_const) (h₂ := B_ext_const)))))))
      -- is_total x y f as function of f: ⨅ w₁, w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
      -- B_ext (fun f => pair w₁ w₂ ∈ f) = B_ext_mem_right
      (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
        (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_const B_ext_mem_right)))))
    (B_ext_subset_left (y := prod x y))

-- src/bvm_extras.lean:692
lemma is_func'_of_is_function {Γ : 𝔹} {x y f} (H_func : Γ ≤ is_function x y f) :
    Γ ≤ is_func' x y f := le_trans H_func inf_le_left

-- src/bvm_extras.lean:694
lemma eq_of_is_function_of_eq {a b x y f x' y' : bSet 𝔹} {Γ : 𝔹}
    (H_is_function : Γ ≤ is_function a b f) (H_eq₁ : Γ ≤ x =ᴮ y)
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x' =ᴮ y' :=
  eq_of_is_func'_of_eq (is_func'_of_is_function H_is_function) H_eq₁ H_mem₁ H_mem₂

-- src/bvm_extras.lean:697
lemma subset_prod_of_is_function {Γ : 𝔹} {x y f} (H_func : Γ ≤ is_function x y f) :
    Γ ≤ f ⊆ᴮ prod x y := le_trans H_func inf_le_right

-- src/bvm_extras.lean:699
lemma is_total_of_is_function {x y f : bSet 𝔹} {Γ} (H_func : Γ ≤ is_function x y f) :
    Γ ≤ is_total x y f :=
  is_total_of_is_func' (is_func'_of_is_function H_func)

-- ============================================================
-- Task 14b: src/bvm_extras.lean lines 700-1300
-- ============================================================

-- src/bvm_extras.lean:702
lemma mem_domain_of_is_function {x y f : bSet 𝔹} {Γ} {z w : bSet 𝔹}
    (H_mem : Γ ≤ pair z w ∈ᴮ f) (H_func : Γ ≤ is_function x y f) : Γ ≤ z ∈ᴮ x :=
  (mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function H_func) H_mem)).left

-- src/bvm_extras.lean:709
lemma mem_codomain_of_is_function {x y f : bSet 𝔹} {Γ} {z w : bSet 𝔹}
    (H_mem : Γ ≤ pair z w ∈ᴮ f) (H_func : Γ ≤ is_function x y f) : Γ ≤ w ∈ᴮ y :=
  (mem_prod_iff.mp (mem_of_mem_subset (subset_prod_of_is_function H_func) H_mem)).right

-- src/bvm_extras.lean:716
lemma factor_image_is_func' {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_func' x (image x y f) f := by
  refine le_inf (le_trans H_is_func' inf_le_left) ?_
  apply le_iInf; intro w₁; rw [← deduction]
  -- Goal: Γ ⊓ w₁ ∈ᴮ x ≤ ⨆ w₂, w₂ ∈ᴮ image x y f ⊓ pair w₁ w₂ ∈ᴮ f
  have H_total := is_total_of_is_func' H_is_func'
  have H_Γ : Γ ⊓ w₁ ∈ᴮ x ≤ Γ := inf_le_left
  have H_w₁ : Γ ⊓ w₁ ∈ᴮ x ≤ w₁ ∈ᴮ x := inf_le_right
  have H_total_spec := le_trans H_Γ (le_trans H_total (iInf_le _ w₁))
  -- H_total_spec : Γ ⊓ w₁ ∈ᴮ x ≤ w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f
  have H_step := le_trans (le_inf H_total_spec H_w₁) bv_imp_elim
  -- H_step : Γ ⊓ w₁ ∈ᴮ x ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f
  -- upgrade w₂ ∈ y to w₂ ∈ image x y f using mem_image
  calc Γ ⊓ w₁ ∈ᴮ x
      ≤ (⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (Γ ⊓ w₁ ∈ᴮ x) := le_inf H_step le_rfl
    _ ≤ ⨆ w₂, (w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (Γ ⊓ w₁ ∈ᴮ x) := (iSup_inf_eq _ _).le
    _ ≤ ⨆ w₂, w₂ ∈ᴮ image x y f ⊓ pair w₁ w₂ ∈ᴮ f := by
          apply iSup_le; intro w₂; apply le_iSup_of_le w₂
          -- Context: (w₂ ∈ y ⊓ pair w₁ w₂ ∈ f) ⊓ (Γ ⊓ w₁ ∈ x)
          refine le_inf ?_ (inf_le_left.trans inf_le_right)
          exact mem_image (inf_le_left.trans inf_le_right)
            (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_left)

-- src/bvm_extras.lean:727
lemma factor_image_is_function {x y f : bSet 𝔹} {Γ} (H_is_function : Γ ≤ is_function x y f) :
    Γ ≤ is_function x (image x y f) f := by
  refine le_inf ?_ ?_
  · exact factor_image_is_func' (is_func'_of_is_function H_is_function)
  · rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
    -- Goal: Γ ⊓ w ∈ f ≤ w ∈ prod x (image x y f)
    -- Step 1: w ∈ f → w ∈ prod x y
    have H_sub := subset_prod_of_is_function H_is_function
    have H_w_prod_xy : Γ ⊓ w ∈ᴮ f ≤ w ∈ᴮ prod x y :=
      mem_of_mem_subset (le_trans inf_le_left H_sub) inf_le_right
    -- Step 2: Augment with context to extract prod x y index
    -- H_w_prod_xy : Γ ⊓ w ∈ f ≤ w ∈ prod x y
    -- Unfold prod membership in the calc chain
    have H_w_prod_unfold : Γ ⊓ w ∈ᴮ f ≤ ⨆ p : x.type × y.type,
        (x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2) := by
      calc Γ ⊓ w ∈ᴮ f ≤ w ∈ᴮ prod x y := H_w_prod_xy
        _ = ⨆ p : x.type × y.type, (prod x y).bval p ⊓ w =ᴮ (prod x y).func p := mem_unfold
        _ = ⨆ p : x.type × y.type, (x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2) :=
              rfl
    calc Γ ⊓ w ∈ᴮ f
        ≤ (⨆ p : x.type × y.type, (x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2)) ⊓
            (Γ ⊓ w ∈ᴮ f) := le_inf H_w_prod_unfold le_rfl
      _ ≤ ⨆ p : x.type × y.type, ((x.bval p.1 ⊓ y.bval p.2) ⊓ w =ᴮ pair (x.func p.1) (y.func p.2)) ⊓
              (Γ ⊓ w ∈ᴮ f) := (iSup_inf_eq _ _).le
      _ ≤ w ∈ᴮ prod x (image x y f) := by
            apply iSup_le; intro ⟨i, j⟩
            -- Context: ((x.bval i ⊓ y.bval j) ⊓ w =ᴮ pair (x.func i) (y.func j)) ⊓ (Γ ⊓ w ∈ f)
            -- Abbrev and extract components
            set L := (x.bval i ⊓ y.bval j) ⊓ w =ᴮ pair (x.func i) (y.func j)
            set R := Γ ⊓ w ∈ᴮ f
            -- hxb : L ⊓ R ≤ x.bval i
            have hxb : L ⊓ R ≤ x.bval i :=
              (inf_le_left (b := R)).trans ((inf_le_left (b := w =ᴮ pair (x.func i) (y.func j))).trans inf_le_left)
            have hyb : L ⊓ R ≤ y.bval j :=
              (inf_le_left (b := R)).trans ((inf_le_left (b := w =ᴮ pair (x.func i) (y.func j))).trans inf_le_right)
            have heq : L ⊓ R ≤ w =ᴮ pair (x.func i) (y.func j) :=
              (inf_le_left (b := R)).trans inf_le_right
            have hw_f : L ⊓ R ≤ w ∈ᴮ f :=
              (inf_le_right (a := L)).trans inf_le_right
            have hpair_f := subst_congr_mem_left' heq hw_f
            have hxi := le_trans hxb (mem_mk' x i)
            have hyj := le_trans hyb (mem_mk' y j)
            have himage := mem_image hpair_f hxi hyj
            exact subst_congr_mem_left' (bv_symm heq) (prod_mem hxi himage)

-- src/bvm_extras.lean:740
lemma check_is_total {x y f : PSet.{u}} (H_total : PSet.is_total x y f) {Γ : 𝔹} :
    Γ ≤ is_total (check x) (check y) (check f) := by
  sorry -- TODO: port from src/bvm_extras.lean:740

-- src/bvm_extras.lean:757
lemma check_is_func {x y f : PSet.{u}} (H_func : PSet.is_func x y f) {Γ : 𝔹} :
    Γ ≤ is_function (check x) (check y) (check f) := by
  sorry -- TODO: port from src/bvm_extras.lean:757

-- src/bvm_extras.lean:797
def function_of_func' {x y f : bSet 𝔹} {Γ} (_H_is_func' : Γ ≤ is_func' x y f) : bSet 𝔹 :=
  f ∩ᴮ (prod x y)

-- src/bvm_extras.lean:800
lemma function_of_func'_subset {x y f : bSet 𝔹} {Γ} {H_is_func' : Γ ≤ is_func' x y f} :
    Γ ≤ function_of_func' H_is_func' ⊆ᴮ f :=
  binary_inter_subset_left

-- src/bvm_extras.lean:804
lemma mem_function_of_func'_iff {x y f : bSet 𝔹} {Γ} {H_is_func' : Γ ≤ is_func' x y f} {z} :
    Γ ≤ z ∈ᴮ (function_of_func' H_is_func') ↔ Γ ≤ z ∈ᴮ f ∧ Γ ≤ z ∈ᴮ (prod x y) :=
  mem_binary_inter_iff

-- src/bvm_extras.lean:807
@[reducible] def is_inj (f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, ⨅ w₂, ⨅ v₁, ⨅ v₂,
    (pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂) ⟹ w₁ =ᴮ w₂

-- src/bvm_extras.lean:810
@[reducible] def is_injective_function (x y f : bSet 𝔹) : 𝔹 :=
  is_function x y f ⊓ is_inj f

-- src/bvm_extras.lean:812
lemma is_inj_of_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ is_injective_function x y f → Γ ≤ is_inj f :=
  fun h => le_trans h inf_le_right

-- src/bvm_extras.lean:814
lemma factor_image_is_injective_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_is_function : Γ ≤ is_injective_function x y f) :
    Γ ≤ is_injective_function x (image x y f) f :=
  le_inf (factor_image_is_function (le_trans H_is_function inf_le_left))
         (le_trans H_is_function inf_le_right)

-- src/bvm_extras.lean:821
@[simp] lemma B_ext_is_injective_function_left {y f : bSet 𝔹} :
    B_ext (fun x => is_injective_function x y f) :=
  -- is_injective_function x y f = is_function x y f ⊓ is_inj f
  B_ext_inf B_ext_is_function_left B_ext_const

-- src/bvm_extras.lean:824
lemma is_func'_of_is_injective_function {x y f : bSet 𝔹} {Γ}
    (H : Γ ≤ is_injective_function x y f) : Γ ≤ is_func' x y f :=
  is_func'_of_is_function (le_trans H inf_le_left)

-- src/bvm_extras.lean:828
lemma check_is_injective_function {x y f : PSet.{u}}
    (H_inj : PSet.is_injective_function x y f) {Γ : 𝔹} :
    Γ ≤ bSet.is_injective_function (check x) (check y) (check f) := by
  sorry -- TODO: port from src/bvm_extras.lean:828

-- src/bvm_extras.lean:868
@[simp] lemma eq_of_is_inj_of_eq {x y x' y' f : bSet 𝔹} {Γ : 𝔹}
    (H_is_inj : Γ ≤ is_inj f) (H_eq : Γ ≤ x' =ᴮ y')
    (H_mem₁ : Γ ≤ pair x x' ∈ᴮ f) (H_mem₂ : Γ ≤ pair y y' ∈ᴮ f) : Γ ≤ x =ᴮ y := by
  have hspec := le_trans H_is_inj
    (iInf_le _ x |>.trans (iInf_le _ y) |>.trans (iInf_le _ x') |>.trans (iInf_le _ y'))
  -- hspec : Γ ≤ pair x x' ∈ f ⊓ pair y y' ∈ f ⊓ x' =ᴮ y' ⟹ x =ᴮ y
  -- bv_imp_elim : (A ⟹ B) ⊓ A ≤ B
  exact le_trans (le_inf hspec (le_inf (le_inf H_mem₁ H_mem₂) H_eq)) bv_imp_elim

-- src/bvm_extras.lean:879
-- not really funext since it doesn't use extensionality in an essential way
lemma funext {x y f g : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_function x y f) (H₂ : Γ ≤ is_function x y g)
    (H_peq : Γ ≤ ⨅ p, p ∈ᴮ prod x y ⟹ (p ∈ᴮ f ⇔ p ∈ᴮ g)) : Γ ≤ f =ᴮ g := by
  have H_sub₁ := subset_prod_of_is_function H₁
  have H_sub₂ := subset_prod_of_is_function H₂
  apply mem_ext
  -- Each branch: Γ ⊓ z ∈ f ≤ z ∈ g or Γ ⊓ z ∈ g ≤ z ∈ f
  · -- f ⊆ g direction
    apply le_iInf; intro z; rw [← deduction]
    -- Context: Γ ⊓ z ∈ f
    have hz_prod : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (le_trans inf_le_left H_sub₁) inf_le_right
    have hpeq_spec : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ prod x y ⟹ (z ∈ᴮ f ⇔ z ∈ᴮ g) :=
      le_trans inf_le_left (le_trans H_peq (iInf_le _ z))
    have hiff := le_trans (le_inf hpeq_spec hz_prod) bv_imp_elim
    -- hiff : Γ ⊓ z ∈ f ≤ z ∈ f ⇔ z ∈ g = (z ∈ f ⟹ z ∈ g) ⊓ (z ∈ g ⟹ z ∈ f)
    have hfwd : Γ ⊓ z ∈ᴮ f ≤ z ∈ᴮ f ⟹ z ∈ᴮ g := le_trans hiff inf_le_left
    exact le_trans (le_inf hfwd inf_le_right) bv_imp_elim
  · -- g ⊆ f direction
    apply le_iInf; intro z; rw [← deduction]
    -- Context: Γ ⊓ z ∈ g
    have hz_prod : Γ ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod x y :=
      mem_of_mem_subset (le_trans inf_le_left H_sub₂) inf_le_right
    have hpeq_spec : Γ ⊓ z ∈ᴮ g ≤ z ∈ᴮ prod x y ⟹ (z ∈ᴮ f ⇔ z ∈ᴮ g) :=
      le_trans inf_le_left (le_trans H_peq (iInf_le _ z))
    have hiff := le_trans (le_inf hpeq_spec hz_prod) bv_imp_elim
    have hbwd : Γ ⊓ z ∈ᴮ g ≤ z ∈ᴮ g ⟹ z ∈ᴮ f := le_trans hiff inf_le_right
    exact le_trans (le_inf hbwd inf_le_right) bv_imp_elim

-- src/bvm_extras.lean:891
/-- A relation f is surjective if for every w ∈ y there is a v ∈ x such that (v,w) ∈ f. -/
@[reducible] def is_surj (x y : bSet 𝔹) (f : bSet 𝔹) : 𝔹 :=
  ⨅ v, v ∈ᴮ y ⟹ (⨆ w, w ∈ᴮ x ⊓ pair w v ∈ᴮ f)

/-- x is larger than y if there is a subset S ⊆ X which surjects onto y. -/
-- src/bvm_extras.lean:895
def larger_than (x y : bSet 𝔹) : 𝔹 :=
  ⨆ S, ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)

-- src/bvm_extras.lean:897
lemma is_surj_empty {Γ : 𝔹} : Γ ≤ is_surj (∅ : bSet 𝔹) ∅ ∅ :=
  forall_empty

-- src/bvm_extras.lean:900
lemma function_of_func'_is_function {x y f : bSet 𝔹} {Γ} (H_is_func' : Γ ≤ is_func' x y f) :
    Γ ≤ is_function x y (function_of_func' H_is_func') := by
  refine le_inf (le_inf ?_ ?_) ?_
  · exact is_func_subset_of_is_func (is_func_of_is_func' H_is_func') binary_inter_subset_left
  · -- totality: for every w₁ ∈ x, ∃ w₂ ∈ y, pair w₁ w₂ ∈ f ∩ prod x y
    apply le_iInf; intro w₁; rw [← deduction, inf_comm]
    -- let Γ_1 := w₁ ∈ᴮ x ⊓ Γ
    have H_total : Γ ≤ is_total x y f := is_total_of_is_func' H_is_func'
    -- Goal: w₁ ∈ x ⊓ Γ ≤ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ (f ∩ prod x y)
    -- From H_total: Γ ≤ is_total x y f
    have H_total_spec : w₁ ∈ᴮ x ⊓ Γ ≤ w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f :=
      le_trans (le_trans inf_le_right H_total) (iInf_le _ w₁)
    -- H_total_spec : w₁ ∈ x ⊓ Γ ≤ w₁ ∈ x ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
    have step : w₁ ∈ᴮ x ⊓ Γ ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f :=
      le_trans (le_inf H_total_spec (inf_le_left (b := Γ))) bv_imp_elim
    -- Augment step with the context to include w₁ ∈ x
    calc w₁ ∈ᴮ x ⊓ Γ
        ≤ (⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (w₁ ∈ᴮ x ⊓ Γ) := le_inf step le_rfl
      _ ≤ ⨆ w₂, (w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f) ⊓ (w₁ ∈ᴮ x ⊓ Γ) := (iSup_inf_eq _ _).le
      _ ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ (f ∩ᴮ prod x y) := by
            apply iSup_le; intro w₂; apply le_iSup_of_le w₂
            refine le_inf (inf_le_left.trans inf_le_left) ?_
            -- need: (w₂ ∈ y ⊓ pair w₁ w₂ ∈ f) ⊓ (w₁ ∈ x ⊓ Γ) ≤ pair w₁ w₂ ∈ (f ∩ prod x y)
            apply mem_binary_inter_iff.mpr
            constructor
            · exact inf_le_left.trans inf_le_right
            · exact le_trans (le_inf (inf_le_right.trans inf_le_left)
                (inf_le_left.trans inf_le_left)) prod_mem_old
  · exact binary_inter_subset_right

-- src/bvm_extras.lean:913
lemma function_of_func'_surj_of_surj {x y f : bSet 𝔹} {Γ}
    (H_is_func' : Γ ≤ is_func' x y f) (H_is_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj x y (function_of_func' H_is_func') := by
  apply le_iInf; intro z; rw [← deduction]
  -- Goal: Γ ⊓ z ∈ᴮ y ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ (f ∩ᴮ prod x y)
  have step : Γ ⊓ z ∈ᴮ y ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f :=
    le_trans (le_inf (le_trans (le_trans inf_le_left H_is_surj) (iInf_le _ z)) inf_le_right) bv_imp_elim
  calc Γ ⊓ z ∈ᴮ y
      ≤ (⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ y) := le_inf step le_rfl
    _ ≤ ⨆ w, (w ∈ᴮ x ⊓ pair w z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ y) := (iSup_inf_eq _ _).le
    _ ≤ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ (f ∩ᴮ prod x y) := by
          apply iSup_le; intro w; apply le_iSup_of_le w
          refine le_inf (inf_le_left.trans inf_le_left) ?_
          apply mem_binary_inter_iff.mpr
          exact ⟨inf_le_left.trans inf_le_right,
            le_trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right))
              prod_mem_old⟩

-- src/bvm_extras.lean:921
lemma function_of_func'_inj_of_inj {x y f : bSet 𝔹} {Γ} {H : Γ ≤ is_func' x y f}
    (H_is_inj : Γ ≤ is_inj f) : Γ ≤ is_inj (function_of_func' H) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  -- Goal: Γ ⊓ (pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod x y) ⊓ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod x y) ⊓ v₁ =ᴮ v₂) ≤ w₁ =ᴮ w₂
  -- use binary_inter_subset_left to extract pair wᵢ vᵢ ∈ f
  -- Abbreviate the context
  set Γ₁ := Γ ⊓ (pair w₁ v₁ ∈ᴮ (f ∩ᴮ prod x y) ⊓ pair w₂ v₂ ∈ᴮ (f ∩ᴮ prod x y) ⊓ v₁ =ᴮ v₂)
  have hmem₁ : Γ₁ ≤ pair w₁ v₁ ∈ᴮ f :=
    mem_of_mem_subset binary_inter_subset_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hmem₂ : Γ₁ ≤ pair w₂ v₂ ∈ᴮ f :=
    mem_of_mem_subset binary_inter_subset_left (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hveq : Γ₁ ≤ v₁ =ᴮ v₂ := inf_le_right.trans inf_le_right
  have hspec : Γ₁ ≤ pair w₁ v₁ ∈ᴮ f ⊓ pair w₂ v₂ ∈ᴮ f ⊓ v₁ =ᴮ v₂ ⟹ w₁ =ᴮ w₂ :=
    le_trans inf_le_left (le_trans H_is_inj
      ((iInf_le _ w₁).trans (iInf_le _ w₂) |>.trans (iInf_le _ v₁) |>.trans (iInf_le _ v₂)))
  exact le_trans (le_inf hspec (le_inf (le_inf hmem₁ hmem₂) hveq)) bv_imp_elim

-- src/bvm_extras.lean:931
lemma surj_image {x y f : bSet 𝔹} {Γ} (H_func : Γ ≤ is_func' x y f) :
    Γ ≤ is_surj x (image x y f) f := by
  apply le_iInf; intro w; rw [← deduction]
  -- After rw [← deduction], goal is: Γ ⊓ w ∈ᴮ image x y f ≤ ⨆ u, u ∈ᴮ x ⊓ pair u w ∈ᴮ f
  have hmem : Γ ⊓ w ∈ᴮ image x y f ≤ w ∈ᴮ image x y f := inf_le_right
  rw [mem_image_iff] at hmem
  exact hmem.right

-- src/bvm_extras.lean:938
lemma image_eq_codomain_of_surj {x y f : bSet 𝔹} {Γ}
    (H_surj : Γ ≤ is_surj x y f) : Γ ≤ image x y f =ᴮ y := by
  refine subset_ext image_subset ?_
  rw [subset_unfold']; apply le_iInf; intro z; rw [← deduction]
  -- After rw [← deduction], goal is: Γ ⊓ z ∈ᴮ y ≤ z ∈ᴮ image x y f
  have hΓ : Γ ⊓ z ∈ᴮ y ≤ Γ := inf_le_left
  have hmem : Γ ⊓ z ∈ᴮ y ≤ z ∈ᴮ y := inf_le_right
  have hspec := le_trans hΓ (le_trans H_surj (iInf_le _ z))
  -- hspec : Γ ⊓ z ∈ᴮ y ≤ z ∈ᴮ y ⟹ ⨆ w, w ∈ᴮ x ⊓ pair w z ∈ᴮ f
  rw [mem_image_iff]
  exact ⟨hmem, le_trans (le_inf hspec hmem) bv_imp_elim⟩

-- src/bvm_extras.lean:946
@[simp] lemma larger_than_domain_subset {Γ : 𝔹} {x y S : bSet 𝔹}
    (HS : Γ ≤ ⨆ f, S ⊆ᴮ x ⊓ (is_func' S y f) ⊓ (is_surj S y f)) : Γ ≤ S ⊆ᴮ x := by
  exact le_trans HS (iSup_le (fun f => le_trans (le_trans inf_le_left inf_le_left) (le_refl _)))

-- src/bvm_extras.lean:950
def injects_into (x y : bSet 𝔹) : 𝔹 := ⨆ f, (is_func' x y f) ⊓ is_inj f

-- src/bvm_extras.lean:952
def injection_into (x y : bSet 𝔹) : 𝔹 := ⨆ f, is_injective_function x y f

-- src/bvm_extras.lean:954
lemma injection_into_of_injects_into {x y : bSet 𝔹} {Γ} (H : Γ ≤ injects_into x y) :
    Γ ≤ injection_into x y :=
  -- injects_into x y = ⨆ f, (is_func' x y f) ⊓ is_inj f
  -- injection_into x y = ⨆ f, is_injective_function x y f
  H.trans (iSup_le fun f =>
    le_iSup_of_le (function_of_func' inf_le_left)
      (le_inf (function_of_func'_is_function inf_le_left)
        (function_of_func'_inj_of_inj inf_le_right)))

-- src/bvm_extras.lean:963
lemma injects_into_of_injection_into {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injection_into x y) :
    Γ ≤ injects_into x y :=
  -- injection_into x y = ⨆ f, is_injective_function x y f = ⨆ f, is_function x y f ⊓ is_inj f
  -- injects_into x y = ⨆ f, (is_func' x y f) ⊓ is_inj f
  -- is_function x y f = is_func' x y f ⊓ ..., so is_function ≤ is_func'
  H_inj.trans (iSup_le fun f =>
    le_iSup_of_le f (le_inf (inf_le_left.trans inf_le_left) inf_le_right))

-- src/bvm_extras.lean:969
lemma injects_into_iff_injection_into {x y : bSet 𝔹} {Γ} :
    Γ ≤ injects_into x y ↔ Γ ≤ injection_into x y :=
  ⟨injection_into_of_injects_into, injects_into_of_injection_into⟩

-- src/bvm_extras.lean:972
lemma check_injects_into {x y : PSet.{u}} (H_inj : PSet.injects_into x y) {Γ : 𝔹} :
    Γ ≤ bSet.injects_into (check x) (check y) := by
  sorry -- TODO: port from src/bvm_extras.lean:972

-- src/bvm_extras.lean:981
@[reducible] def is_surj_onto (x y f : bSet 𝔹) : 𝔹 := (is_func' x y f) ⊓ (is_surj x y f)

-- src/bvm_extras.lean:983
def surjects_onto (x y : bSet 𝔹) : 𝔹 := ⨆ f, is_surj_onto x y f

-- src/bvm_extras.lean:985
-- larger_than y z = ⨆ S f, S ⊆ y ⊓ is_func' S z f ⊓ is_surj S z f
-- B_ext as function of z:
-- is_total S z f = ⨅ w₁, w₁ ∈ S ⟹ ⨆ w₂, w₂ ∈ z ⊓ pair w₁ w₂ ∈ f
-- is_surj S z f = ⨅ v, v ∈ z ⟹ ⨆ w, w ∈ S ⊓ pair w v ∈ f
private def B_ext_is_total_right (S f : bSet 𝔹) : B_ext (fun z => is_total S z f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const)
    (h₂ := B_ext_iSup (h := fun _ => B_ext_inf B_ext_mem_right B_ext_const)))

private def B_ext_is_surj_codomain (S f : bSet 𝔹) : B_ext (fun z => is_surj S z f) :=
  B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

@[simp] lemma B_ext_larger_than_right {y : bSet 𝔹} : B_ext (fun z => larger_than y z) :=
  B_ext_iSup (h := fun S => B_ext_iSup (h := fun f =>
    B_ext_inf (B_ext_inf B_ext_const
      (B_ext_inf B_ext_const (B_ext_is_total_right S f)))
    (B_ext_is_surj_codomain S f)))

-- src/bvm_extras.lean:988
-- larger_than z y = ⨆ S f, S ⊆ z ⊓ is_func' S y f ⊓ is_surj S y f
-- B_ext as function of z: S ⊆ z = ⨅ j, S.bval j ⟹ S.func j ∈ z
@[simp] lemma B_ext_larger_than_left {y : bSet 𝔹} : B_ext (fun z => larger_than z y) :=
  -- larger_than z y = ⨆ S f, S ⊆ z ⊓ is_func' S y f ⊓ is_surj S y f
  -- B_ext (fun z => S ⊆ z) = B_ext_subset_right
  B_ext_iSup (h := fun S => B_ext_iSup (h := fun f =>
    B_ext_inf (B_ext_inf B_ext_subset_right B_ext_const) B_ext_const))

-- src/bvm_extras.lean:991
-- injects_into z y = ⨆ f, is_func' z y f ⊓ is_inj f
-- is_func' z y f = is_func f ⊓ is_total z y f
-- is_total z y f = ⨅ w₁, w₁ ∈ z ⟹ ⨆ w₂, w₂ ∈ y ⊓ pair w₁ w₂ ∈ f
-- B_ext as function of z: w₁ ∈ z changes with z
@[simp] lemma B_ext_injects_into_left {y : bSet 𝔹} : B_ext (fun z => injects_into z y) :=
  B_ext_iSup (h := fun f =>
    B_ext_inf
      (B_ext_inf B_ext_const
        (B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))
      B_ext_const)

-- src/bvm_extras.lean:994
-- injects_into y z = ⨆ f, is_func' y z f ⊓ is_inj f
-- B_ext as function of z (in codomain y→z)
@[simp] lemma B_ext_injects_into_right {y : bSet 𝔹} : B_ext (fun z => injects_into y z) :=
  B_ext_iSup (h := fun f =>
    B_ext_inf
      (B_ext_inf B_ext_const (B_ext_is_total_right y f))
      B_ext_const)

-- ============================================================
-- src/bvm_extras.lean lines 1004-1300
-- ============================================================

-- src/bvm_extras.lean:1018
-- The pointed_extension construction: extends a partial surjection f : S ↠ y
-- to a total surjection x ↠ y by mapping elements outside S to b.
-- This definition uses subset.mk over (prod x y).type, with bval encoding
-- the condition.
def pointed_extension {x y : bSet 𝔹} {Γ : 𝔹} {S f : bSet 𝔹}
    (b : bSet 𝔹) (_H_b : Γ ≤ b ∈ᴮ y) (_H_S : Γ ≤ S ⊆ᴮ x)
    (_H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x y).type =>
    (x.func pr.1 ∈ᴮ S ⟹ pair (x.func pr.1) (y.func pr.2) ∈ᴮ f) ⊓
    ((x.func pr.1 ∈ᴮ S)ᶜ ⟹ (y.func pr.2) =ᴮ b))

-- src/bvm_extras.lean:1023
@[simp] lemma pointed_extension_func {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    {H_b : Γ ≤ b ∈ᴮ y} {H_S : Γ ≤ S ⊆ᴮ x} {H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f}
    {pr : (prod x y).type} :
    (pointed_extension b H_b H_S H_surj).func pr = pair (x.func pr.1) (y.func pr.2) := rfl

-- src/bvm_extras.lean:1072-1215: All lemmas about pointed_extension
-- These are sorry-stubbed since they require heavy tactic work.

-- src/bvm_extras.lean:1136
lemma pointed_extension_is_func {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_func (pointed_extension b H_b H_S H_surj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1136

-- src/bvm_extras.lean:1177
lemma pointed_extension_is_total {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_total x y (pointed_extension b H_b H_S H_surj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1177

-- src/bvm_extras.lean:1191
lemma pointed_extension_is_func' {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_func' x y (pointed_extension b H_b H_S H_surj) :=
  le_inf (pointed_extension_is_func H_b H_S H_surj)
         (pointed_extension_is_total H_b H_S H_surj)

-- src/bvm_extras.lean:1198
lemma pointed_extension_is_surj {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ is_surj x y (pointed_extension b H_b H_S H_surj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1198

-- src/bvm_extras.lean:1209
lemma pointed_extension_spec {x y : bSet 𝔹} {Γ : 𝔹} {S f b : bSet 𝔹}
    (H_b : Γ ≤ b ∈ᴮ y) (H_S : Γ ≤ S ⊆ᴮ x)
    (H_surj : Γ ≤ is_func' S y f ⊓ is_surj S y f) :
    Γ ≤ surjects_onto x y :=
  le_iSup_of_le (pointed_extension b H_b H_S H_surj)
    (le_inf (pointed_extension_is_func' H_b H_S H_surj)
            (pointed_extension_is_surj H_b H_S H_surj))

-- src/bvm_extras.lean:1220
lemma surjects_onto_of_larger_than_and_exists_mem {x y : bSet 𝔹} {Γ : 𝔹}
    (H_larger_than : Γ ≤ larger_than x y) (H_nonempty : Γ ≤ ⨆ w, w ∈ᴮ y) :
    Γ ≤ surjects_onto x y := by
  sorry -- TODO: port from src/bvm_extras.lean:1220

-- src/bvm_extras.lean:1230
lemma larger_than_of_surjects_onto {x y : bSet 𝔹} {Γ} (H_surj : Γ ≤ surjects_onto x y) :
    Γ ≤ larger_than x y := by
  sorry -- TODO: port from src/bvm_extras.lean:1230 (needs bv_cases for iSup)

-- src/bvm_extras.lean:1238
lemma check_not_is_func {x y f : PSet.{u}} (H : ¬ PSet.is_func x y f) :
    ∀ {Γ : 𝔹}, (Γ ≤ is_function (check x) (check y) (check f) → Γ ≤ (⊥ : 𝔹)) := by
  sorry -- TODO: port from src/bvm_extras.lean:1238

-- src/bvm_extras.lean:1273
lemma check_not_is_surj {x y f : PSet.{u}} (H : ¬ PSet.is_surj x y f) :
    ∀ {Γ : 𝔹}, Γ ≤ is_surj (check x) (check y) (check f) → Γ ≤ (⊥ : 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:1273

-- src/bvm_extras.lean:1291
lemma bot_lt_of_true {b : 𝔹} (H : ∀ {Γ}, Γ ≤ b) : ⊥ < b := by
  have := @H ⊤
  rw [top_le_iff] at this
  simp [this]

-- ============================================================
-- src/bvm_extras.lean lines 1300-1900
-- ============================================================

-- src/bvm_extras.lean:1301
-- Given a surjection f : x ↠ z and an injection g : y ↪ z, lift f along g to a surjection f' : x ↠ y.
def lift_surj_inj {x z f g : bSet 𝔹} (y : bSet 𝔹) {Γ : 𝔹}
    (_H_surj : Γ ≤ is_surj x z f) (_H_inj : Γ ≤ is_inj g) : bSet 𝔹 :=
  @subset.mk _ _ (prod x y)
    (fun p => ⨆ w, w ∈ᴮ z ⊓ (pair (x.func p.1) w) ∈ᴮ f ⊓
                           (pair (y.func p.2) w ∈ᴮ g))

-- src/bvm_extras.lean:1306
lemma ex_witness_of_mem_lift_surj_inj {x y z f g : bSet 𝔹} {Γ : 𝔹} {w₁ w₂ : bSet 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (_H_is_func'_f : Γ ≤ is_func' x z f)
    (H : Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj)) :
    Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) := by
  sorry -- TODO: port from src/bvm_extras.lean:1306

-- src/bvm_extras.lean:1318
lemma mem_lift_surj_inj_iff {x y z f g : bSet 𝔹} {Γ : 𝔹} {w₁ w₂ : bSet 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_is_func'_f : Γ ≤ is_func' x z f) {H_mem₁ : Γ ≤ w₁ ∈ᴮ x} {H_mem₂ : Γ ≤ w₂ ∈ᴮ y} :
    Γ ≤ pair w₁ w₂ ∈ᴮ (lift_surj_inj y H_surj H_inj) ↔
      Γ ≤ ⨆ w, (w ∈ᴮ z ⊓ (pair w₁ w ∈ᴮ f) ⊓ (pair w₂ w ∈ᴮ g)) := by
  sorry -- TODO: port from src/bvm_extras.lean:1318

-- src/bvm_extras.lean:1346
lemma lift_surj_inj_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_is_func_f : Γ ≤ is_func' x z f) :
    Γ ≤ is_func (lift_surj_inj y H_surj H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1346

-- src/bvm_extras.lean:1362
lemma lift_surj_inj_is_total {y z f g S : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g) (H_is_func_f : Γ ≤ is_func' S z f) :
    Γ ≤ is_total (subset.mk (fun i : S.type =>
      ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y
      (lift_surj_inj y H_surj H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1362

-- src/bvm_extras.lean:1375
lemma lift_surj_inj_is_surj {y z f g S : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ is_surj S z f) (H_inj : Γ ≤ is_inj g)
    (H_is_func_f : Γ ≤ is_func' S z f) (H_is_func_g : Γ ≤ is_func' y z g) :
    Γ ≤ is_surj (subset.mk (fun i : S.type =>
      ⨆ b, b ∈ᴮ y ⊓ ⨆ c, c ∈ᴮ z ⊓ pair (S.func i) c ∈ᴮ f ⊓ pair b c ∈ᴮ g)) y
      (lift_surj_inj y H_surj H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1375

-- src/bvm_extras.lean:1404
def extend_surj_inj {x z f g : bSet 𝔹} (y : bSet 𝔹) {Γ : 𝔹}
    (_H_surj : Γ ≤ is_surj x z f) (_H_inj : Γ ≤ is_inj g) : bSet 𝔹 :=
  @subset.mk _ _ (prod y z)
    (fun p => ⨆ w, w ∈ᴮ x ⊓ (pair w (z.func p.2)) ∈ᴮ f ⊓
                           (pair w (y.func p.1) ∈ᴮ g))

-- src/bvm_extras.lean:1410
lemma ex_witness_of_mem_extend_surj_inj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    {w₁ w₂ : bSet 𝔹}
    (H_is_func'_f : Γ ≤ is_func' x z f)
    (H : Γ ≤ pair w₁ w₂ ∈ᴮ extend_surj_inj y H_surj H_inj) :
    Γ ≤ ⨆ w, (w ∈ᴮ x ⊓ (pair w w₁ ∈ᴮ g) ⊓ (pair w w₂ ∈ᴮ f)) := by
  sorry -- TODO: port from src/bvm_extras.lean:1410

-- src/bvm_extras.lean:1422
lemma mem_extend_surj_inj_iff {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    {w₁ w₂ : bSet 𝔹}
    {H_mem₁ : Γ ≤ w₁ ∈ᴮ y} {H_mem₂ : Γ ≤ w₂ ∈ᴮ z}
    (H_is_func'_f : Γ ≤ is_func' x z f) :
    Γ ≤ pair w₁ w₂ ∈ᴮ extend_surj_inj y H_surj H_inj ↔
      Γ ≤ ⨆ w, (w ∈ᴮ x ⊓ (pair w w₁ ∈ᴮ g) ⊓ (pair w w₂ ∈ᴮ f)) := by
  sorry -- TODO: port from src/bvm_extras.lean:1422

-- src/bvm_extras.lean:1445
lemma extend_surj_inj_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g) :
    Γ ≤ is_func (extend_surj_inj y H_surj H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1445

-- src/bvm_extras.lean:1457
lemma extend_surj_inj_is_total {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g) :
    Γ ≤ is_total (image x y g) z (extend_surj_inj y H_surj H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1457

-- src/bvm_extras.lean:1472
lemma extend_surj_inj_is_surj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    {H_surj : Γ ≤ is_surj x z f} {H_inj : Γ ≤ is_inj g}
    (H_f_is_func' : Γ ≤ is_func' x z f) (H_g_is_func' : Γ ≤ is_func' x y g) :
    Γ ≤ is_surj (image x y g) z (extend_surj_inj y H_surj H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1472

-- src/bvm_extras.lean:1486
-- (locally: ≺ means (larger_than x y)ᶜ, ≼ means injects_into x y)
lemma bSet_lt_of_lt_of_le {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ (larger_than x y)ᶜ) (H₂ : Γ ≤ injects_into y z) :
    Γ ≤ (larger_than x z)ᶜ := by
  sorry -- TODO: port from src/bvm_extras.lean:1486

-- src/bvm_extras.lean:1500
lemma bSet_lt_of_le_of_lt {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ injects_into x y) (H₂ : Γ ≤ (larger_than y z)ᶜ) :
    Γ ≤ (larger_than x z)ᶜ := by
  sorry -- TODO: port from src/bvm_extras.lean:1500

-- ============================================================
-- src/bvm_extras.lean:1513-1604: is_func'_comp section
-- ============================================================

-- src/bvm_extras.lean:1518
def is_func'_comp {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (_Hf_func : Γ ≤ is_func' x y f) (_Hg_func : Γ ≤ is_func' y z g) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x z).type =>
    ⨆ b, b ∈ᴮ y ⊓ pair (x.func pr.1) b ∈ᴮ f ⊓ pair b (z.func pr.2) ∈ᴮ g)

-- src/bvm_extras.lean:1521
lemma mem_is_func'_comp_iff {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) {Γ' : 𝔹} {a c : bSet 𝔹} :
    Γ' ≤ pair a c ∈ᴮ is_func'_comp Hf_func Hg_func ↔
      Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ c ∈ᴮ z ∧ Γ' ≤ ⨆ b, b ∈ᴮ y ⊓ (pair a b ∈ᴮ f ⊓ pair b c ∈ᴮ g) := by
  sorry -- TODO: port from src/bvm_extras.lean:1521

-- src/bvm_extras.lean:1554
lemma is_func'_comp_is_func {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) :
    Γ ≤ is_func (is_func'_comp Hf_func Hg_func) := by
  sorry -- TODO: port from src/bvm_extras.lean:1554

-- src/bvm_extras.lean:1565
lemma is_func'_comp_is_total {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) :
    Γ ≤ is_total x z (is_func'_comp Hf_func Hg_func) := by
  sorry -- TODO: port from src/bvm_extras.lean:1565

-- src/bvm_extras.lean:1576
lemma is_func'_comp_is_func' {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g) :
    Γ ≤ is_func' x z (is_func'_comp Hf_func Hg_func) :=
  le_inf (is_func'_comp_is_func Hf_func Hg_func) (is_func'_comp_is_total Hf_func Hg_func)

-- src/bvm_extras.lean:1583
lemma is_func'_comp_inj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g)
    (Hf_inj : Γ ≤ is_inj f) (Hg_inj : Γ ≤ is_inj g) :
    Γ ≤ is_inj (is_func'_comp Hf_func Hg_func) := by
  sorry -- TODO: port from src/bvm_extras.lean:1583

-- src/bvm_extras.lean:1594
lemma is_func'_comp_surj {x y z f g : bSet 𝔹} {Γ : 𝔹}
    (Hf_func : Γ ≤ is_func' x y f) (Hg_func : Γ ≤ is_func' y z g)
    (H₁ : Γ ≤ is_surj x y f) (H₂ : Γ ≤ is_surj y z g) :
    Γ ≤ is_surj x z (is_func'_comp Hf_func Hg_func) := by
  sorry -- TODO: port from src/bvm_extras.lean:1594

-- src/bvm_extras.lean:1606
def function_comp {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    (H₁ : Γ' ≤ is_function x y f) (H₂ : Γ' ≤ is_function y z g) : bSet 𝔹' :=
  is_func'_comp (is_func'_of_is_function H₁) (is_func'_of_is_function H₂)

-- src/bvm_extras.lean:1609
lemma function_comp_is_function {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    {H₁ : Γ' ≤ is_function x y f} {H₂ : Γ' ≤ is_function y z g} :
    Γ' ≤ is_function x z (function_comp H₁ H₂) :=
  le_inf (is_func'_comp_is_func' _ _) subset.mk_subset

-- src/bvm_extras.lean:1616
def injective_function_comp {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    (H₁ : Γ' ≤ is_injective_function x y f) (H₂ : Γ' ≤ is_injective_function y z g) : bSet 𝔹' :=
  is_func'_comp (is_func'_of_is_injective_function H₁) (is_func'_of_is_injective_function H₂)

-- src/bvm_extras.lean:1619
lemma injective_function_comp_is_injective_function {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    {H₁ : Γ' ≤ is_injective_function x y f} {H₂ : Γ' ≤ is_injective_function y z g} :
    Γ' ≤ is_injective_function x z (injective_function_comp H₁ H₂) :=
  le_inf (function_comp_is_function (H₁ := H₁.trans inf_le_left) (H₂ := H₂.trans inf_le_left))
         (is_func'_comp_inj _ _ (H₁.trans inf_le_right) (H₂.trans inf_le_right))

-- src/bvm_extras.lean:1625
lemma injective_function_comp_is_function {𝔹' : Type u} [NontrivialCompleteBooleanAlgebra 𝔹'] {Γ' : 𝔹'} {x y z f g : bSet 𝔹'}
    {H₁ : Γ' ≤ is_injective_function x y f} {H₂ : Γ' ≤ is_injective_function y z g} :
    Γ' ≤ is_function x z (injective_function_comp H₁ H₂) :=
  injective_function_comp_is_injective_function.trans inf_le_left

-- src/bvm_extras.lean:1628
lemma injects_into_trans {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ injects_into x y) (H₂ : Γ ≤ injects_into y z) :
    Γ ≤ injects_into x z :=
  -- Extract witnesses f and g from the two iSup conditions, then compose
  calc Γ ≤ (⨆ f, is_func' x y f ⊓ is_inj f) ⊓ (⨆ g, is_func' y z g ⊓ is_inj g) :=
          le_inf H₁ H₂
    _ ≤ ⨆ f, (is_func' x y f ⊓ is_inj f) ⊓ (⨆ g, is_func' y z g ⊓ is_inj g) :=
          (iSup_inf_eq _ _).le
    _ ≤ ⨆ f, ⨆ g, (is_func' x y f ⊓ is_inj f) ⊓ (is_func' y z g ⊓ is_inj g) := by
          apply iSup_le; intro f
          rw [inf_iSup_eq' (a := is_func' x y f ⊓ is_inj f)
            (s := fun g => is_func' y z g ⊓ is_inj g)]
          exact iSup_le (fun g => le_iSup_of_le f (le_iSup_of_le g le_rfl))
    _ ≤ ⨆ h, is_func' x z h ⊓ is_inj h := by
          apply iSup_le; intro f; apply iSup_le; intro g
          apply le_iSup_of_le (is_func'_comp (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          exact le_inf
            (is_func'_comp_is_func' (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
            (is_func'_comp_inj (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
              (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))

-- src/bvm_extras.lean:1636
lemma injection_into_trans {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ injection_into x y) (H₂ : Γ ≤ injection_into y z) :
    Γ ≤ injection_into x z := by
  rw [← injects_into_iff_injection_into] at H₁ H₂ ⊢
  exact injects_into_trans H₁ H₂

-- src/bvm_extras.lean:1639
lemma AE_of_check_func_check₀ (x y : PSet.{u}) {f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ is_func' (check x) (check y) f) (H_nonzero : ⊥ < Γ) :
    ∀ (i : x.Type), ∃ (j : y.Type),
      ⊥ < (is_func' (check x) (check y) f) ⊓
          (pair (check (x.Func i)) (check (y.Func j))) ∈ᴮ f := by
  sorry -- TODO: port from src/bvm_extras.lean:1639

-- src/bvm_extras.lean:1653
lemma AE_of_check_func_check (x y : PSet.{u}) {f : bSet 𝔹} {Γ : 𝔹}
    (H : Γ ≤ is_func' (check x) (check y) f) (H_nonzero : ⊥ < Γ) :
    ∀ (i : x.Type), ∃ (j : y.Type) (Γ' : 𝔹) (_H_nonzero' : ⊥ < Γ') (_H_le : Γ' ≤ Γ),
      Γ' ≤ (is_func' (check x) (check y) f) ∧
      Γ' ≤ (pair (check (x.Func i)) (check (y.Func j))) ∈ᴮ f := by
  sorry -- TODO: port from src/bvm_extras.lean:1653

-- src/bvm_extras.lean:1692
lemma exists_surjection_of_surjects_onto {x y : bSet 𝔹} {Γ : 𝔹}
    (H_surj : Γ ≤ surjects_onto x y) :
    Γ ≤ ⨆ f, is_function x y f ⊓ is_surj x y f :=
  -- Extract witness from surjects_onto = ⨆ f, is_func' x y f ⊓ is_surj x y f
  H_surj.trans (iSup_le fun f' =>
    le_iSup_of_le (function_of_func' inf_le_left)
      (le_inf (function_of_func'_is_function inf_le_left)
        (function_of_func'_surj_of_surj inf_le_left inf_le_right)))

-- src/bvm_extras.lean:1700
def functions (x y : bSet 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun s : (bv_powerset (prod x y) : bSet 𝔹).type =>
    is_function x y ((bv_powerset (prod x y)).func s))

-- src/bvm_extras.lean:1703
@[simp] lemma functions_func {x y : bSet 𝔹} {i} :
    (functions x y).func i = (bv_powerset (prod x y)).func i := rfl

-- src/bvm_extras.lean:1705
@[simp] lemma functions_bval {x y : bSet 𝔹} {i} :
    (functions x y).bval i = is_function x y ((bv_powerset (prod x y)).func i) := rfl

-- src/bvm_extras.lean:1707
@[simp] lemma functions_type {x y : bSet 𝔹} :
    (functions x y).type = (bv_powerset (prod x y)).type := rfl

-- src/bvm_extras.lean:1709
lemma mem_functions_iff {g x y : bSet 𝔹} {Γ : 𝔹} :
    (Γ ≤ g ∈ᴮ functions x y) ↔ (Γ ≤ is_function x y g) := by
  sorry -- TODO: port from src/bvm_extras.lean:1709

-- ============================================================
-- src/bvm_extras.lean:1732-1798: function_mk' section
-- ============================================================

-- src/bvm_extras.lean:1740
def functionMk' {x y : bSet 𝔹}
    (F : x.type → y.type)
    (χ : x.type → 𝔹)
    (_H_ext : ∀ i j {Γ : 𝔹}, Γ ≤ x.func i =ᴮ x.func j → Γ ≤ y.func (F i) =ᴮ y.func (F j))
    (_H_mem : ∀ i {Γ : 𝔹}, Γ ≤ x.bval i → Γ ≤ y.bval (F i) ∧ Γ ≤ χ i) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x y).type => χ pr.1 ⊓ y.func pr.2 =ᴮ y.func (F pr.1))

-- src/bvm_extras.lean:1757
lemma functionMk'_is_func {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ is_func (functionMk' F χ H_ext H_mem) := by
  sorry -- TODO: port from src/bvm_extras.lean:1757

-- src/bvm_extras.lean:1767
lemma functionMk'_is_total {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ is_total x y (functionMk' F χ H_ext H_mem) := by
  -- Work in the is_total' form since it uses x.bval/x.func indices
  rw [is_total_iff_is_total']
  unfold is_total'
  apply le_iInf; intro i; rw [← deduction]
  -- Goal: Γ ⊓ x.bval i ≤ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ (functionMk' ...)
  obtain ⟨hyF, hχ⟩ := H_mem i inf_le_right
  apply le_iSup_of_le (F i)
  -- Goal: Γ ⊓ x.bval i ≤ y.bval (F i) ⊓ pair (x.func i) (y.func (F i)) ∈ᴮ (functionMk' ...)
  refine le_inf hyF ?_
  rw [mem_unfold]
  apply le_iSup_of_le (i, F i)
  -- Goal: Γ ⊓ x.bval i ≤ (χ i ⊓ y.func (F i) =ᴮ y.func (F i)) ⊓
  --   pair (x.func i) (y.func (F i)) =ᴮ pair (x.func (i, F i).1) (y.func (i, F i).2)
  -- (functionMk' ...).bval (i, F i) = (χ i ⊓ y.func (F i) =ᴮ y.func (F i)) ⊓ (x.bval i ⊓ y.bval (F i))
  -- (functionMk' ...).func (i, F i) = pair (x.func i) (y.func (F i))
  simp only [functionMk', subset.mk, set_of_indicator_bval, set_of_indicator_func, prod_func, prod_bval]
  refine le_inf (le_inf (le_inf hχ bv_refl) (le_inf inf_le_right hyF)) bv_refl

-- src/bvm_extras.lean:1774
lemma functionMk'_is_subset {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ functionMk' F χ H_ext H_mem ⊆ᴮ prod x y :=
  subset.mk_subset

-- src/bvm_extras.lean:1780
lemma functionMk'_is_function {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i) :
    Γ ≤ is_function x y (functionMk' F χ H_ext H_mem) :=
  le_inf (le_inf (functionMk'_is_func F χ H_ext H_mem) (functionMk'_is_total F χ H_ext H_mem))
         (functionMk'_is_subset F χ H_ext H_mem)

-- src/bvm_extras.lean:1788
lemma functionMk'_is_inj {x y : bSet 𝔹} {Γ : 𝔹}
    (F : x.type → y.type) (χ : x.type → 𝔹)
    (H_ext : ∀ i j {Γ' : 𝔹}, Γ' ≤ x.func i =ᴮ x.func j → Γ' ≤ y.func (F i) =ᴮ y.func (F j))
    (H_mem : ∀ i {Γ' : 𝔹}, Γ' ≤ x.bval i → Γ' ≤ y.bval (F i) ∧ Γ' ≤ χ i)
    (H_inj : ∀ i j {Γ'' : 𝔹}, Γ'' ≤ y.func (F i) =ᴮ y.func (F j) → Γ'' ≤ x.func i =ᴮ x.func j) :
    Γ ≤ is_inj (functionMk' F χ H_ext H_mem) := by
  sorry -- TODO: port from src/bvm_extras.lean:1788

-- ============================================================
-- src/bvm_extras.lean:1800-1888: inj_inverse section
-- ============================================================

-- src/bvm_extras.lean:1806
def inj_inverse {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) : bSet 𝔹 :=
  subset.mk (fun pr : (prod (image x y f) x).type =>
    pair (x.func pr.2) ((image x y f).func pr.1) ∈ᴮ f)

-- src/bvm_extras.lean:1809
lemma mem_inj_inverse_iff {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)
    {Γ' : 𝔹} {b a : bSet 𝔹} :
    Γ' ≤ pair b a ∈ᴮ inj_inverse H_func H_inj ↔
      Γ' ≤ a ∈ᴮ x ∧ Γ' ≤ b ∈ᴮ y ∧ Γ' ≤ pair a b ∈ᴮ f := by
  sorry -- TODO: port from src/bvm_extras.lean:1809

-- src/bvm_extras.lean:1841
lemma inj_inverse_is_func {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_func (inj_inverse H_func H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1841

-- src/bvm_extras.lean:1850
lemma inj_inverse_is_total {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_total (image x y f) x (inj_inverse H_func H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1850

-- src/bvm_extras.lean:1858
lemma inj_inverse_is_func' {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_func' (image x y f) x (inj_inverse H_func H_inj) :=
  le_inf (inj_inverse_is_func H_func H_inj) (inj_inverse_is_total H_func H_inj)

-- src/bvm_extras.lean:1865
lemma inj_inverse_is_surj {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_surj (image x y f) x (inj_inverse H_func H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1865

-- src/bvm_extras.lean:1875
lemma inj_inverse_subset_prod {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ inj_inverse H_func H_inj ⊆ᴮ prod (image x y f) x :=
  subset.mk_subset

-- src/bvm_extras.lean:1877
lemma inj_inverse_is_function {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_function (image x y f) x (inj_inverse H_func H_inj) :=
  le_inf (inj_inverse_is_func' H_func H_inj) (inj_inverse_subset_prod H_func H_inj)

-- src/bvm_extras.lean:1880
lemma inj_inverse_is_inj {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f) :
    Γ ≤ is_inj (inj_inverse H_func H_inj) := by
  sorry -- TODO: port from src/bvm_extras.lean:1880

-- ============================================================
-- src/bvm_extras.lean:1890-1900: injective_function_inverse section
-- ============================================================

section injective_function_inverse_section
variable {Γ : 𝔹}

-- src/bvm_extras.lean:1892
def injective_function_inverse {x y f : bSet 𝔹} (H_inj : Γ ≤ is_injective_function x y f) :
    bSet 𝔹 :=
  inj_inverse (is_func'_of_is_injective_function H_inj)
              (is_inj_of_is_injective_function H_inj)

-- src/bvm_extras.lean:1895
lemma injective_function_inverse_is_injective_function {x y f : bSet 𝔹}
    {H_inj : Γ ≤ is_injective_function x y f} :
    Γ ≤ is_injective_function (image x y f) x (injective_function_inverse H_inj) :=
  le_inf (inj_inverse_is_function _ _) (inj_inverse_is_inj _ _)

-- src/bvm_extras.lean:1898
lemma injective_function_inverse_is_inj {x y f : bSet 𝔹}
    {H_inj : Γ ≤ is_injective_function x y f} :
    Γ ≤ is_inj (injective_function_inverse H_inj) :=
  injective_function_inverse_is_injective_function.trans inf_le_right

end injective_function_inverse_section

-- ============================================================
-- src/bvm_extras.lean:1902-1927: function_eval section
-- ============================================================

-- Helper: get existential from is_total
private lemma function_eval_exists {x y f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function x y f) (z : bSet 𝔹) (H_mem : Γ ≤ z ∈ᴮ x) :
    ∃ w, Γ ≤ w ∈ᴮ y ⊓ pair z w ∈ᴮ f :=
  -- From is_total, specialize at z, apply bv_imp_elim, then exists_convert
  have H_total_spec : Γ ≤ z ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f :=
    le_trans (is_total_of_is_function H_func) (iInf_le _ z)
  have H_ex : Γ ≤ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair z w₂ ∈ᴮ f :=
    le_trans (le_inf H_total_spec H_mem) bv_imp_elim
  exists_convert H_ex (B_ext_inf B_ext_mem_left B_ext_pair_mem_right)

-- src/bvm_extras.lean:1906
noncomputable def function_eval {x y f : bSet 𝔹} {Γ : 𝔹} (H_func : Γ ≤ is_function x y f)
    (z : bSet 𝔹) (H_mem : Γ ≤ z ∈ᴮ x) : bSet 𝔹 :=
  (function_eval_exists H_func z H_mem).choose

-- src/bvm_extras.lean:1914
lemma function_eval_spec {x y f : bSet 𝔹} {Γ : 𝔹} {H_func : Γ ≤ is_function x y f}
    {z : bSet 𝔹} {H_mem : Γ ≤ z ∈ᴮ x} :
    Γ ≤ (function_eval H_func z H_mem) ∈ᴮ y ⊓ pair z (function_eval H_func z H_mem) ∈ᴮ f :=
  (function_eval_exists H_func z H_mem).choose_spec

-- src/bvm_extras.lean:1921
lemma function_eval_mem_codomain {x y f : bSet 𝔹} {Γ : 𝔹} {H_func : Γ ≤ is_function x y f}
    {z : bSet 𝔹} {H_mem : Γ ≤ z ∈ᴮ x} :
    Γ ≤ (function_eval H_func z H_mem) ∈ᴮ y :=
  function_eval_spec.trans inf_le_left

-- src/bvm_extras.lean:1924
lemma function_eval_pair_mem {x y f : bSet 𝔹} {Γ : 𝔹} {H_func : Γ ≤ is_function x y f}
    {z : bSet 𝔹} {H_mem : Γ ≤ z ∈ᴮ x} :
    Γ ≤ pair z (function_eval H_func z H_mem) ∈ᴮ f :=
  function_eval_spec.trans inf_le_right

-- ============================================================
-- src/bvm_extras.lean:1930: surjects_onto_of_injects_into
-- ============================================================

-- src/bvm_extras.lean:1930
lemma surjects_onto_of_injects_into' {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injects_into x y)
    (H_exists_mem : Γ ≤ exists_mem x) : Γ ≤ surjects_onto y x := by
  sorry -- TODO: port from src/bvm_extras.lean:1930

-- ============================================================
-- src/bvm_extras.lean:1956-1989: functionMk (= function.mk) and check''
-- ============================================================

-- src/bvm_extras.lean:1956: function.mk renamed to functionMk
-- (functionMk' already exists; this is a different construction called function.mk in Lean 3)
def functionMk {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) : bSet 𝔹 :=
  ⟨u.type, fun a => pair (u.func a) (F a), u.bval⟩

@[simp] lemma functionMk_type {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} :
    (functionMk F h_congr).type = u.type := rfl

@[simp] lemma functionMk_func {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} :
    (functionMk F h_congr).func i = pair (u.func i) (F i) := rfl

@[simp] lemma functionMk_bval {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i} :
    (functionMk F h_congr).bval i = u.bval i := rfl

@[simp] lemma functionMk_self {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    {h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j} {i : u.type} :
    u.bval i ≤ pair (u.func i) (F i) ∈ᴮ functionMk F h_congr := by
  simp only [mem_unfold, functionMk_type, functionMk_bval, functionMk_func]
  exact le_iSup_of_le i (le_inf le_rfl bv_refl)

-- src/bvm_extras.lean:1972: check' named check'' to avoid collision
def check'' {α : Type u} (A : α → bSet 𝔹) : bSet 𝔹 := ⟨α, A, fun _ => ⊤⟩

@[simp] lemma check''_type {α : Type u} {A : α → bSet 𝔹} : (check'' A).type = α := rfl
@[simp] lemma check''_bval {α : Type u} {A : α → bSet 𝔹} {i} : (check'' A).bval i = ⊤ := rfl
@[simp] lemma check''_func {α : Type u} {A : α → bSet 𝔹} {i} : (check'' A).func i = A i := rfl

-- src/bvm_extras.lean:1978
lemma functionMk_is_func {u : bSet 𝔹} (F : u.type → bSet 𝔹)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_func (functionMk F h_congr) := by
  -- is_func g = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ g ⊓ pair w₂ v₂ ∈ g ⊓ w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂
  sorry -- TODO: requires complex iSup distribution over two indexed witnesses

-- src/bvm_extras.lean:2041
lemma functionMk_inj_of_inj {u : bSet 𝔹} {F : u.type → bSet 𝔹}
    (h_inj : ∀ i j, i ≠ j → F i =ᴮ F j ≤ ⊥)
    (h_congr : ∀ i j, u.func i =ᴮ u.func j ≤ F i =ᴮ F j) :
    (⊤ : 𝔹) ≤ is_inj (functionMk F h_congr) := by
  sorry -- TODO: port from src/bvm_extras.lean:2041

-- ============================================================
-- src/bvm_extras.lean:2080-2136: bot_of_mem_self, bot_of_mem_mem
-- ============================================================

-- src/bvm_extras.lean:2080
lemma bot_of_mem_self {x : bSet 𝔹} : (⊤ : 𝔹) ≤ (x ∈ᴮ x ⟹ ⊥) := by
  sorry -- TODO: port from src/bvm_extras.lean:2080 (inductive proof)

-- src/bvm_extras.lean:2093
lemma bot_of_mem_self' {x : bSet 𝔹} {Γ} (H : Γ ≤ (x ∈ᴮ x)) : Γ ≤ ⊥ := by
  have h := @bot_of_mem_self 𝔹 _ x
  -- h : ⊤ ≤ x ∈ᴮ x ⟹ ⊥, i.e., ⊤ ⊓ x ∈ᴮ x ≤ ⊥ (by ← deduction)
  calc Γ ≤ ⊤ ⊓ x ∈ᴮ x := le_inf le_top H
    _ ≤ ⊥ := by rwa [← deduction] at h

-- src/bvm_extras.lean:2099
lemma bot_of_zero_eq_one {Γ : 𝔹} (H : Γ ≤ (0 : bSet 𝔹) =ᴮ 1) : Γ ≤ ⊥ := by
  apply bot_of_mem_self'
  -- Need: Γ ≤ 0 ∈ᴮ 0
  -- Since H : Γ ≤ 0 =ᴮ 1, and 0 ∈ᴮ 1, we can rewrite 0 = 1 to get 0 ∈ᴮ 0
  exact bv_rw' H (ϕ := fun z => (0 : bSet 𝔹) ∈ᴮ z)
    (h_congr := B_ext_mem_right) (H_new := zero_mem_one)

-- src/bvm_extras.lean:2110
lemma bot_of_mem_mem (x y : bSet 𝔹) : (⊤ : 𝔹) ≤ ((x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥) := by
  sorry -- TODO: port from src/bvm_extras.lean:2110 (double induction)

-- src/bvm_extras.lean:2131
lemma bot_of_mem_mem' (x y : bSet 𝔹) {Γ} (H : Γ ≤ x ∈ᴮ y) (H' : Γ ≤ y ∈ᴮ x) : Γ ≤ ⊥ := by
  have h : (⊤ : 𝔹) ≤ (x ∈ᴮ y ⊓ y ∈ᴮ x) ⟹ ⊥ := bot_of_mem_mem x y
  calc Γ ≤ ⊤ ⊓ (x ∈ᴮ y ⊓ y ∈ᴮ x) := le_inf le_top (le_inf H H')
    _ ≤ ⊥ := by rwa [← deduction] at h

end extras

-- ============================================================
-- src/bvm_extras.lean:2140-2218: section check (inside bSet namespace)
-- ============================================================

section bSet_check_extras
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2154
lemma check_powerset_subset_powerset (x : PSet) {Γ : 𝔹} :
    Γ ≤ (check (PSet.powerset x) : bSet 𝔹) ⊆ᴮ (bv_powerset (check x)) := by
  sorry -- TODO: port from src/bvm_extras.lean:2154

-- src/bvm_extras.lean:2193
lemma check_functions_subset_functions {x y : PSet.{u}} {Γ : 𝔹} :
    Γ ≤ (check (PSet.functions x y) : bSet 𝔹) ⊆ᴮ functions (check x) (check y) := by
  sorry -- TODO: port from src/bvm_extras.lean:2193

-- src/bvm_extras.lean:2203
@[simp] lemma check_mem'' {y : PSet} {i : y.Type} :
    ((check (y.Func i) : bSet 𝔹)) ∈ᴮ (check y) = (⊤ : 𝔹) := by
  apply top_unique; simp

-- src/bvm_extras.lean:2206
lemma of_nat_inj' {n k : ℕ} (H_neq : n ≠ k) :
    ((of_nat n : bSet 𝔹) =ᴮ of_nat k) = ⊥ :=
  check_bv_eq_bot_of_not_equiv (PSet.ofNat_inj H_neq)

-- src/bvm_extras.lean:2209
lemma of_nat_mem_of_lt' {k₁ k₂ : ℕ} (H_lt : k₁ < k₂) {Γ : 𝔹} :
    Γ ≤ (of_nat k₁ : bSet 𝔹) ∈ᴮ (of_nat k₂) :=
  check_mem (PSet.ofNat_mem_of_lt H_lt)

-- src/bvm_extras.lean:2215
@[simp] lemma zero_eq_some_none' {Γ : 𝔹} :
    Γ ≤ (0 : bSet 𝔹) =ᴮ (𝟚 : bSet 𝔹).func (some none) :=
  bv_refl

end bSet_check_extras

-- ============================================================
-- src/bvm_extras.lean:2220-2396: section powerset (inside bSet namespace)
-- ============================================================

section powerset_section
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
variable (x : bSet 𝔹)

-- src/bvm_extras.lean:2228
-- powerset_injects_F: maps (bv_powerset x).type → (functions x 𝟚).type
-- encodes χ ↦ characteristic function as subset of x × 𝟚
def powerset_injects_F : (bv_powerset x).type → (functions x 𝟚).type :=
  fun χ pr =>
    (x.func pr.1 ∈ᴮ set_of_indicator χ ⊓ ((𝟚 : bSet 𝔹).func pr.2 =ᴮ 0)) ⊔
    (x.func pr.1 ∈ᴮ subset.mk (fun i => (x.func i ∈ᴮ set_of_indicator χ)ᶜ) ⊓
      ((𝟚 : bSet 𝔹).func pr.2 =ᴮ 1))

-- src/bvm_extras.lean:2231
lemma mem_powerset_injects_F_iff {Γ : 𝔹} {χ : x.type → 𝔹} {z : bSet 𝔹} :
    Γ ≤ pair z 0 ∈ᴮ (functions x 𝟚).func (powerset_injects_F x χ) ↔
    Γ ≤ z ∈ᴮ set_of_indicator χ := by
  sorry -- TODO: port from src/bvm_extras.lean:2231

-- src/bvm_extras.lean:2249
lemma powerset_injects_F_ext : ∀ (i j : (bv_powerset x).type) {Γ : 𝔹},
    Γ ≤ (bv_powerset x).func i =ᴮ (bv_powerset x).func j →
    Γ ≤ (functions x 𝟚).func (powerset_injects_F x i) =ᴮ
        (functions x 𝟚).func (powerset_injects_F x j) := by
  sorry -- TODO: port from src/bvm_extras.lean:2249

-- src/bvm_extras.lean:2301
lemma powerset_injects_F_subset_prod {χ : x.type → 𝔹} {Γ : 𝔹}
    (H_le : Γ ≤ set_of_indicator χ ⊆ᴮ x) :
    Γ ≤ (bv_powerset (prod x 𝟚)).func (powerset_injects_F x χ) ⊆ᴮ prod x 𝟚 := by
  sorry -- TODO: port from src/bvm_extras.lean:2301

-- src/bvm_extras.lean:2318
lemma powerset_injects_F_mem : ∀ (i : (bv_powerset x).type) {Γ : 𝔹},
    Γ ≤ (bv_powerset x).bval i →
    Γ ≤ (functions x 𝟚).bval (powerset_injects_F x i) ∧ Γ ≤ (⊤ : 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:2318

-- src/bvm_extras.lean:2377
lemma powerset_injects_F_inj : ∀ (i j : (bv_powerset x).type) {Γ : 𝔹},
    Γ ≤ (functions x 𝟚).func (powerset_injects_F x i) =ᴮ
        (functions x 𝟚).func (powerset_injects_F x j) →
    Γ ≤ (bv_powerset x).func i =ᴮ (bv_powerset x).func j := by
  sorry -- TODO: port from src/bvm_extras.lean:2377

-- src/bvm_extras.lean:2387
noncomputable def powerset_injects_f : bSet 𝔹 :=
  functionMk' (powerset_injects_F x) (fun _ => ⊤)
    (powerset_injects_F_ext x) (powerset_injects_F_mem x)

-- src/bvm_extras.lean:2389
lemma powerset_injects_into_functions {Γ : 𝔹} :
    Γ ≤ injects_into (bv_powerset x) (functions x 𝟚) :=
  le_iSup_of_le (powerset_injects_f x)
    (le_inf (is_func'_of_is_function (functionMk'_is_function _ _ _ _))
            (functionMk'_is_inj _ _ _ _ (powerset_injects_F_inj x)))

end powerset_section

-- ============================================================
-- src/bvm_extras.lean:2212: check_succ_eq_succ_check (needed by omega_is_omega)
-- ============================================================

-- src/bvm_extras.lean:2212
lemma check_succ_eq_succ_check {n : ℕ} {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] :
    (of_nat (n.succ) : bSet 𝔹) = succ (of_nat n) := by
  sorry -- TODO: port from src/bvm_extras.lean:2212

-- ============================================================
-- src/bvm_extras.lean:2398-2747: section ordinals
-- ============================================================

section ordinals
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2401
@[reducible] def epsilon_trichotomy (x : bSet 𝔹) : 𝔹 :=
  ⨅ y, y ∈ᴮ x ⟹ (⨅ z, z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))

-- src/bvm_extras.lean:2403
@[reducible] def epsilon_well_founded (x : bSet 𝔹) : 𝔹 :=
  ⨅ u, u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))

-- src/bvm_extras.lean:2405
def epsilon_well_orders (x : bSet 𝔹) : 𝔹 :=
  epsilon_trichotomy x ⊓ epsilon_well_founded x

-- src/bvm_extras.lean:2408
@[reducible] def ewo (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x

-- src/bvm_extras.lean:2410
@[simp] lemma B_ext_ewo : B_ext (fun w : bSet 𝔹 => epsilon_well_orders w) := by
  sorry -- TODO: port from src/bvm_extras.lean:2410

-- src/bvm_extras.lean:2413
lemma epsilon_dichotomy (x y z : bSet 𝔹) :
    epsilon_well_orders x ≤ y ∈ᴮ x ⟹ (z ∈ᴮ x ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y)) := by
  sorry -- TODO: port from src/bvm_extras.lean:2413

-- src/bvm_extras.lean:2420
def is_transitive (x : bSet 𝔹) : 𝔹 := ⨅ y, y ∈ᴮ x ⟹ y ⊆ᴮ x

-- src/bvm_extras.lean:2422
lemma subset_of_mem_transitive {x w : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ is_transitive x)
    (H₂ : Γ ≤ w ∈ᴮ x) : Γ ≤ w ⊆ᴮ x :=
  le_trans (le_inf (le_trans H₁ (iInf_le _ w)) H₂) bv_imp_elim

-- src/bvm_extras.lean:2425
@[simp] lemma B_ext_is_transitive : B_ext (is_transitive : bSet 𝔹 → 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:2425

-- src/bvm_extras.lean:2428
def Ord (x : bSet 𝔹) : 𝔹 := epsilon_well_orders x ⊓ is_transitive x

-- src/bvm_extras.lean:2430
lemma epsilon_trichotomy_of_Ord {x a b : bSet 𝔹} {Γ : 𝔹} (Ha_mem : Γ ≤ a ∈ᴮ x)
    (Hb_mem : Γ ≤ b ∈ᴮ x) (H_Ord : Γ ≤ Ord x) :
    Γ ≤ a =ᴮ b ⊔ a ∈ᴮ b ⊔ b ∈ᴮ a := by
  have h_tri : Γ ≤ epsilon_trichotomy x :=
    le_trans (le_trans H_Ord inf_le_left) inf_le_left
  have h1 : Γ ≤ ⨅ z, z ∈ᴮ x ⟹ (a =ᴮ z ⊔ a ∈ᴮ z ⊔ z ∈ᴮ a) :=
    le_trans (le_inf (le_trans h_tri (iInf_le _ a)) Ha_mem) bv_imp_elim
  exact le_trans (le_inf (le_trans h1 (iInf_le _ b)) Hb_mem) bv_imp_elim

-- src/bvm_extras.lean:2438
lemma injects_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ injects_into x y := by
  sorry -- TODO: port from src/bvm_extras.lean:2438

-- src/bvm_extras.lean:2475
lemma injects_into_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ injects_into x x :=
  injects_into_of_subset subset_self

-- src/bvm_extras.lean:2478
lemma bSet_le_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) : Γ ≤ injects_into x y :=
  injects_into_of_subset H

-- src/bvm_extras.lean:2481
lemma injection_into_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ injection_into x y :=
  injects_into_iff_injection_into.mp (injects_into_of_subset H)

-- src/bvm_extras.lean:2484
def Card (y : bSet 𝔹) : 𝔹 := Ord y ⊓ ⨅ x, x ∈ᴮ y ⟹ (larger_than y x)ᶜ

-- src/bvm_extras.lean:2486
lemma is_transitive_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ is_transitive y := by
  sorry -- TODO: port from src/bvm_extras.lean:2486

-- src/bvm_extras.lean:2520
lemma is_ewo_of_mem_Ord (y x : bSet 𝔹) : Ord x ⊓ y ∈ᴮ x ≤ epsilon_well_orders y := by
  sorry -- TODO: port from src/bvm_extras.lean:2520

-- src/bvm_extras.lean:2551
theorem Ord_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) :
    Γ ≤ Ord x :=
  le_inf
    (le_trans (le_inf H_Ord H_mem) (is_ewo_of_mem_Ord x y))
    (le_trans (le_inf H_Ord H_mem) (is_transitive_of_mem_Ord x y))

-- src/bvm_extras.lean:2638
lemma check_is_transitive {x : PSet} (H : PSet.is_transitive x) {Γ : 𝔹} :
    Γ ≤ is_transitive (check x : bSet 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:2638

-- src/bvm_extras.lean:2647
lemma check_ewo_left {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ (⨅ y, y ∈ᴮ (check x : bSet 𝔹) ⟹
      (⨅ z, z ∈ᴮ (check x : bSet 𝔹) ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  sorry -- TODO: port from src/bvm_extras.lean:2647

-- src/bvm_extras.lean:2665
lemma check_ewo_right {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ (⨅ u, u ⊆ᴮ (check x : bSet 𝔹) ⟹
      ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ u ⊓ (⨅ z', z' ∈ᴮ u ⟹ (z' ∈ᴮ y)ᶜ))) := by
  apply le_iInf; intro u
  rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity u inf_le_right

-- src/bvm_extras.lean:2671
lemma check_ewo {x : PSet} (H : PSet.epsilon_well_orders x) {Γ : 𝔹} :
    Γ ≤ epsilon_well_orders (check x : bSet 𝔹) :=
  le_inf (check_ewo_left H) (check_ewo_right H)

-- src/bvm_extras.lean:2674
@[simp] lemma check_Ord {x : PSet} (H : PSet.Ord x) {Γ : 𝔹} :
    Γ ≤ Ord (check x : bSet 𝔹) :=
  le_inf (check_ewo H.left) (check_is_transitive H.right)

-- src/bvm_extras.lean:2677
@[simp] lemma Ord_card_ex (κ : Cardinal) {Γ : 𝔹} :
    Γ ≤ Ord (check (PSet.card_ex κ) : bSet 𝔹) := by
  apply check_Ord; simp [PSet.card_ex]

-- src/bvm_extras.lean:2680
def closed_under_successor (Γ : 𝔹) (x : bSet 𝔹) := Γ ≤ ⨅ y, y ∈ᴮ x ⟹ succ y ∈ᴮ x

-- src/bvm_extras.lean:2682
def omega_spec (ω : bSet 𝔹) : Prop :=
  (∀ {Γ : 𝔹}, Γ ≤ not_empty ω ∧ closed_under_successor Γ ω) ∧
  ∀ (x : bSet 𝔹) {Γ : 𝔹} (H₁ : Γ ≤ ∅ ∈ᴮ x) (H₂ : closed_under_successor Γ x), Γ ≤ ω ⊆ᴮ x

-- src/bvm_extras.lean:2684
lemma omega_closed_under_succ {Γ : 𝔹} : closed_under_successor Γ (bSet.omega) := by
  sorry -- TODO: port from src/bvm_extras.lean:2684

-- src/bvm_extras.lean:2694
lemma omega_nonempty {Γ : 𝔹} : Γ ≤ not_empty bSet.omega := by
  unfold not_empty
  rw [nonempty_iff_exists_mem]
  exact le_iSup_of_le (of_nat 0) of_nat_mem_omega

-- src/bvm_extras.lean:2701
lemma omega_is_omega : omega_spec (bSet.omega : bSet 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:2701

-- src/bvm_extras.lean:2714
lemma Ord_omega {Γ : 𝔹} : Γ ≤ Ord (omega : bSet 𝔹) :=
  le_inf (check_ewo PSet.is_ewo_omega) (check_is_transitive PSet.is_transitive_omega)

-- src/bvm_extras.lean:2717
lemma Ord_of_nat {Γ : 𝔹} {n : ℕ} : Γ ≤ Ord (of_nat n) :=
  Ord_of_mem_Ord of_nat_mem_omega Ord_omega

-- src/bvm_extras.lean:2719
lemma Ord_one {Γ : 𝔹} : Γ ≤ Ord (1 : bSet 𝔹) := Ord_of_nat

-- src/bvm_extras.lean:2721
lemma Ord_zero {Γ : 𝔹} : Γ ≤ Ord (0 : bSet 𝔹) := Ord_of_nat

-- src/bvm_extras.lean:2723
lemma of_nat_subset_omega {n : ℕ} {Γ : 𝔹} : Γ ≤ of_nat n ⊆ᴮ omega :=
  subset_of_mem_transitive (le_trans Ord_omega inf_le_right) of_nat_mem_omega

-- src/bvm_extras.lean:2727
/-- ℵ₁ is defined as: the least ordinal which does not inject into ω -/
@[reducible] def aleph_one_Ord_spec (x : bSet 𝔹) : 𝔹 :=
  (injects_into x omega)ᶜ ⊓
    (Ord x ⊓ (⨅ y, Ord y ⟹ ((injects_into y bSet.omega)ᶜ ⟹ x ⊆ᴮ y)))

-- src/bvm_extras.lean:2730
@[simp] lemma aleph_one_check_exists_mem {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {Γ : 𝔹} : Γ ≤ exists_mem (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) := by
  apply check_exists_mem
  have : ∃ z, z ∈ PSet.card_ex (Cardinal.aleph (1 : ℕ)) :=
    @PSet.card_ex_aleph_exists_mem 1
  convert this using 2
  norm_cast

-- src/bvm_extras.lean:2736
@[simp] lemma B_ext_Ord : B_ext (Ord : bSet 𝔹 → 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:2736

-- src/bvm_extras.lean:2741
/-- The universal property of ℵ₁: it injects into any ordinal larger than ω -/
@[reducible] def le_of_omega_lt (x : bSet 𝔹) : 𝔹 :=
  ⨅ z, Ord z ⟹ ((larger_than bSet.omega z)ᶜ ⟹ injects_into x z)

-- src/bvm_extras.lean:2743
@[simp] lemma B_ext_le_of_omega_lt : B_ext (le_of_omega_lt : bSet 𝔹 → 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:2743

end ordinals

-- ============================================================
-- src/bvm_extras.lean:2749-2793: section zorns_lemma
-- ============================================================

section zorns_lemma
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2753
theorem bSet_zorns_lemma' {Γ : 𝔹} :
    Γ ≤ ⨅ (X : bSet 𝔹), (X =ᴮ ∅)ᶜ ⟹
      ((⨅ y, (y ⊆ᴮ X ⊓ (⨅ (w₁ : bSet 𝔹), ⨅ (w₂ : bSet 𝔹),
          w₁ ∈ᴮ y ⊓ w₂ ∈ᴮ y ⟹ (w₁ ⊆ᴮ w₂ ⊔ w₂ ⊆ᴮ w₁))) ⟹ bv_union y ∈ᴮ X) ⟹
        (⨆ c, c ∈ᴮ X ⊓ (⨅ z, z ∈ᴮ X ⟹ (c ⊆ᴮ z ⟹ c =ᴮ z)))) := by
  sorry -- TODO: port from src/bvm_extras.lean:2753

end zorns_lemma

-- ============================================================
-- src/bvm_extras.lean:2795-2821: section CH
-- ============================================================

section CH
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras.lean:2803
def CH : 𝔹 :=
  (⨆ (x : bSet 𝔹), Ord x ⊓ ⨆ (y : bSet 𝔹),
    (larger_than omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓
    injects_into y (bv_powerset omega))ᶜ

-- src/bvm_extras.lean:2805
def CH₂ : 𝔹 :=
  (⨆ (x : bSet 𝔹), Ord x ⊓ (larger_than omega x)ᶜ ⊓ (larger_than x (bv_powerset omega))ᶜ)ᶜ

-- src/bvm_extras.lean:2807
lemma CH_iff_CH₂ : ∀ {Γ : 𝔹}, Γ ≤ CH ↔ Γ ≤ CH₂ := by
  intro Γ
  constructor
  · intro H
    sorry -- TODO: port CH_iff_CH₂ from src/bvm_extras.lean:2807
  · intro H
    sorry -- TODO: port CH_iff_CH₂ (reverse) from src/bvm_extras.lean:2807

end CH

end bSet
