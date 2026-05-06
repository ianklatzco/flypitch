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
  sorry -- TODO: port from src/bvm_extras.lean:62

-- src/bvm_extras.lean:69
lemma insert1_symm (y z : bSet 𝔹) : ⊤ ≤ bSet.insert1 y ({z} : bSet 𝔹) =ᴮ bSet.insert1 z ({y} : bSet 𝔹) := by
  sorry -- TODO: port from src/bvm_extras.lean:69

-- src/bvm_extras.lean:78
lemma eq_inserted_of_eq_singleton' {x y z : bSet 𝔹} :
    ({x} : bSet 𝔹) =ᴮ bSet.insert1 y ({z} : bSet 𝔹) ≤ x =ᴮ z := by
  sorry -- TODO: port from src/bvm_extras.lean:78

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
  sorry -- TODO: port from src/bvm_extras.lean:94

-- src/bvm_extras.lean:112
lemma subset_binary_inter_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ z ⊆ᴮ x ∩ᴮ y ↔ (Γ ≤ z ⊆ᴮ x ∧ Γ ≤ z ⊆ᴮ y) := by
  sorry -- TODO: port from src/bvm_extras.lean:112

-- src/bvm_extras.lean:126
lemma binary_inter_symm {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y =ᴮ y ∩ᴮ x := by
  sorry -- TODO: port from src/bvm_extras.lean:126

-- src/bvm_extras.lean:132
lemma B_congr_binary_inter_left {y : bSet 𝔹} : B_congr (fun x => x ∩ᴮ y) := by
  sorry -- TODO: port from src/bvm_extras.lean:132

-- src/bvm_extras.lean:139
lemma B_congr_binary_inter_right {y : bSet 𝔹} : B_congr (fun x => y ∩ᴮ x) := by
  sorry -- TODO: port from src/bvm_extras.lean:139

-- src/bvm_extras.lean:146
lemma binary_inter_subset_left {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ x := by
  sorry -- TODO: port from src/bvm_extras.lean:146

-- src/bvm_extras.lean:150
lemma binary_inter_subset_right {x y : bSet 𝔹} {Γ} : Γ ≤ x ∩ᴮ y ⊆ᴮ y := by
  sorry -- TODO: port from src/bvm_extras.lean:150

-- src/bvm_extras.lean:158
lemma unordered_pair_symm (x y : bSet 𝔹) {Γ : 𝔹} : Γ ≤ ({x, y} : bSet 𝔹) =ᴮ {y, x} := by
  sorry -- TODO: port from src/bvm_extras.lean:158

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
  sorry -- TODO: port from src/bvm_extras.lean:185

-- src/bvm_extras.lean:204
lemma succ_eq_binary_union' {x : bSet 𝔹} {Γ} : Γ ≤ succ x =ᴮ binary_union x ({x} : bSet 𝔹) :=
  bv_trans succ_eq_binary_union binary_union_symm

-- src/bvm_extras.lean:207
@[reducible] def pair (x y : bSet 𝔹) : bSet 𝔹 := ({{x}, {x, y}} : bSet 𝔹)

-- src/bvm_extras.lean:209
@[simp] lemma subst_congr_pair_left {x z y : bSet 𝔹} : x =ᴮ z ≤ pair x y =ᴮ pair z y := by
  sorry -- TODO: port from src/bvm_extras.lean:209

-- src/bvm_extras.lean:216
@[simp] lemma subst_congr_pair_left' {x z y : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x =ᴮ z → Γ ≤ pair x y =ᴮ pair z y :=
  poset_yoneda_inv Γ subst_congr_pair_left

-- src/bvm_extras.lean:219
lemma subst_congr_pair_right {x y z : bSet 𝔹} : y =ᴮ z ≤ pair x y =ᴮ pair x z := by
  sorry -- TODO: port from src/bvm_extras.lean:219

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
  sorry -- TODO: port from src/bvm_extras.lean:276

-- src/bvm_extras.lean:287
lemma inserted_eq_of_insert_eq {y v w : bSet 𝔹} :
    ({v, y} : bSet 𝔹) =ᴮ {v, w} ≤ y =ᴮ w := by
  sorry -- TODO: port from src/bvm_extras.lean:287

-- src/bvm_extras.lean:297
lemma eq_of_eq_pair'_right {x z y : bSet 𝔹} : pair y x =ᴮ pair y z ≤ x =ᴮ z := by
  sorry -- TODO: port from src/bvm_extras.lean:297

-- src/bvm_extras.lean:316
theorem eq_of_eq_pair_left {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ x =ᴮ v := by
  sorry -- TODO: port from src/bvm_extras.lean:316

-- src/bvm_extras.lean:330
lemma eq_of_eq_pair_left' {x y v w : bSet 𝔹} {Γ} :
    Γ ≤ pair x y =ᴮ pair v w → Γ ≤ x =ᴮ v :=
  poset_yoneda_inv Γ eq_of_eq_pair_left

-- src/bvm_extras.lean:333
theorem eq_of_eq_pair_right {x y v w : bSet 𝔹} : pair x y =ᴮ pair v w ≤ y =ᴮ w := by
  sorry -- TODO: port from src/bvm_extras.lean:333

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
  sorry -- TODO: port from src/bvm_extras.lean:371

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
  sorry -- TODO: port from src/bvm_extras.lean:415

-- src/bvm_extras.lean:428
@[simp] lemma B_congr_prod_right {x : bSet 𝔹} : B_congr (fun y => prod x y) := by
  sorry -- TODO: port from src/bvm_extras.lean:428

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
  sorry -- TODO: port from src/bvm_extras.lean:538

-- src/bvm_extras.lean:548
@[reducible] def is_functional (f : bSet 𝔹) : 𝔹 :=
  ⨅ z, (⨆ w, pair z w ∈ᴮ f) ⟹ (⨆ w', ⨅ w'', pair z w'' ∈ᴮ f ⟹ w' =ᴮ w'')

-- src/bvm_extras.lean:551
lemma is_functional_of_is_func (f : bSet 𝔹) {Γ} (H : Γ ≤ is_func f) : Γ ≤ is_functional f := by
  sorry -- TODO: port from src/bvm_extras.lean:551

-- src/bvm_extras.lean:561
@[reducible] def is_total (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ w₁, w₁ ∈ᴮ x ⟹ ⨆ w₂, w₂ ∈ᴮ y ⊓ pair w₁ w₂ ∈ᴮ f

-- src/bvm_extras.lean:565
@[reducible] def is_total' (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ i, x.bval i ⟹ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ᴮ f

-- src/bvm_extras.lean:568
lemma is_total_iff_is_total' {Γ : 𝔹} {x y f} :
    Γ ≤ is_total x y f ↔ Γ ≤ is_total' x y f := by
  sorry -- TODO: port from src/bvm_extras.lean:568

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
  sorry -- TODO: port from src/bvm_extras.lean:628

-- src/bvm_extras.lean:638
lemma mem_image_iff {x y b f : bSet 𝔹} {Γ} :
    Γ ≤ b ∈ᴮ image x y f ↔ (Γ ≤ b ∈ᴮ y) ∧ Γ ≤ ⨆ z, z ∈ᴮ x ⊓ pair z b ∈ᴮ f := by
  sorry -- TODO: port from src/bvm_extras.lean:638

-- src/bvm_extras.lean:649
@[simp] lemma B_congr_image_left {y f : bSet 𝔹} : B_congr (fun x => image x y f) := by
  sorry -- TODO: port from src/bvm_extras.lean:649

-- src/bvm_extras.lean:658
@[simp] lemma B_congr_image_right {x y : bSet 𝔹} : B_congr (fun f => image x y f) := by
  sorry -- TODO: port from src/bvm_extras.lean:658

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
  sorry -- TODO: port from src/bvm_extras.lean:673

/-- f is a function x → y if it is extensional, total, and is a subset of the product of x and y -/
-- src/bvm_extras.lean:684
@[reducible] def is_function (x y f : bSet 𝔹) : 𝔹 :=
  is_func' x y f ⊓ (f ⊆ᴮ prod x y)

-- src/bvm_extras.lean:687
@[simp] lemma B_ext_is_function_left {y f : bSet 𝔹} : B_ext (fun x => is_function x y f) := by
  sorry -- TODO: port from src/bvm_extras.lean:687

-- src/bvm_extras.lean:690
@[simp] lemma B_ext_is_function_right {x y : bSet 𝔹} : B_ext (fun f => is_function x y f) := by
  sorry -- TODO: port from src/bvm_extras.lean:690

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

end extras

end bSet
