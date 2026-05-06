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
  -- need to upgrade w₂ ∈ᴮ y to w₂ ∈ᴮ image x y f
  sorry -- TODO: port from src/bvm_extras.lean:716

-- src/bvm_extras.lean:727
lemma factor_image_is_function {x y f : bSet 𝔹} {Γ} (H_is_function : Γ ≤ is_function x y f) :
    Γ ≤ is_function x (image x y f) f := by
  refine le_inf ?_ ?_
  · exact factor_image_is_func' (is_func'_of_is_function H_is_function)
  · rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
    sorry -- TODO: port from src/bvm_extras.lean:727

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
    B_ext (fun x => is_injective_function x y f) := by
  sorry -- TODO: port from src/bvm_extras.lean:821 (simp timeout)

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
  all_goals {
    apply le_iInf; intro z; rw [← deduction]
    sorry -- TODO: port from src/bvm_extras.lean:879
  }

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
    have H_total := is_total_of_is_func' H_is_func'
    sorry -- TODO: port from src/bvm_extras.lean:900
  · exact binary_inter_subset_right

-- src/bvm_extras.lean:913
lemma function_of_func'_surj_of_surj {x y f : bSet 𝔹} {Γ}
    (H_is_func' : Γ ≤ is_func' x y f) (H_is_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj x y (function_of_func' H_is_func') := by
  apply le_iInf; intro z; rw [← deduction]
  sorry -- TODO: port from src/bvm_extras.lean:913

-- src/bvm_extras.lean:921
lemma function_of_func'_inj_of_inj {x y f : bSet 𝔹} {Γ} {H : Γ ≤ is_func' x y f}
    (H_is_inj : Γ ≤ is_inj f) : Γ ≤ is_inj (function_of_func' H) := by
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction]
  sorry -- TODO: port from src/bvm_extras.lean:921

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
    Γ ≤ injection_into x y := by
  sorry -- TODO: port from src/bvm_extras.lean:954 (needs bv_cases for iSup)

-- src/bvm_extras.lean:963
lemma injects_into_of_injection_into {x y : bSet 𝔹} {Γ} (H_inj : Γ ≤ injection_into x y) :
    Γ ≤ injects_into x y := by
  sorry -- TODO: port from src/bvm_extras.lean:963 (needs bv_cases for iSup)

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
@[simp] lemma B_ext_larger_than_right {y : bSet 𝔹} : B_ext (fun z => larger_than y z) := by
  sorry -- TODO: port from src/bvm_extras.lean:985

-- src/bvm_extras.lean:988
@[simp] lemma B_ext_larger_than_left {y : bSet 𝔹} : B_ext (fun z => larger_than z y) := by
  sorry -- TODO: port from src/bvm_extras.lean:988

-- src/bvm_extras.lean:991
@[simp] lemma B_ext_injects_into_left {y : bSet 𝔹} : B_ext (fun z => injects_into z y) := by
  sorry -- TODO: port from src/bvm_extras.lean:991

-- src/bvm_extras.lean:994
@[simp] lemma B_ext_injects_into_right {y : bSet 𝔹} : B_ext (fun z => injects_into y z) := by
  sorry -- TODO: port from src/bvm_extras.lean:994

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

end extras

end bSet
