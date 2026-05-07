/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
-- Lean 4 port of src/bvm_extras2.lean

import Flypitch4.BvmExtras

open scoped Flypitch
open Lattice

universe u

namespace bSet

-- ============================================================
-- src/bvm_extras2.lean:17-35: section lemmas
-- ============================================================

section lemmas
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:20
lemma prod_subset {x₁ x₂ y₁ y₂ : bSet 𝔹} (H_sub₁ : Γ ≤ x₁ ⊆ᴮ x₂) (H_sub₂ : Γ ≤ y₁ ⊆ᴮ y₂) :
    Γ ≤ prod x₁ y₁ ⊆ᴮ prod x₂ y₂ := by
  rw [subset_unfold']
  apply le_iInf; intro pr; rw [← deduction]
  -- Goal: Γ ⊓ pr ∈ prod x₁ y₁ ≤ pr ∈ prod x₂ y₂
  set ctx := Γ ⊓ pr ∈ᴮ prod x₁ y₁
  have hmem : ctx ≤ pr ∈ᴮ prod x₁ y₁ := inf_le_right
  obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hmem
  apply mem_prod_iff₂.mpr
  exact ⟨v, mem_of_mem_subset (inf_le_left.trans H_sub₁) Hv,
         w, mem_of_mem_subset (inf_le_left.trans H_sub₂) Hw, H_eq⟩

-- src/bvm_extras2.lean:29
lemma prod_subset_left {x₁ x₂ y : bSet 𝔹} (H_sub : Γ ≤ x₁ ⊆ᴮ x₂) :
    Γ ≤ prod x₁ y ⊆ᴮ prod x₂ y :=
  prod_subset H_sub subset_self

-- src/bvm_extras2.lean:32
lemma prod_subset_right {x y₁ y₂ : bSet 𝔹} (H_sub : Γ ≤ y₁ ⊆ᴮ y₂) :
    Γ ≤ prod x y₁ ⊆ᴮ prod x y₂ :=
  prod_subset subset_self H_sub

end lemmas

-- ============================================================
-- src/bvm_extras2.lean:37-62: section inj_inverse_surj
-- ============================================================

section inj_inverse_surj
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {x y f : bSet 𝔹} {Γ : 𝔹}
  (H_func : Γ ≤ is_func' x y f) (H_inj : Γ ≤ is_inj f)

-- src/bvm_extras2.lean:41
lemma inj_inverse.is_total_surj (H_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_total y x (inj_inverse H_func H_inj) := by
  have heq := bv_symm (image_eq_codomain_of_surj H_surj)
  -- is_total z x g = ⨅ w, w ∈ z ⟹ ⨆ w', w' ∈ x ⊓ pair w w' ∈ g
  -- B_ext (fun z => is_total z x g): z appears only in w ∈ z
  apply bv_rw' heq (ϕ := fun z => is_total z x (inj_inverse H_func H_inj))
  · exact B_ext_iInf (h := fun w => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))
  · exact inj_inverse_is_total H_func H_inj

-- src/bvm_extras2.lean:48
lemma inj_inverse.is_function_surj (H_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_function y x (inj_inverse H_func H_inj) := by
  have heq := bv_symm (image_eq_codomain_of_surj H_surj)
  apply bv_rw' heq (ϕ := fun z => is_function z x (inj_inverse H_func H_inj))
  · exact B_ext_is_function_left
  · exact inj_inverse_is_function H_func H_inj

-- src/bvm_extras2.lean:55
lemma inj_inverse.is_surj_surj (H_surj : Γ ≤ is_surj x y f) :
    Γ ≤ is_surj y x (inj_inverse H_func H_inj) := by
  -- is_surj y x g = ⨅ v, v ∈ x ⟹ ⨆ w, w ∈ y ⊓ pair w v ∈ g
  -- inj_inverse_is_surj gives: is_surj (image x y f) x (inj_inverse)
  -- image x y f =ᴮ y via image_eq_codomain_of_surj
  apply bv_rw' (bv_symm (image_eq_codomain_of_surj H_surj))
          (ϕ := fun z => is_surj z x (inj_inverse H_func H_inj))
  · -- B_ext (fun z => is_surj z x g): z appears in w ∈ z, i.e., w ∈ᴮ z inside ⨆ w
    -- is_surj z x g = ⨅ v, v ∈ x ⟹ ⨆ w, w ∈ z ⊓ pair w v ∈ g
    exact B_ext_iInf (h := fun _ =>
      B_ext_imp (h₁ := B_ext_const) (h₂ :=
        B_ext_iSup (h := fun w => B_ext_inf B_ext_mem_right B_ext_const)))
  · exact inj_inverse_is_surj H_func H_inj

end inj_inverse_surj

-- ============================================================
-- src/bvm_extras2.lean:64-345: section Ord
-- ============================================================

section Ord
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹}

-- src/bvm_extras2.lean:67
lemma subset_of_mem_Ord {x y : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_Ord : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y :=
  subset_of_mem_transitive (H_Ord.trans inf_le_right) H_mem

-- src/bvm_extras2.lean:70
lemma mem_of_mem_Ord {x y z : bSet 𝔹} {Γ : 𝔹} (H_mem : Γ ≤ x ∈ᴮ y) (H_mem' : Γ ≤ y ∈ᴮ z)
    (H_ord₂ : Γ ≤ Ord z) : Γ ≤ x ∈ᴮ z :=
  mem_of_mem_subset (subset_of_mem_Ord H_mem' H_ord₂) H_mem

-- src/bvm_extras2.lean:78
lemma transitive_union {u : bSet 𝔹} {Γ : 𝔹} (Hu : Γ ≤ ⨅ z, z ∈ᴮ u ⟹ is_transitive z) :
    Γ ≤ is_transitive (bv_union u) := by
  sorry -- TODO: port from src/bvm_extras2.lean:78

-- src/bvm_extras2.lean:88
lemma transitive_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ is_transitive (x ∩ᴮ y) := by
  sorry -- TODO: port from src/bvm_extras2.lean:88

-- src/bvm_extras2.lean:96
lemma epsilon_trichotomy_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) :
    Γ ≤ epsilon_trichotomy (x ∩ᴮ y) := by
  sorry -- TODO: port from src/bvm_extras2.lean:96

-- src/bvm_extras2.lean:104
lemma epsilon_well_founded_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) :
    Γ ≤ epsilon_well_founded (x ∩ᴮ y) := by
  rw [epsilon_well_founded]
  apply le_iInf; intro w; rw [← deduction, ← deduction]
  -- ctx = Γ ⊓ w ⊆ᴮ (x ∩ᴮ y) ⊓ (w =ᴮ ∅)ᶜ
  -- epsilon_well_founded x = ⨅ u, u ⊆ x ⟹ ((u = ∅)ᶜ ⟹ ⨆ v, ...)
  -- Apply at w with w ⊆ x (via w ⊆ x ∩ y ⊆ x) and w ≠ ∅
  set ctx := Γ ⊓ w ⊆ᴮ x ∩ᴮ y ⊓ (w =ᴮ ∅)ᶜ
  have Hw_sub_x : ctx ≤ w ⊆ᴮ x :=
    subset_trans' (inf_le_left.trans inf_le_right) binary_inter_subset_left
  have Hw_ne : ctx ≤ (w =ᴮ ∅)ᶜ := inf_le_right
  -- epsilon_well_founded x at w
  have Hewf : ctx ≤ epsilon_well_founded x :=
    inf_le_left.trans (inf_le_left.trans
      (le_trans H₁ (inf_le_left.trans inf_le_right)))
  -- epsilon_well_founded x = ⨅ u, u ⊆ x ⟹ ((u = ∅)ᶜ ⟹ ⨆ y, ...)
  have Hewf_w : ctx ≤ w ⊆ᴮ x ⟹ ((w =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ w ⊓ (⨅ z', z' ∈ᴮ w ⟹ (z' ∈ᴮ y)ᶜ)) :=
    le_trans Hewf (iInf_le _ w)
  have h1 : ctx ≤ (w =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ w ⊓ (⨅ z', z' ∈ᴮ w ⟹ (z' ∈ᴮ y)ᶜ) :=
    le_trans (le_inf Hewf_w Hw_sub_x) bv_imp_elim
  exact le_trans (le_inf h1 Hw_ne) bv_imp_elim

-- src/bvm_extras2.lean:112
lemma Ord_binary_inter {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ Ord (binary_inter x y) := by
  sorry -- TODO: port from src/bvm_extras2.lean:112

-- ============================================================
-- src/bvm_extras2.lean:122-158: section compl
-- ============================================================

section compl

def compl (x y : bSet 𝔹) : bSet 𝔹 := comprehend (fun z => (z ∈ᴮ y)ᶜ) x

-- src/bvm_extras2.lean:126
lemma compl_subset {x y : bSet 𝔹} {Γ : 𝔹} : Γ ≤ compl x y ⊆ᴮ x :=
  subset.mk_subset

-- src/bvm_extras2.lean:129
lemma mem_compl_iff {x y : bSet 𝔹} {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ compl x y ↔ (Γ ≤ z ∈ᴮ x ∧ Γ ≤ (z ∈ᴮ y)ᶜ) := by
  sorry -- TODO: port from src/bvm_extras2.lean:129

end compl

-- src/bvm_extras2.lean:141
lemma compl_empty_of_subset {x y : bSet 𝔹} {Γ : 𝔹} (H_sub : Γ ≤ x ⊆ᴮ y) :
    Γ ≤ compl x y =ᴮ ∅ := by
  sorry -- TODO: port from src/bvm_extras2.lean:141

-- src/bvm_extras2.lean:149
lemma nonempty_compl_of_ne {x y : bSet 𝔹} {Γ : 𝔹} (H_ne : Γ ≤ (x =ᴮ y)ᶜ) :
    Γ ≤ ((compl x y =ᴮ ∅)ᶜ) ⊔ ((compl y x =ᴮ ∅)ᶜ) := by
  sorry -- TODO: port from src/bvm_extras2.lean:149

-- src/bvm_extras2.lean:160
lemma eq_iff_not_mem_of_Ord {x y z : bSet 𝔹} {Γ : 𝔹} (H_mem₁ : Γ ≤ x ∈ᴮ z) (H_mem₂ : Γ ≤ y ∈ᴮ z)
    (H_ord : Γ ≤ Ord z) : Γ ≤ x =ᴮ y ↔ (Γ ≤ (x ∈ᴮ y)ᶜ ∧ Γ ≤ (y ∈ᴮ x)ᶜ) := by
  sorry -- TODO: port from src/bvm_extras2.lean:160

-- src/bvm_extras2.lean:173
lemma Ord.lt_of_ne_and_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H_ne : Γ ≤ (x =ᴮ y)ᶜ) (H_le : Γ ≤ x ⊆ᴮ y) : Γ ≤ x ∈ᴮ y := by
  sorry -- TODO: port from src/bvm_extras2.lean:173

-- src/bvm_extras2.lean:201
lemma Ord.le_or_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ⊔ y ⊆ᴮ x := by
  sorry -- TODO: port from src/bvm_extras2.lean:201

-- src/bvm_extras2.lean:220
lemma Ord.trichotomy {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ⊔ x ∈ᴮ y ⊔ y ∈ᴮ x := by
  sorry -- TODO: port from src/bvm_extras2.lean:220

-- src/bvm_extras2.lean:232
lemma Ord.eq_iff_not_mem {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x =ᴮ y ↔ (Γ ≤ (x ∈ᴮ y)ᶜ ∧ Γ ≤ (y ∈ᴮ x)ᶜ) := by
  sorry -- TODO: port from src/bvm_extras2.lean:232

-- src/bvm_extras2.lean:245
lemma Ord.eq_of_not_mem {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H_nmem₁ : Γ ≤ (x ∈ᴮ y)ᶜ) (H_nmem₂ : Γ ≤ (y ∈ᴮ x)ᶜ) : Γ ≤ x =ᴮ y := by
  rw [Ord.eq_iff_not_mem H₁ H₂]; exact ⟨H_nmem₁, H_nmem₂⟩

-- src/bvm_extras2.lean:248
lemma Ord.le_iff_lt_or_eq {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ x ⊆ᴮ y ↔ (Γ ≤ x ∈ᴮ y ⊔ x =ᴮ y) := by
  sorry -- TODO: port from src/bvm_extras2.lean:248

-- src/bvm_extras2.lean:259
lemma Ord.lt_of_not_le {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ (x ⊆ᴮ y)ᶜ → Γ ≤ y ∈ᴮ x := by
  sorry -- TODO: port from src/bvm_extras2.lean:259

-- src/bvm_extras2.lean:271
lemma Ord.resolve_lt {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    Γ ≤ (x ∈ᴮ y)ᶜ → Γ ≤ y ∈ᴮ x ⊔ y =ᴮ x := by
  intro H_not_mem
  sorry -- TODO: port from src/bvm_extras2.lean:271

-- src/bvm_extras2.lean:280
lemma epsilon_trichotomy_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹)
    (H_ord : Γ ≤ ⨅ x, x ∈ᴮ u ⟹ Ord x) :
    Γ ≤ (⨅ y, y ∈ᴮ u ⟹ (⨅ z, z ∈ᴮ u ⟹ (y =ᴮ z ⊔ y ∈ᴮ z ⊔ z ∈ᴮ y))) := by
  apply le_iInf; intro y; rw [← deduction]
  apply le_iInf; intro z; rw [← deduction]
  -- ctx = Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u
  -- H_ord : Γ ≤ ⨅ x, x ∈ u ⟹ Ord x
  have H₁ : Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u ≤ Ord y :=
    le_trans (le_inf
      (inf_le_left.trans (inf_le_left.trans (H_ord.trans (iInf_le _ y))))
      (inf_le_left.trans inf_le_right)) bv_imp_elim
  have H₂ : Γ ⊓ y ∈ᴮ u ⊓ z ∈ᴮ u ≤ Ord z :=
    le_trans (le_inf
      (inf_le_left.trans (inf_le_left.trans (H_ord.trans (iInf_le _ z))))
      inf_le_right) bv_imp_elim
  exact Ord.trichotomy H₁ H₂

-- src/bvm_extras2.lean:289
lemma epsilon_wf_of_sub_Ord {Γ : 𝔹} (u : bSet 𝔹) :
    Γ ≤ (⨅ x, x ⊆ᴮ u ⟹ ((x =ᴮ ∅)ᶜ ⟹ ⨆ y, y ∈ᴮ x ⊓ (⨅ z', z' ∈ᴮ x ⟹ (z' ∈ᴮ y)ᶜ))) := by
  apply le_iInf; intro x; rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity x inf_le_right

-- src/bvm_extras2.lean:295
def exists_two (η : bSet 𝔹) : 𝔹 :=
  (⨅ x, x ∈ᴮ η ⟹ ⨆ z, z ∈ᴮ η ⊓ (x ∈ᴮ z ⊔ z ∈ᴮ x))

-- src/bvm_extras2.lean:297
@[simp] lemma B_ext_exists_two : B_ext (exists_two : bSet 𝔹 → 𝔹) := by
  sorry -- TODO: port from src/bvm_extras2.lean:297

-- src/bvm_extras2.lean:302
lemma one_mem_of_not_zero_and_not_one {η : bSet 𝔹} {Γ : 𝔹} (H_ord : Γ ≤ Ord η)
    (H_not_zero : Γ ≤ (η =ᴮ 0)ᶜ) (H_not_one : Γ ≤ (η =ᴮ 1)ᶜ) : Γ ≤ 1 ∈ᴮ η := by
  sorry -- TODO: port from src/bvm_extras2.lean:302

-- src/bvm_extras2.lean:312
lemma exists_two_iff {η : bSet 𝔹} {Γ : 𝔹} (H_ord : Γ ≤ Ord η) :
    Γ ≤ exists_two η ↔ Γ ≤ (η =ᴮ 1)ᶜ := by
  sorry -- TODO: port from src/bvm_extras2.lean:312

end Ord

-- ============================================================
-- src/bvm_extras2.lean:347-537: section eps_iso
-- ============================================================

section eps_iso
variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:350
@[reducible] def strong_eps_hom (x y f : bSet 𝔹) : 𝔹 :=
  ⨅ z₁, z₁ ∈ᴮ x ⟹ ⨅ z₂, z₂ ∈ᴮ x ⟹ ⨅ w₁, w₁ ∈ᴮ y ⟹ ⨅ w₂, w₂ ∈ᴮ y ⟹
    (pair z₁ w₁ ∈ᴮ f ⟹ (pair z₂ w₂ ∈ᴮ f ⟹ (z₁ ∈ᴮ z₂ ⇔ w₁ ∈ᴮ w₂)))

-- src/bvm_extras2.lean:352
lemma strong_eps_hom_iff {x y f : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ strong_eps_hom x y f ↔
    ∀ {Γ'} (_H_le : Γ' ≤ Γ), ∀ z₁ (_Hz₁_mem : Γ' ≤ z₁ ∈ᴮ x) (z₂) (_Hz₂_mem : Γ' ≤ z₂ ∈ᴮ x)
      (w₁) (_Hw₁_mem : Γ' ≤ w₁ ∈ᴮ y) (w₂) (_Hw₂_mem : Γ' ≤ w₂ ∈ᴮ y)
      (_Hpr₁_mem : Γ' ≤ pair z₁ w₁ ∈ᴮ f) (_Hpr₂_mem : Γ' ≤ pair z₂ w₂ ∈ᴮ f),
      Γ' ≤ z₁ ∈ᴮ z₂ ↔ Γ' ≤ w₁ ∈ᴮ w₂ := by
  sorry -- TODO: port from src/bvm_extras2.lean:352

-- src/bvm_extras2.lean:365
lemma strong_eps_hom_unfold {x y f : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ strong_eps_hom x y f) :
    ∀ z₁ (Hz₁_mem : Γ ≤ z₁ ∈ᴮ x) (z₂) (Hz₂_mem : Γ ≤ z₂ ∈ᴮ x)
      (w₁) (Hw₁_mem : Γ ≤ w₁ ∈ᴮ y) (w₂) (Hw₂_mem : Γ ≤ w₂ ∈ᴮ y)
      (Hpr₁_mem : Γ ≤ pair z₁ w₁ ∈ᴮ f) (Hpr₂_mem : Γ ≤ pair z₂ w₂ ∈ᴮ f),
      Γ ≤ z₁ ∈ᴮ z₂ ↔ Γ ≤ w₁ ∈ᴮ w₂ :=
    fun z₁ Hz₁ z₂ Hz₂ w₁ Hw₁ w₂ Hw₂ Hpr₁ Hpr₂ => by
  -- strong_eps_hom x y f = ⨅ z₁, z₁∈x ⟹ ⨅ z₂, z₂∈x ⟹ ⨅ w₁, w₁∈y ⟹ ⨅ w₂, w₂∈y ⟹
  --   pair z₁ w₁ ∈ f ⟹ (pair z₂ w₂ ∈ f ⟹ (z₁∈z₂ ⇔ w₁∈w₂))
  have h1 := le_trans H (iInf_le _ z₁)
  have h2 := le_trans (le_inf h1 Hz₁) bv_imp_elim
  have h3 := le_trans h2 (iInf_le _ z₂)
  have h4 := le_trans (le_inf h3 Hz₂) bv_imp_elim
  have h5 := le_trans h4 (iInf_le _ w₁)
  have h6 := le_trans (le_inf h5 Hw₁) bv_imp_elim
  have h7 := le_trans h6 (iInf_le _ w₂)
  have h8 := le_trans (le_inf h7 Hw₂) bv_imp_elim
  have h9 := le_trans (le_inf h8 Hpr₁) bv_imp_elim
  have h10 := le_trans (le_inf h9 Hpr₂) bv_imp_elim
  rw [bv_biimp_iff] at h10
  exact h10 le_rfl

-- src/bvm_extras2.lean:371
def eps_iso (x y f : bSet 𝔹) : 𝔹 :=
  is_function x y f ⊓ (strong_eps_hom x y f) ⊓ is_surj x y f

-- src/bvm_extras2.lean:373
lemma is_surj_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹} (H_eps_iso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_surj x y f :=
  le_trans H_eps_iso inf_le_right

-- src/bvm_extras2.lean:376
lemma is_function_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹} (H_eps_iso : Γ ≤ eps_iso x y f) :
    Γ ≤ is_function x y f :=
  le_trans H_eps_iso (inf_le_left.trans inf_le_left)

-- src/bvm_extras2.lean:379
lemma strong_eps_hom_of_eps_iso {x y f : bSet 𝔹} {Γ : 𝔹} (H_eps_iso : Γ ≤ eps_iso x y f) :
    Γ ≤ strong_eps_hom x y f :=
  le_trans H_eps_iso (inf_le_left.trans inf_le_right)

-- src/bvm_extras2.lean:382
lemma eps_iso_mem {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) (H_mem'' : Γ ≤ z₁ ∈ᴮ z₂)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ w₁ ∈ᴮ w₂ :=
  (strong_eps_hom_unfold (strong_eps_hom_of_eps_iso H₂)
    z₁ H_mem z₂ H_mem' w₁ H_mem''' w₂ H_mem'''' H_mem_pr₁ H_mem_pr₂).mp H_mem''

-- src/bvm_extras2.lean:385
lemma eps_iso_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f)
    (H_mem'' : Γ ≤ w₁ ∈ᴮ w₂) : Γ ≤ z₁ ∈ᴮ z₂ :=
  (strong_eps_hom_unfold (strong_eps_hom_of_eps_iso H₂)
    z₁ H_mem z₂ H_mem' w₁ H_mem''' w₂ H_mem'''' H_mem_pr₁ H_mem_pr₂).mpr H_mem''

-- src/bvm_extras2.lean:388
lemma eps_iso_not_mem {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x) (H_mem'' : Γ ≤ (z₁ ∈ᴮ z₂)ᶜ)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f) : Γ ≤ (w₁ ∈ᴮ w₂)ᶜ := by
  simp only [← imp_bot] at H_mem'' ⊢
  rw [← deduction] at H_mem'' ⊢
  -- ctx = Γ ⊓ z₁ ∈ z₂, goal: ⊥, similarly H_mem'' : Γ ⊓ z₁ ∈ z₂ ≤ ⊥
  sorry -- TODO: port from src/bvm_extras2.lean:388

-- src/bvm_extras2.lean:394
lemma eps_iso_not_mem' {x y f z₁ z₂ : bSet 𝔹} {Γ : 𝔹} (H₂ : Γ ≤ eps_iso x y f)
    (H_mem : Γ ≤ z₁ ∈ᴮ x) (H_mem' : Γ ≤ z₂ ∈ᴮ x)
    {w₁} (H_mem''' : Γ ≤ w₁ ∈ᴮ y) (H_mem_pr₁ : Γ ≤ pair z₁ w₁ ∈ᴮ f)
    {w₂} (H_mem'''' : Γ ≤ w₂ ∈ᴮ y) (H_mem_pr₂ : Γ ≤ pair z₂ w₂ ∈ᴮ f)
    (H_mem'' : Γ ≤ (w₁ ∈ᴮ w₂)ᶜ) : Γ ≤ (z₁ ∈ᴮ z₂)ᶜ := by
  simp only [← imp_bot] at H_mem'' ⊢
  rw [← deduction] at H_mem'' ⊢
  sorry -- TODO: port from src/bvm_extras2.lean:394

-- src/bvm_extras2.lean:400
lemma eps_iso_inj_of_Ord {x y f : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H₃ : Γ ≤ eps_iso x y f) : Γ ≤ is_inj f := by
  sorry -- TODO: port from src/bvm_extras2.lean:400

-- src/bvm_extras2.lean:423
def eps_iso_inv {x y f : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y)
    (H₃ : Γ ≤ eps_iso x y f) : bSet 𝔹 :=
  inj_inverse (is_func'_of_is_function (is_function_of_eps_iso H₃))
    (eps_iso_inj_of_Ord H₁ H₂ H₃)

-- src/bvm_extras2.lean:425
lemma eps_iso_inv_surj {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ is_surj y x (eps_iso_inv H₁ H₂ H₃) :=
  inj_inverse.is_surj_surj
    (H_func := is_func'_of_is_function (is_function_of_eps_iso H₃))
    (H_inj := eps_iso_inj_of_Ord H₁ H₂ H₃)
    (is_surj_of_eps_iso H₃)

-- src/bvm_extras2.lean:428
lemma eps_iso_inv_is_function {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ is_function y x (eps_iso_inv H₁ H₂ H₃) :=
  inj_inverse.is_function_surj
    (H_func := is_func'_of_is_function (is_function_of_eps_iso H₃))
    (H_inj := eps_iso_inj_of_Ord H₁ H₂ H₃)
    (is_surj_of_eps_iso H₃)

-- src/bvm_extras2.lean:433
lemma eps_iso_inv_strong_eps_hom {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ strong_eps_hom y x (eps_iso_inv H₁ H₂ H₃) := by
  sorry -- TODO: port from src/bvm_extras2.lean:433

-- src/bvm_extras2.lean:449
lemma eps_iso_eps_iso_inv {x y f : bSet 𝔹} {Γ : 𝔹} {H₁ : Γ ≤ Ord x} {H₂ : Γ ≤ Ord y}
    {H₃ : Γ ≤ eps_iso x y f} : Γ ≤ eps_iso y x (eps_iso_inv H₁ H₂ H₃) :=
  le_inf (le_inf eps_iso_inv_is_function eps_iso_inv_strong_eps_hom) eps_iso_inv_surj

-- src/bvm_extras2.lean:453
lemma eps_iso_symm {x y : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord x) (H₂ : Γ ≤ Ord y) :
    (Γ ≤ ⨆ f, eps_iso x y f) ↔ (Γ ≤ ⨆ f, eps_iso y x f) := by
  sorry -- TODO: port from src/bvm_extras2.lean:453

-- src/bvm_extras2.lean:460
lemma eps_iso_mono {x y z f : bSet 𝔹} {Γ : 𝔹} (H₁ : Γ ≤ Ord y) (H₂ : Γ ≤ z ⊆ᴮ y)
    (H₃ : Γ ≤ eps_iso y z f) (H₄ : Γ ≤ x ∈ᴮ y) (w' : bSet 𝔹)
    (Hw' : Γ ≤ pair x w' ∈ᴮ f) : Γ ≤ x ⊆ᴮ w' := by
  sorry -- TODO: port from src/bvm_extras2.lean:460

-- src/bvm_extras2.lean:505
lemma eq_of_Ord_eps_iso_aux {x y : bSet 𝔹} {Γ : 𝔹} (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y)
    (H_eps_iso : Γ ≤ ⨆ f, eps_iso y x f) (H_mem : Γ ≤ x ∈ᴮ y) : Γ ≤ ⊥ := by
  sorry -- TODO: port from src/bvm_extras2.lean:505

-- src/bvm_extras2.lean:526
lemma eq_of_Ord_eps_iso {x y : bSet 𝔹} {Γ : 𝔹} (Hx_ord : Γ ≤ Ord x) (Hy_ord : Γ ≤ Ord y)
    (H_eps_iso : Γ ≤ ⨆ f, eps_iso x y f) : Γ ≤ x =ᴮ y := by
  sorry -- TODO: port from src/bvm_extras2.lean:526

end eps_iso

-- ============================================================
-- src/bvm_extras2.lean:539-597: remainder
-- ============================================================

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/bvm_extras2.lean:541
def is_limit (η : bSet 𝔹) : 𝔹 :=
  (∅ ∈ᴮ η) ⊓ (⨅ x, x ∈ᴮ η ⟹ ⨆ y, y ∈ᴮ η ⊓ x ∈ᴮ y)

-- src/bvm_extras2.lean:543
lemma is_epsilon_well_founded {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ epsilon_well_founded x := by
  rw [epsilon_well_founded]
  apply le_iInf; intro u; rw [← deduction, ← deduction]
  exact bSet_axiom_of_regularity u inf_le_right

-- src/bvm_extras2.lean:546
lemma Ord_succ {η : bSet 𝔹} {Γ : 𝔹} (H_Ord : Γ ≤ Ord η) : Γ ≤ Ord (succ η) := by
  sorry -- TODO: port from src/bvm_extras2.lean:546

-- src/bvm_extras2.lean:563
lemma Ord.succ_le_of_lt {η ρ : bSet 𝔹} {Γ : 𝔹} (H_Ord' : Γ ≤ Ord ρ) (H_lt : Γ ≤ η ∈ᴮ ρ) :
    Γ ≤ succ η ⊆ᴮ ρ := by
  sorry -- TODO: port from src/bvm_extras2.lean:563

-- src/bvm_extras2.lean:572
lemma omega_least_is_limit {Γ : 𝔹} :
    Γ ≤ ⨅ η, Ord η ⟹ ((is_limit η) ⟹ omega ⊆ᴮ η) := by
  sorry -- TODO: port from src/bvm_extras2.lean:572

end bSet
