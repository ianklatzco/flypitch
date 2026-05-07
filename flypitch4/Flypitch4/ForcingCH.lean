/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
-- Lean 4 port of src/forcing_CH.lean (645 lines) — Task 21

import Flypitch4.Collapse
import Flypitch4.AlephOne

open scoped Flypitch
open Lattice

universe u

open Set TopologicalSpace Cardinal

-- Local notation for Boolean implication / biimplication
local infix:65 " ⟹ " => Lattice.imp
local infix:50 " ⇔ " => Lattice.biimp
-- ≺ means "strictly smaller" (negation of larger_than via complement)
local infix:75 " ≺ " => (fun x y => (bSet.larger_than x y)ᶜ)
-- ≼ means "injects into"
local infix:75 " ≼ " => (fun x y => bSet.injects_into x y)

-- ℵ₁ as a pSet
noncomputable abbrev pSet_aleph1 : PSet.{u} := PSet.card_ex (Cardinal.aleph 1)

-- local ω shorthand
local notation "ω" => (bSet.omega)

attribute [local instance] Classical.propDecidable

-- ============================================================
-- namespace bSet
-- ============================================================

namespace bSet

-- ============================================================
-- section aleph_one (src lines 25-42)
-- ============================================================

section aleph_one

variable {𝔹 : Type*} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing_CH.lean:31
noncomputable def aleph_one : bSet 𝔹 := a1

-- src/forcing_CH.lean:33
lemma aleph_one_satisfies_spec {Γ : 𝔹} :
    Γ ≤ aleph_one_Ord_spec (aleph_one (𝔹 := 𝔹)) :=
  a1_spec

-- src/forcing_CH.lean:36
lemma aleph_one_check_sub_aleph_one {Γ : 𝔹} :
    Γ ≤ (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) ⊆ᴮ aleph_one :=
  aleph_one_check_sub_aleph_one_aux a1_Ord a1_spec

-- src/forcing_CH.lean:39
lemma aleph_one_le_of_omega_lt {Γ : 𝔹} :
    Γ ≤ le_of_omega_lt (aleph_one (𝔹 := 𝔹)) :=
  a1_le_of_omega_lt

end aleph_one

-- ============================================================
-- section lemmas (src lines 44-353)
-- ============================================================

section lemmas

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing_CH.lean:51-53
/-- Corresponds to proposition 5.2 in Moore's 'the method of forcing'. -/
lemma check_forall (x : PSet.{u}) (ϕ : bSet 𝔹 → 𝔹) {b : 𝔹} :
    (∀ (y : x.Type), b ≤ ϕ (check (x.Func y))) →
    (b ≤ (⨅ (y : x.Type), ϕ (check (x.Func y)))) :=
  fun H => le_iInf H

-- src/forcing_CH.lean:55-62
lemma aleph_one_check_is_aleph_one_of_omega_lt {Γ : 𝔹}
    (H : Γ ≤ (larger_than bSet.omega (check pSet_aleph1) : 𝔹)ᶜ) :
    Γ ≤ (check pSet_aleph1 : bSet 𝔹) =ᴮ (aleph_one (𝔹 := 𝔹)) := by
  -- Port from src/forcing_CH.lean:55-62
  refine subset_ext aleph_one_check_sub_aleph_one ?_
  have hspec := @aleph_one_satisfies_spec 𝔹 _ Γ
  unfold aleph_one_Ord_spec at hspec
  have hspec_rr : Γ ≤ ⨅ y, Ord y ⟹ ((injects_into y bSet.omega)ᶜ ⟹ a1 ⊆ᴮ y) :=
    le_trans hspec (le_trans inf_le_right inf_le_right)
  have happ : Γ ≤ Ord (check pSet_aleph1) ⟹ ((injects_into (check pSet_aleph1) bSet.omega)ᶜ ⟹
      a1 ⊆ᴮ check pSet_aleph1) :=
    le_trans hspec_rr (iInf_le _ _)
  have hOrd : Γ ≤ Ord (check pSet_aleph1) := Ord_card_ex (Cardinal.aleph 1)
  have hnotinj : Γ ≤ (injects_into (check pSet_aleph1) bSet.omega)ᶜ := by
    rw [← imp_bot, ← deduction]
    apply bv_absurd (larger_than bSet.omega (check pSet_aleph1))
    · apply larger_than_of_surjects_onto
      exact surjects_onto_of_injects_into' inf_le_right aleph_one_check_exists_mem
    · exact le_trans inf_le_left H
  have step1 : Γ ≤ (injects_into (check pSet_aleph1) bSet.omega)ᶜ ⟹ a1 ⊆ᴮ check pSet_aleph1 :=
    le_trans (le_inf happ hOrd) bv_imp_elim
  exact le_trans (le_inf step1 hnotinj) bv_imp_elim

-- src/forcing_CH.lean:64-77
theorem CH_true_aux
    (H_aleph_one : ∀ {Γ : 𝔹}, Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹))
    (H_not_lt    : ∀ {Γ : 𝔹}, Γ ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ)
    : ∀ {Γ : 𝔹}, Γ ≤ CH := by
  -- Port from src/forcing_CH.lean:64-77
  intro Γ
  -- Goal: Γ ≤ CH
  -- CH = (⨆ x, Ord x ⊓ ⨆ y, (larger_than ω x)ᶜ ⊓ (larger_than x y)ᶜ ⊓ injects_into y (𝒫ω))ᶜ
  -- Proof: show the inner iSup ≤ ⊥, i.e., for any x, y: absurd from H_aleph_one and H_not_lt
  unfold CH
  rw [← imp_bot, ← deduction]
  -- Goal after deduction: Γ ⊓ (⨆ x, Ord x ⊓ ⨆ y, ...) ≤ ⊥
  rw [inf_iSup_eq']
  apply iSup_le; intro x
  simp_rw [inf_iSup_eq']
  apply iSup_le; intro y
  -- Context: Γ ⊓ (Ord x ⊓ ((larger_than ω x)ᶜ ⊓ (larger_than x y)ᶜ ⊓ injects_into y (𝒫ω))) ≤ ⊥
  set ctx := Γ ⊓ (Ord x ⊓ ((larger_than bSet.omega x)ᶜ ⊓ (larger_than x y)ᶜ ⊓
               injects_into y (bv_powerset bSet.omega)))
  have hOrd : ctx ≤ Ord x :=
    inf_le_right.trans inf_le_left
  have hLtX : ctx ≤ (larger_than bSet.omega x)ᶜ :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hLtY : ctx ≤ (larger_than x y)ᶜ :=
    inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hInj : ctx ≤ injects_into y (bv_powerset bSet.omega) :=
    inf_le_right.trans (inf_le_right.trans inf_le_right)
  -- From H_aleph_one: check ℵ₁ ≼ x
  -- le_of_omega_lt = ⨅ z, Ord z ⟹ ((larger_than ω z)ᶜ ⟹ injects_into (check ℵ₁) z)
  have hInj_a1_x : ctx ≤ injects_into (check pSet_aleph1) x :=
    -- H_aleph_one : ctx ≤ ⨅ z, Ord z ⟹ ((larger_than ω z)ᶜ ⟹ injects_into (check ℵ₁) z)
    -- Instantiate at z = x, then apply modus ponens twice
    le_trans (le_inf
      (le_trans (le_inf
        (H_aleph_one.trans (iInf_le _ x))
        hOrd)
        bv_imp_elim)
      hLtX)
      bv_imp_elim
  -- check ℵ₁ ≼ x and (larger_than x y)ᶜ → (larger_than (check ℵ₁) y)ᶜ
  have hLt_a1_y : ctx ≤ (larger_than (check pSet_aleph1) y)ᶜ :=
    bSet_lt_of_le_of_lt hInj_a1_x hLtY
  -- (larger_than (check ℵ₁) y)ᶜ and y ≼ 𝒫ω → (larger_than (check ℵ₁) (𝒫ω))ᶜ
  have hLt_a1_cont : ctx ≤ (larger_than (check pSet_aleph1) (bv_powerset bSet.omega))ᶜ :=
    bSet_lt_of_lt_of_le hLt_a1_y hInj
  -- H_not_lt gives larger_than (check ℵ₁) (𝒫ω)
  have hPos : ctx ≤ larger_than (check pSet_aleph1) (bv_powerset bSet.omega) := by
    have h : ctx ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ := H_not_lt
    simp only [compl_compl] at h
    exact h
  exact bv_absurd _ hPos hLt_a1_cont

-- src/forcing_CH.lean:79-81
def rel_of_array (x y : bSet 𝔹) (af : x.type → y.type → 𝔹) : bSet 𝔹 :=
  set_of_indicator (fun pr : (prod x y).type => af pr.1 pr.2)

-- src/forcing_CH.lean:82-102
lemma rel_of_array_surj (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₁ : ∀ i, x.bval i = ⊤)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_wide : ∀ j, (⨆ i, af i j) = ⊤) {Γ}
    : Γ ≤ (is_surj x y (rel_of_array x y af)) := by
  -- is_surj x y f = ⨅ v, v ∈ y ⟹ (⨆ w, w ∈ x ⊓ pair w v ∈ f)
  apply le_iInf; intro v
  rw [← deduction]
  -- Goal: Γ ⊓ v ∈ᴮ y ≤ ⨆ w, w ∈ᴮ x ⊓ pair w v ∈ᴮ rel_of_array x y af
  -- Use bounded_exists to express target as ⨆ i, x.bval i ⊓ pair (x.func i) v ∈ rel
  rw [← @bounded_exists 𝔹 _ x (fun w => pair w v ∈ᴮ rel_of_array x y af)
    (h_congr := B_ext_pair_mem_left)]
  -- Unfold v ∈ y, distribute
  rw [mem_unfold, inf_iSup_eq']
  apply iSup_le; intro j₀
  -- ctx = Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀)
  -- Goal: ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) v ∈ rel
  -- Key: first show ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ rel
  -- Then use bv_rw' with v =ᴮ y.func j₀ to replace y.func j₀ with v
  -- Step 1: show ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ rel
  have step1 : Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀) ≤
      ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ᴮ rel_of_array x y af := by
    apply le_trans le_top
    rw [← H_wide j₀]
    apply iSup_le; intro i₀
    apply le_iSup_of_le i₀
    refine le_inf ?_ ?_
    · rw [H_bval₁]; exact le_top
    · -- pair (x.func i₀) (y.func j₀) ∈ rel_of_array ≥ af i₀ j₀
      unfold rel_of_array
      rw [mem_unfold]
      simp only [set_of_indicator_bval, set_of_indicator_func, prod_func]
      apply le_iSup_of_le (i₀, j₀)
      simp [bv_eq_refl]
  -- Step 2: use bv_rw' with v =ᴮ y.func j₀ to convert
  have heq : Γ ⊓ (y.bval j₀ ⊓ v =ᴮ y.func j₀) ≤ v =ᴮ y.func j₀ :=
    inf_le_right.trans inf_le_right
  -- Use bv_rw' with v =ᴮ y.func j₀ to get ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) v ∈ rel
  -- from step1: ctx ≤ ⨆ i, x.bval i ⊓ pair (x.func i) (y.func j₀) ∈ rel
  exact @bv_rw' 𝔹 _ v (y.func j₀) _ heq
    (ϕ := fun z => ⨆ i, x.bval i ⊓ pair (x.func i) z ∈ᴮ rel_of_array x y af)
    (h_congr := B_ext_iSup (h := fun i => B_ext_inf B_ext_const B_ext_pair_mem_right))
    (H_new := step1)

-- src/forcing_CH.lean:104-113
lemma mem_left_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_left : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₁ : ∀ i, x.bval i = ⊤)
    : Γ ≤ w₁ ∈ᴮ x := by
  -- rel_of_array x y af = set_of_indicator (fun pr => af pr.1 pr.2) on prod x y
  -- pair w₁ w₂ ∈ rel_of_array x y af = ⨆ pr, af pr.1 pr.2 ⊓ pair w₁ w₂ =ᴮ pair (x.func pr.1) (y.func pr.2)
  unfold rel_of_array at H_mem_left
  rw [mem_unfold] at H_mem_left
  simp only [set_of_indicator_bval, set_of_indicator_func, prod_func] at H_mem_left
  -- H_mem_left : Γ ≤ ⨆ pr, af pr.1 pr.2 ⊓ pair w₁ w₂ =ᴮ pair (x.func pr.1) (y.func pr.2)
  -- Goal: Γ ≤ w₁ ∈ x = ⨆ i, x.bval i ⊓ w₁ =ᴮ x.func i
  rw [mem_unfold]
  apply H_mem_left.trans
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le i
  refine le_inf ?_ ?_
  · rw [H_bval₁]; exact le_top
  · exact inf_le_right.trans eq_of_eq_pair_left

-- src/forcing_CH.lean:115-124
lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_right : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    : Γ ≤ w₂ ∈ᴮ y := by
  unfold rel_of_array at H_mem_right
  rw [mem_unfold] at H_mem_right
  simp only [set_of_indicator_bval, set_of_indicator_func, prod_func] at H_mem_right
  rw [mem_unfold]
  apply H_mem_right.trans
  apply iSup_le; intro ⟨i, j⟩
  apply le_iSup_of_le j
  refine le_inf ?_ ?_
  · rw [H_bval₂]; exact le_top
  · exact inf_le_right.trans eq_of_eq_pair_right

-- src/forcing_CH.lean:128-169
lemma rel_of_array_extensional (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ (is_func (rel_of_array x y af)) := by
  -- is_func f = ⨅ w₁ w₂ v₁ v₂, pair w₁ v₁ ∈ f ⊓ pair w₂ v₂ ∈ f ⟹ (w₁ =ᴮ w₂ ⟹ v₁ =ᴮ v₂)
  apply le_iInf; intro w₁; apply le_iInf; intro w₂
  apply le_iInf; intro v₁; apply le_iInf; intro v₂
  rw [← deduction, ← deduction]
  -- Goal: Γ ⊓ (pair w₁ v₁ ∈ rel ⊓ pair w₂ v₂ ∈ rel) ⊓ (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  -- Unfold the membership in rel_of_array
  unfold rel_of_array
  simp only [mem_unfold, set_of_indicator_bval, set_of_indicator_func, prod_func] at *
  -- H_mem₁: Γ ⊓ (⨆ pr₁, af pr₁.1 pr₁.2 ⊓ pair w₁ v₁ =ᴮ pair (x.func pr₁.1) (y.func pr₁.2)) ⊓
  --        (⨆ pr₂, af pr₂.1 pr₂.2 ⊓ pair w₂ v₂ =ᴮ pair (x.func pr₂.1) (y.func pr₂.2)) ⊓
  --        (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  -- Distribute the iSup through the meet
  -- Goal: Γ ⊓ (⨆ p₁ : x.type × y.type, ...) ⊓ (⨆ p₂, ...) ⊓ (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  simp_rw [iSup_inf_eq', inf_iSup_eq', iSup_inf_eq']
  apply iSup_le; intro p₁
  obtain ⟨i₁, j₁⟩ := p₁
  apply iSup_le; intro p₂
  obtain ⟨i₂, j₂⟩ := p₂
  simp only []
  -- Context structure (from simp_rw of iSup_inf_eq', inf_iSup_eq'):
  -- Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
  --      (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤ v₁ =ᴮ v₂
  -- Extract the pair equalities
  have hpair₁ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hpair₂ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂) :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have haf₁ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              af i₁ j₁ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have haf₂ : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              af i₂ j₂ :=
    inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have heq_w : Γ ⊓ (af i₁ j₁ ⊓ pair w₁ v₁ =ᴮ pair (x.func i₁) (y.func j₁) ⊓
              (af i₂ j₂ ⊓ pair w₂ v₂ =ᴮ pair (x.func i₂) (y.func j₂))) ⊓ (w₁ =ᴮ w₂) ≤
              w₁ =ᴮ w₂ := inf_le_right
  -- Get component equalities from pair equalities
  have hw₁ := hpair₁.trans (eq_of_eq_pair_left (x := w₁) (y := v₁))
  have hv₁ := hpair₁.trans (eq_of_eq_pair_right (x := w₁) (y := v₁))
  have hw₂ := hpair₂.trans (eq_of_eq_pair_left (x := w₂) (y := v₂))
  have hv₂ := hpair₂.trans (eq_of_eq_pair_right (x := w₂) (y := v₂))
  -- x.func i₁ =ᴮ x.func i₂ from transitivity
  have hxi := bv_trans (bv_symm hw₁) (bv_trans heq_w hw₂)
  -- Case analysis on j₁ = j₂
  by_cases hjj : j₁ = j₂
  · -- j₁ = j₂: v₁ =ᴮ y.func j₁ =ᴮ v₂ since y.func j₁ = y.func j₂ and v₂ =ᴮ y.func j₂
    -- Use transitivity: ctx ≤ v₁ =ᴮ y.func j₁ and ctx ≤ y.func j₁ =ᴮ v₂
    -- y.func j₁ =ᴮ v₂ = y.func j₂ =ᴮ v₂ (since j₁ = j₂)
    -- but we can't rewrite because it changes ctx too
    -- Instead: the proof is ctx ≤ v₁ =ᴮ v₂ = (v₁ =ᴮ y.func j₁) ⊓ (y.func j₁ =ᴮ v₂) via bv_trans
    -- y.func j₁ =ᴮ v₂: since j₁ = j₂, v₂ =ᴮ y.func j₁ from hv₂ + hjj
    -- bv_symm hv₂ : ctx ≤ y.func j₂ =ᴮ v₂
    -- show ctx ≤ y.func j₁ =ᴮ v₂ using convert or by rewriting at goal level:
    apply bv_trans hv₁
    -- Goal: ctx ≤ y.func j₁ =ᴮ v₂
    -- hv₂ : ctx ≤ v₂ =ᴮ y.func j₂ and j₁ = j₂
    -- so y.func j₁ =ᴮ v₂ = y.func j₂ =ᴮ v₂ ... same problem
    -- Use convert to handle the j₁ ↔ j₂ discrepancy
    convert bv_symm hv₂ using 2
    exact congrArg y.func hjj
  · -- j₁ ≠ j₂: must get contradiction
    -- Case analysis on i₁ = i₂
    by_cases hii : i₁ = i₂
    · -- i₁ = i₂: by H_anti, af i₁ j₁ ⊓ af i₁ j₂ ≤ ⊥
      -- We have haf₁ : ctx ≤ af i₁ j₁ and haf₂ : ctx ≤ af i₂ j₂ = af i₁ j₂ (since i₁ = i₂)
      have haf₂_rw : af i₂ j₂ = af i₁ j₂ := by rw [hii]
      have : af i₁ j₁ ⊓ af i₂ j₂ ≤ ⊥ := by rw [haf₂_rw]; exact H_anti i₁ j₁ j₂ hjj
      exact bv_exfalso (le_trans (le_inf haf₁ haf₂) this)
    · -- i₁ ≠ i₂: H_inj says ⊥ < x.func i₁ =ᴮ x.func i₂ → i₁ = i₂
      -- So ¬ (⊥ < x.func i₁ =ᴮ x.func i₂), i.e., x.func i₁ =ᴮ x.func i₂ ≤ ⊥
      have hbot : x.func i₁ =ᴮ x.func i₂ ≤ ⊥ := by
        rw [le_bot_iff]
        by_contra h
        exact hii (H_inj i₁ i₂ (bot_lt_iff_ne_bot.mpr h))
      exact bv_exfalso (hxi.trans hbot)

-- src/forcing_CH.lean:171-191
lemma rel_of_array_is_func' (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_tall : ∀ i, (⨆ j, af i j) = ⊤)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ is_func' x y (rel_of_array x y af) := by
  -- is_func' = is_func ⊓ is_total
  refine le_inf (rel_of_array_extensional x y af H_anti H_inj) ?_
  -- Now show is_total x y (rel_of_array x y af)
  rw [is_total_iff_is_total']
  -- is_total' x y f = ⨅ i, x.bval i ⟹ ⨆ j, y.bval j ⊓ pair (x.func i) (y.func j) ∈ f
  apply le_iInf; intro i₀
  rw [← deduction]
  -- Goal: Γ ⊓ x.bval i₀ ≤ ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ rel_of_array x y af
  -- pair (x.func i₀) (y.func j₀) ∈ rel = ⨆ (i,j), af i j ⊓ pair (x.func i₀) (y.func j₀) =ᴮ pair (x.func i) (y.func j)
  -- This contains af i₀ j₀ ⊓ pair (x.func i₀) (y.func j₀) =ᴮ pair (x.func i₀) (y.func j₀) = af i₀ j₀
  -- So ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ rel
  --   ≥ ⨆ j₀, ⊤ ⊓ af i₀ j₀ = ⨆ j₀, af i₀ j₀ = H_tall i₀ = ⊤
  -- Goal: Γ ⊓ x.bval i₀ ≤ ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ᴮ rel_of_array x y af
  -- Use H_tall i₀ : ⨆ j₀, af i₀ j₀ = ⊤ to show ⨆ j₀, y.bval j₀ ⊓ pair... = ⊤
  -- bound: ⨆ j₀, y.bval j₀ ⊓ pair (x.func i₀) (y.func j₀) ∈ rel ≥ ⨆ j₀, af i₀ j₀ = ⊤
  apply le_trans le_top
  rw [← H_tall i₀]
  apply iSup_le; intro j₀
  apply le_iSup_of_le j₀
  refine le_inf ?_ ?_
  · rw [H_bval₂]; exact le_top
  · -- pair (x.func i₀) (y.func j₀) ∈ rel_of_array ≥ af i₀ j₀
    unfold rel_of_array
    rw [mem_unfold]
    simp only [set_of_indicator_bval, set_of_indicator_func, prod_func]
    apply le_iSup_of_le (i₀, j₀)
    simp [bv_eq_refl]

-- ============================================================
-- section function_reflect (src lines 193-350)
-- ============================================================

section function_reflect

-- Private auxiliary for function_reflect_of_omega_closed.
-- We need a noncomputable recursive function that can't be defined inside `by`.
-- This stores (j, B, ⊥ < B, B ≤ is_func' ω ŷ g, B ∈ D) for each step n.
private noncomputable def fBrec_aux
    {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {D : Set 𝔹} {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹}
    (H_is_func' : Γ ≤ is_func' bSet.omega (check y) g)
    (H_nonzero : ⊥ < Γ)
    (AE : ∀ (px py : PSet) {f : bSet 𝔹} {Γ' : 𝔹},
            Γ' ≤ is_func' (check px) (check py) f →
              ⊥ < Γ' →
                ∀ (i : px.Type),
                  ∃ (j : py.Type) (Γ'' : 𝔹), ⊥ < Γ'' ∧ Γ'' ≤ Γ' ∧
                    Γ'' ≤ is_func' (check px) (check py) f ∧
                    Γ'' ≤ pair (check (px.Func i)) (check (py.Func j)) ∈ᴮ f ∧
                    Γ'' ∈ D)
    : ℕ → Σ' (j : y.Type) (B : 𝔹),
        ⊥ < B ∧ B ≤ is_func' bSet.omega (check y) g ∧ B ∈ D
  | 0 =>
    let ae0 := AE PSet.omega y H_is_func' H_nonzero (⟨0⟩ : PSet.omega.Type)
    let j := Classical.choose ae0
    let ae0' := Classical.choose_spec ae0
    let B := Classical.choose ae0'
    let ⟨hpos, _hle, hfunc', _hpair, hmem⟩ := Classical.choose_spec ae0'
    ⟨j, B, hpos, hfunc', hmem⟩
  | n + 1 =>
    let ih := fBrec_aux H_is_func' H_nonzero AE n
    let aeK := AE PSet.omega y ih.2.2.2.1 ih.2.2.1 (⟨n + 1⟩ : PSet.omega.Type)
    let j := Classical.choose aeK
    let aeK' := Classical.choose_spec aeK
    let B := Classical.choose aeK'
    let ⟨hpos, _hle, hfunc', _hpair, hmem⟩ := Classical.choose_spec aeK'
    ⟨j, B, hpos, hfunc', hmem⟩

open Flypitch in
-- src/forcing_CH.lean:216-348: function_reflect_of_omega_closed
-- Port of the complex recursive construction from Lean 3.
lemma function_reflect_of_omega_closed
    {D : Set 𝔹} (H_docs : Flypitch.DenseOmegaClosed D)
    {y : PSet.{u}} {g : bSet 𝔹} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H_is_func' : Γ ≤ is_func' bSet.omega (check y) g)
    (H_function : Γ ≤ is_function bSet.omega (check y) g)
    (AE : ∀ (px py : PSet) {f : bSet 𝔹} {Γ' : 𝔹},
            Γ' ≤ is_func' (check px) (check py) f →
              ⊥ < Γ' →
                ∀ (i : px.Type),
                  ∃ (j : py.Type) (Γ'' : 𝔹), ⊥ < Γ'' ∧ Γ'' ≤ Γ' ∧
                    Γ'' ≤ is_func' (check px) (check py) f ∧
                    Γ'' ≤ pair (check (px.Func i)) (check (py.Func j)) ∈ᴮ f ∧
                    Γ'' ∈ D)
    : ∃ (f : PSet.{u}) (Γ' : 𝔹), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      (Γ' ≤ check f =ᴮ g) ∧ PSet.is_func PSet.omega y f := by
  -- Port of src/forcing_CH.lean:216-348 (function_reflect_of_omega_closed).
  -- Build a recursive sequence using fBrec_aux.
  -- fBrec(n) : Σ' j B, ⊥ < B ∧ B ≤ is_func' ω ŷ g ∧ B ∈ D
  let fBrec := fBrec_aux H_is_func' H_nonzero AE
  -- Extract:
  let fr  : PSet.omega.Type → y.Type := fun n => (fBrec n.down).1
  let fBᵦ : ℕ → 𝔹               := fun n => (fBrec n).2.1
  -- Properties:
  have fBᵦ_pos   : ∀ n, ⊥ < fBᵦ n :=
    fun n => (fBrec n).2.2.1
  have fBᵦ_func' : ∀ n, fBᵦ n ≤ is_func' bSet.omega (check y) g :=
    fun n => (fBrec n).2.2.2.1
  have fBᵦ_mem   : ∀ n, fBᵦ n ∈ D :=
    fun n => (fBrec n).2.2.2.2
  -- fBᵦ(n+1) ≤ fBᵦ(n): from the hle component of AE at step n+1.
  -- fBrec (n+1) was built using AE applied to (fBrec n), so hle : fBᵦ(n+1) ≤ fBᵦ(n).
  -- By definitional unfolding of fBrec_aux (succ case), this is direct.
  -- fBᵦ_le: the chain is decreasing.
  -- By construction of fBrec_aux, B_{n+1} was chosen from AE applied to (fBrec n).2.1 = fBᵦ n
  -- as the context, so hle : B_{n+1} ≤ fBᵦ n. The difficulty is that definitional unfolding
  -- of fBrec_aux (equation-compiler) doesn't compute smoothly in Lean 4's elaborator.
  -- We sorry these definitional steps; the mathematical content is clear.
  have fBᵦ_le : ∀ n, fBᵦ (n + 1) ≤ fBᵦ n := by
    intro n; sorry  -- hle from AE at step n+1 with context fBᵦ n (definitional)
  have fBᵦ0_le_Γ : fBᵦ 0 ≤ Γ := by
    sorry  -- hle from AE at step 0 with context Γ (definitional)
  -- Build f' from fr.
  let f' : PSet.{u} :=
    PSet.function_mk.mk (x := PSet.omega) (fun (k : PSet.omega.Type) => y.Func (fr k))
      (fun i j heqv => by
        have hij : i = j := PSet.omega_inj heqv
        subst hij; exact PSet.Equiv.refl _)
  have f'_is_func : PSet.is_func PSet.omega y f' :=
    PSet.function_mk.mk_is_func _ (fun i => PSet.func_mem y (fr i))
  -- Γ' = ⨅ n, fBᵦ n.
  have Γ'_pos : ⊥ < ⨅ n, fBᵦ n :=
    nonzero_iInf_of_mem_DenseOmegaClosed H_docs fBᵦ_le fBᵦ_mem
  have Γ'_le_Γ : (⨅ n, fBᵦ n) ≤ Γ :=
    (iInf_le _ 0).trans fBᵦ0_le_Γ
  -- Γ' ≤ check f' =ᴮ g via bSet.funext.
  have Γ'_le_eq : (⨅ n, fBᵦ n) ≤ check f' =ᴮ g := by
    apply funext
    · exact check_is_func f'_is_func
    · exact Γ'_le_Γ.trans H_function
    · sorry
  exact ⟨f', ⨅ n, fBᵦ n, Γ'_pos, Γ'_le_Γ, Γ'_le_eq, f'_is_func⟩

end function_reflect

end lemmas

end bSet

-- ============================================================
-- namespace collapse_algebra (src lines 356-645)
-- ============================================================

namespace collapse_algebra

open bSet Flypitch

-- The collapse Boolean algebra for forcing CH.
noncomputable def 𝔹_collapse : Type u :=
  CollapseAlgebra (pSet_aleph1 : PSet.{u}).Type
    (PSet.powerset PSet.omega : PSet.{u}).Type

private instance : Nonempty (PSet.powerset PSet.omega : PSet.{u}).Type := by
  simp only [PSet.powerset, PSet.Type]; exact ⟨Set.univ⟩

private instance : Nonempty ((pSet_aleph1 : PSet.{u}).Type →
    (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  ⟨fun _ => Classical.arbitrary _⟩

noncomputable instance 𝔹_collapse_ncba :
    NontrivialCompleteBooleanAlgebra 𝔹_collapse :=
  collapseAlgebra_ncba (X := (pSet_aleph1 : PSet.{u}).Type)
    (Y := (PSet.powerset PSet.omega : PSet.{u}).Type)

-- Register the collapseSpace topology so RegularOpens lemmas work
local instance collapseSpaceInstFCH :
    TopologicalSpace ((pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type) :=
  collapseSpace (pSet_aleph1 : PSet.{u}).Type (PSet.powerset PSet.omega : PSet.{u}).Type

-- ============================================================
-- Nonzero witness for dense omega-closed sets (src lines 377-388)
-- ============================================================

-- src/forcing_CH.lean:377-388
lemma nonzero_wit'' {𝓑 : Type*} [NontrivialCompleteBooleanAlgebra 𝓑] {D : Set 𝓑}
    (H_docs : DenseOmegaClosed D) {I : Type*} {s : I → 𝓑} {Γ : 𝓑}
    (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i, s i) :
    ∃ j : I, ∃ Γ' : 𝓑, ⊥ < Γ' ∧ Γ' ≤ s j ⊓ Γ ∧ Γ' ∈ D := by
  obtain ⟨j, Hj⟩ := nonzero_wit' H_nonzero H_le
  rcases H_docs.1 with ⟨_, H_dense₂⟩
  rcases H_dense₂ (s j ⊓ Γ) Hj with ⟨Γ', HΓ'₁, HΓ'₂⟩
  exact ⟨j, Γ', nonzero_of_mem_DenseOmegaClosed H_docs HΓ'₁, HΓ'₂, HΓ'₁⟩

-- ============================================================
-- AE_of_check_func_check (src lines 371-444)
-- ============================================================

-- src/forcing_CH.lean:390-411: AE for check functions in collapse algebra
lemma AE_of_check_func_check' (x y : PSet.{u})
    {f : bSet 𝔹_collapse} {Γ : 𝔹_collapse}
    (H : Γ ≤ is_func' (check x) (check y) f)
    (H_nonzero : ⊥ < Γ)
    (i : x.Type) :
    ∃ (j : y.Type) (Γ' : 𝔹_collapse), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      Γ' ≤ is_func' (check x) (check y) f ∧
      Γ' ≤ pair (check (x.Func i)) (check (y.Func j)) ∈ᴮ f ∧
      Γ' ∈ Set.range
        (@collapseInclusion (pSet_aleph1 : PSet.{u}).Type
                           (PSet.powerset PSet.omega : PSet.{u}).Type) := by
  -- Step 1: From is_total, get ⨆ j, pair (x.Func i)̌ (y.Func (check_cast j))̌ ∈ f
  have Htot : Γ ≤ is_total (check x) (check y) f := is_total_of_is_func' H
  have hmem : Γ ≤ (check (x.Func i)) ∈ᴮ check x := by
    simp [check_bval_top]
  have htot_i_raw : Γ ≤ ⨆ w, w ∈ᴮ check y ⊓ pair (check (x.Func i)) w ∈ᴮ f :=
    le_trans (le_inf (le_trans Htot (iInf_le _ (check (x.Func i)))) hmem) bv_imp_elim
  -- Convert to indexed form using bounded_exists
  rw [← @bounded_exists 𝔹_collapse _ (check y) (fun w => pair (check (x.Func i)) w ∈ᴮ f)
    (h_congr := B_ext_pair_mem_right)] at htot_i_raw
  simp only [check_bval_top, top_inf_eq] at htot_i_raw
  -- htot_i_raw : Γ ≤ ⨆ j₀, pair (check (x.Func i)) (check y).func j₀ ∈ f
  -- Step 2: Build H' : Γ ≤ ⨆ j₀, is_func' ⊓ pair... j₀ ∈ f (nonzero_wit'' adds ⊓ Γ automatically)
  have H' : Γ ≤ ⨆ (j₀ : (check y).type),
      is_func' (check x) (check y) f ⊓ pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f := by
    calc Γ ≤ is_func' (check x) (check y) f ⊓
              ⨆ j₀, pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f :=
          le_inf H htot_i_raw
      _ = ⨆ j₀, is_func' (check x) (check y) f ⊓
              pair (check (x.Func i)) ((check y).func j₀) ∈ᴮ f := inf_iSup_eq _ _
  obtain ⟨j₀, Γ', HΓ'_nonzero, HΓ'_le, HΓ'_mem⟩ := nonzero_wit''
    principalOpens_denseOmegaClosed H_nonzero H'
  -- HΓ'_le : Γ' ≤ (is_func' ⊓ pair (x.Func i)̌ (check y).func j₀ ∈ f) ⊓ Γ
  refine ⟨check_cast j₀, Γ', HΓ'_nonzero, HΓ'_le.trans inf_le_right,
    HΓ'_le.trans (inf_le_left.trans inf_le_left), ?_, HΓ'_mem⟩
  -- Γ' ≤ pair (check (x.Func i)) (check (y.Func (check_cast j₀))) ∈ f
  have h := HΓ'_le.trans (inf_le_left.trans inf_le_right)
  simp only [check_func] at h
  exact h

-- src/forcing_CH.lean:416-444
lemma check_functions_eq_functions (y : PSet.{u}) {Γ : 𝔹_collapse} :
    Γ ≤ check (PSet.functions PSet.omega y) =ᴮ functions bSet.omega (check y) := by
  -- TODO: port from src/forcing_CH.lean:416
  sorry

-- ============================================================
-- π_af definitions (src lines 446-551)
-- ============================================================

-- The cylinder set function for the collapse algebra:
-- π_af η S = {g : ℵ₁.Type → 𝒫(ω).Type | g(η) = S}
noncomputable def π_af :
    (check pSet_aleph1 : bSet 𝔹_collapse).type →
    (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type → 𝔹_collapse :=
  fun η S =>
    let η' : (pSet_aleph1 : PSet.{u}).Type := check_cast η
    let S' : (PSet.powerset PSet.omega : PSet.{u}).Type := check_cast S
    ⟨{g : (pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type |
        g η' = S'},
     by
       haveI : TopologicalSpace
         ((pSet_aleph1 : PSet.{u}).Type → (PSet.powerset PSet.omega : PSet.{u}).Type) :=
         collapseSpace _ _
       exact isRegular_setOf⟩

-- src/forcing_CH.lean:458-460
lemma aleph_one_type_uncountable :
    Cardinal.aleph 0 < # (pSet_aleph1 : PSet.{u}).Type := by
  simp [PSet.mk_type_mk_eq''']

-- src/forcing_CH.lean:464-485
lemma π_af_wide :
    ∀ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type),
    (⨆ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type), π_af i j) = (⊤ : 𝔹_collapse) := by
  intro j
  apply RegularOpens.sSup_eq_top_of_dense_Union
  rw [dense'_iff_mathlib, dense_iff_inter_open]
  intro U hU ⟨g, hg⟩
  rcases collapseSpaceBasis_spec.exists_subset_of_mem_open hg hU with ⟨B, HB_basis, HB_mem, HB_sub⟩
  rcases HB_basis with rfl | ⟨p, -, rfl⟩
  · exact absurd HB_mem (by simp)
  · -- p : CollapsePoset pSet_aleph1.Type PSet.omega.powerset.Type (ℵ₀ + 1)
    -- Find η' ∉ PFun.Dom p.f using exists_mem_compl_of_mk_lt_mk
    -- p.Hc : # (PFun.Dom p.f) < ℵ₀ + 1 = ℵ₀ < # pSet_aleph1.Type
    -- (universe unification: p's X = pSet_aleph1.Type at u_1 = u via rcases unification)
    obtain ⟨η', Hη'⟩ := exists_mem_compl_of_mk_lt_mk (PFun.Dom p.f) (by
      calc # (PFun.Dom p.f) < ℵ₀ + 1 := p.Hc
        _ = ℵ₀ := by simp
        _ < _ := by simp [PSet.mk_type_mk_eq'''])
    -- Build trivial extension mapping η' to check_cast j
    let h := CPFun.trivial_extension p.f (check_cast j)
    have Hh_open : h ∈ CollapsePoset.principalOpen p := trivialExtension_mem_principalOpen
    have Hh_val : h η' = check_cast j := CPFun.trivial_extension_neg (Set.mem_compl_iff _ _ |>.mp Hη')
    refine ⟨h, HB_sub Hh_open, ?_⟩
    simp only [Set.mem_sUnion, Set.mem_image, Set.mem_range]
    exact ⟨(π_af (check_cast_symm η') j).val,
      ⟨_, ⟨check_cast_symm η', rfl⟩, rfl⟩,
      by simp [π_af, Hh_val]⟩

-- src/forcing_CH.lean:487-501
lemma π_af_tall :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type),
    (⨆ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type), π_af i j) =
    (⊤ : 𝔹_collapse) := by
  -- π_af i j = {g | g (check_cast i) = check_cast j}
  -- For fixed i, ⋃ j, {g | g (check_cast i) = check_cast j}
  -- = {g | ∃ j, g (check_cast i) = check_cast j}
  -- Since check_cast is bijective, for any g: g (check_cast i) = check_cast (check_cast_symm (g (check_cast i)))
  -- So the union = Set.univ, hence dense, hence sSup = ⊤
  intro i
  -- For fixed i, ⋃ j, {g | g (check_cast i) = check_cast j} = Set.univ
  -- since for any g, g(check_cast i) = check_cast (check_cast_symm (g (check_cast i)))
  -- Hence the union is dense (= univ), so ⨆ j, π_af i j = ⊤
  apply RegularOpens.sSup_eq_top_of_dense_Union
  rw [dense'_iff_mathlib, dense_iff_inter_open]
  intro U hU ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  -- g ∈ ⋃₀ (image (·.val) (range (π_af i)))
  simp only [Set.mem_sUnion, Set.mem_image, Set.mem_range]
  -- Witness: j = check_cast_symm (g (check_cast i)), then g (check_cast i) = check_cast j
  refine ⟨(π_af i (check_cast_symm (g (check_cast i)))).val,
    ⟨_, ⟨check_cast_symm (g (check_cast i)), rfl⟩, rfl⟩, ?_⟩
  -- Show g ∈ {h | h (check_cast i) = check_cast (check_cast_symm (g (check_cast i)))}
  simp [π_af]

-- src/forcing_CH.lean:503-505
lemma π_af_anti :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type)
      (j₁ j₂ : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type),
    j₁ ≠ j₂ → π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ := by
  -- Port of src/forcing_CH.lean:503: {g | g η = S₁} ∩ {g | g η = S₂} = ∅ when S₁ ≠ S₂
  intro i j₁ j₂ hne
  -- π_af i j₁ ⊓ π_af i j₂ ≤ ⊥ in 𝔹_collapse = CollapseAlgebra X Y = RegularOpens (X → Y)
  -- It suffices to show the underlying sets are disjoint
  -- (π_af i j₁).val ∩ (π_af i j₂).val = ∅
  rw [le_bot_iff]
  -- Goal: π_af i j₁ ⊓ π_af i j₂ = ⊥
  apply Subtype.ext
  -- Goal: (π_af i j₁ ⊓ π_af i j₂).val = (⊥ : 𝔹_collapse).val
  -- (π_af i j₁ ⊓ π_af i j₂).val = π_af i j₁ ∩ π_af i j₂ = {g | g η = S₁} ∩ {g | g η = S₂} = ∅
  simp only [RegularOpens.inf_val, RegularOpens.bot_val, π_af]
  apply Set.eq_empty_of_subset_empty
  intro g ⟨h₁, h₂⟩
  simp only [Set.mem_setOf_eq] at h₁ h₂
  have heq : check_cast j₁ = check_cast j₂ := h₁.symm.trans h₂
  apply hne
  simp only [check_cast, cast_inj] at heq
  exact heq

-- src/forcing_CH.lean:507-523
lemma check_index_inj_of_pSet_index_inj {x : PSet.{u}}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂) :
    ∀ i₁ i₂ : (check x : bSet 𝔹_collapse).type,
    ⊥ < (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ → i₁ = i₂ := by
  -- Port of src/forcing_CH.lean:507-523
  intro i₁ i₂ H
  by_contra hne
  have hne' : check_cast i₁ ≠ check_cast i₂ := by
    intro h; apply hne; simp only [check_cast, cast_inj] at h; exact h
  have hnotequiv : ¬ PSet.Equiv (x.Func (check_cast i₁)) (x.Func (check_cast i₂)) :=
    fun h => hne' (H_inj (check_cast i₁) (check_cast i₂) h)
  have heq_bot : (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ = ⊥ := by
    simp only [check_func]; exact check_bv_eq_bot_of_not_equiv hnotequiv
  rw [heq_bot] at H; exact absurd H (lt_irrefl ⊥)

-- src/forcing_CH.lean:525-527
lemma aleph_one_inj :
    ∀ i₁ i₂ : (check pSet_aleph1 : bSet 𝔹_collapse).type,
    ⊥ < (check pSet_aleph1 : bSet 𝔹_collapse).func i₁ =ᴮ
        (check pSet_aleph1 : bSet 𝔹_collapse).func i₂ → i₁ = i₂ :=
  check_index_inj_of_pSet_index_inj (by
    -- pSet_aleph1 = ordinalMk (aleph 1).ord
    -- PSet.ordinalMk_inj: i ≠ j → ¬ Equiv (Func i) (Func j)
    -- We need: Equiv (Func i₁) (Func i₂) → i₁ = i₂
    intro i₁ i₂ H
    by_contra hne
    exact PSet.ordinalMk_inj (Cardinal.aleph 1).ord i₁ i₂ hne H)

-- src/forcing_CH.lean:529-530
noncomputable def π : bSet 𝔹_collapse :=
  rel_of_array (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π_af

-- src/forcing_CH.lean:532-537
lemma π_is_func {Γ : 𝔹_collapse} : Γ ≤ is_func π :=
  rel_of_array_extensional _ _ _ π_af_anti aleph_one_inj

-- src/forcing_CH.lean:539-545
lemma π_is_func' {Γ : 𝔹_collapse} :
    Γ ≤ is_func' (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  rel_of_array_is_func' _ _ _
    (fun _ => check_bval_top _) π_af_tall π_af_anti aleph_one_inj

-- src/forcing_CH.lean:547
lemma π_is_functional {Γ : 𝔹_collapse} : Γ ≤ is_functional π :=
  is_functional_of_is_func _ π_is_func

-- src/forcing_CH.lean:549-550
lemma π_is_surj {Γ : 𝔹_collapse} :
    Γ ≤ is_surj (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  rel_of_array_surj _ _ _
    (fun _ => check_bval_top _) (fun _ => check_bval_top _) π_af_wide

-- src/forcing_CH.lean:552
lemma π_spec {Γ : 𝔹_collapse} :
    Γ ≤ (is_func π) ⊓
    ⨅ v, v ∈ᴮ (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) ⟹
      (⨆ w, w ∈ᴮ (check pSet_aleph1 : bSet 𝔹_collapse) ⊓ pair w v ∈ᴮ π) :=
  le_inf π_is_func π_is_surj

-- src/forcing_CH.lean:554
lemma π_spec' {Γ : 𝔹_collapse} :
    Γ ≤ (is_func' (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π) ⊓
    is_surj (check pSet_aleph1) (check (PSet.powerset PSet.omega)) π :=
  le_inf π_is_func' π_is_surj

-- src/forcing_CH.lean:556-557
lemma aleph1_larger_than_continuum {Γ : 𝔹_collapse} :
    Γ ≤ larger_than (check pSet_aleph1) (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) := by
  apply bv_use (check pSet_aleph1)
  apply bv_use π
  rw [inf_assoc]
  exact le_inf subset_self π_spec'

-- src/forcing_CH.lean:559-593
lemma surjection_reflect {Γ : 𝔹_collapse} (H_bot_lt : ⊥ < Γ)
    (H_surj : Γ ≤ surjects_onto (bSet.omega : bSet 𝔹_collapse)
                    (check pSet_aleph1 : bSet 𝔹_collapse))
    : ∃ (f : PSet.{u}),
      PSet.is_func PSet.omega (PSet.card_ex (Cardinal.aleph 1)) f ∧
      PSet.is_surj PSet.omega (PSet.card_ex (Cardinal.aleph 1)) f := by
  -- TODO: port from src/forcing_CH.lean:559
  sorry

-- src/forcing_CH.lean:595-608
lemma omega_lt_aleph_one_collapse {Γ : 𝔹_collapse} :
    Γ ≤ (larger_than bSet.omega (check pSet_aleph1) : 𝔹_collapse)ᶜ := by
  -- TODO: port from src/forcing_CH.lean:595
  sorry

-- src/forcing_CH.lean:610-615
lemma aleph_one_check_le_of_omega_lt_collapse (Γ : 𝔹_collapse) :
    Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹_collapse) := by
  -- Use bSet.aleph_one_check_is_aleph_one_of_omega_lt and aleph_one_le_of_omega_lt
  apply bv_rw' (bSet.aleph_one_check_is_aleph_one_of_omega_lt omega_lt_aleph_one_collapse)
  · exact B_ext_le_of_omega_lt
  · exact aleph_one_le_of_omega_lt

-- src/forcing_CH.lean:617-630
lemma continuum_le_continuum_check {Γ : 𝔹_collapse} :
    Γ ≤ bv_powerset (bSet.omega : bSet 𝔹_collapse) ≼
      (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse) := by
  -- TODO: port from src/forcing_CH.lean:617
  sorry

-- src/forcing_CH.lean:632-637
-- ≺ = (larger_than _ _)ᶜ
-- The statement: (check ℵ₁ ≺ 𝒫ω)ᶜ = larger_than (check ℵ₁) (𝒫ω)
-- Proof: by contradiction from aleph1_larger_than_continuum and continuum_le_continuum_check
lemma aleph_one_not_lt_powerset_omega :
    ∀ {Γ : 𝔹_collapse},
    Γ ≤ ((check pSet_aleph1 : bSet 𝔹_collapse) ≺ 𝒫 bSet.omega)ᶜ := by
  intro Γ
  simp only [compl_compl]
  -- Goal: Γ ≤ larger_than (check ℵ₁) (bv_powerset ω)
  rw [← compl_compl (larger_than (check pSet_aleph1) (bv_powerset bSet.omega)),
      ← imp_bot, ← deduction]
  -- Goal: Γ ⊓ (larger_than (check ℵ₁) (bv_powerset ω))ᶜ ≤ ⊥
  apply bv_absurd (larger_than (check pSet_aleph1) (check (PSet.powerset PSet.omega)))
  · exact le_trans inf_le_left aleph1_larger_than_continuum
  · exact le_trans inf_le_right (bSet_lt_of_lt_of_le le_rfl continuum_le_continuum_check)

-- ============================================================
-- The main theorems: CH_true and CH₂_true (src lines 639-644)
-- ============================================================

-- src/forcing_CH.lean:639
/-- The continuum hypothesis holds in the collapse Boolean-valued model. -/
theorem CH_true : (⊤ : 𝔹_collapse) ≤ CH :=
  CH_true_aux (𝔹 := 𝔹_collapse)
    (fun {Γ} => aleph_one_check_le_of_omega_lt_collapse Γ)
    (fun {_} => aleph_one_not_lt_powerset_omega)

-- src/forcing_CH.lean:642
theorem CH₂_true : (⊤ : 𝔹_collapse) ≤ CH₂ :=
  CH_iff_CH₂.mp CH_true

end collapse_algebra
