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
  -- TODO: port from src/forcing_CH.lean:82
  sorry

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

open Flypitch in
-- src/forcing_CH.lean:334: function_reflect_of_omega_closed
-- (The intermediate construction is sorry-stubbed; only the interface is kept)
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
  -- TODO: port from src/forcing_CH.lean:334 (complex recursive construction)
  sorry

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
  -- TODO: port from src/forcing_CH.lean:390
  sorry

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
  -- TODO: port from src/forcing_CH.lean:464
  sorry

-- src/forcing_CH.lean:487-501
lemma π_af_tall :
    ∀ (i : (check pSet_aleph1 : bSet 𝔹_collapse).type),
    (⨆ (j : (check (PSet.powerset PSet.omega) : bSet 𝔹_collapse).type), π_af i j) =
    (⊤ : 𝔹_collapse) := by
  -- TODO: port from src/forcing_CH.lean:487
  sorry

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
