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
  -- TODO: port from src/forcing_CH.lean:55
  sorry

-- src/forcing_CH.lean:64-77
theorem CH_true_aux
    (H_aleph_one : ∀ {Γ : 𝔹}, Γ ≤ le_of_omega_lt (check pSet_aleph1 : bSet 𝔹))
    (H_not_lt    : ∀ {Γ : 𝔹}, Γ ≤ ((check pSet_aleph1 : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ)
    : ∀ {Γ : 𝔹}, Γ ≤ CH := by
  intro Γ
  -- TODO: port from src/forcing_CH.lean:64
  sorry

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
  -- TODO: port from src/forcing_CH.lean:104
  sorry

-- src/forcing_CH.lean:115-124
lemma mem_right_of_mem_rel_of_array {x y w₁ w₂ : bSet 𝔹} {af : x.type → y.type → 𝔹}
    {Γ} (H_mem_right : Γ ≤ pair w₁ w₂ ∈ᴮ rel_of_array x y af)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    : Γ ≤ w₂ ∈ᴮ y := by
  -- TODO: port from src/forcing_CH.lean:115
  sorry

-- src/forcing_CH.lean:128-169
lemma rel_of_array_extensional (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ (is_func (rel_of_array x y af)) := by
  -- TODO: port from src/forcing_CH.lean:128
  sorry

-- src/forcing_CH.lean:171-191
lemma rel_of_array_is_func' (x y : bSet 𝔹) (af : x.type → y.type → 𝔹)
    (H_bval₂ : ∀ i, y.bval i = ⊤)
    (H_tall : ∀ i, (⨆ j, af i j) = ⊤)
    (H_anti : ∀ i, (∀ j₁ j₂, j₁ ≠ j₂ → af i j₁ ⊓ af i j₂ ≤ ⊥))
    (H_inj  : ∀ i₁ i₂, ⊥ < (x.func i₁) =ᴮ (x.func i₂) → i₁ = i₂)
    {Γ}
    : Γ ≤ is_func' x y (rel_of_array x y af) := by
  -- TODO: port from src/forcing_CH.lean:171
  sorry

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
  -- TODO: port from src/forcing_CH.lean:334
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
  simp [PSet.mk_type_mk_eq''', PSet.omega_lt_aleph_one]

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
  -- TODO: port from src/forcing_CH.lean:503
  sorry

-- src/forcing_CH.lean:507-523
lemma check_index_inj_of_pSet_index_inj {x : PSet.{u}}
    (H_inj : ∀ i₁ i₂ : x.Type, PSet.Equiv (x.Func i₁) (x.Func i₂) → i₁ = i₂) :
    ∀ i₁ i₂ : (check x : bSet 𝔹_collapse).type,
    ⊥ < (check x : bSet 𝔹_collapse).func i₁ =ᴮ (check x : bSet 𝔹_collapse).func i₂ → i₁ = i₂ := by
  -- TODO: port from src/forcing_CH.lean:507
  sorry

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
-- The statement: Γ ≤ -(ℵ₁̌ ≺ 𝒫(ω)) means Γ ≤ ((larger_than ℵ₁ (𝒫ω))ᶜ)ᶜ = Γ ≤ larger_than ℵ₁ (𝒫ω)
-- Wait - ≺ = (larger_than x y)ᶜ, so -(ℵ₁ ≺ 𝒫ω) = -((larger_than ℵ₁ 𝒫ω)ᶜ) = (larger_than ℵ₁ 𝒫ω)ᶜᶜ
-- In boolean algebra, aᶜᶜ = a, so -(ℵ₁ ≺ 𝒫ω) = larger_than ℵ₁ 𝒫ω
-- But the goal is Γ ≤ (ℵ₁ ≺ 𝒫ω)ᶜ = (larger_than ℵ₁ 𝒫ω)ᶜᶜ = larger_than ℵ₁ 𝒫ω? No.
-- Let me re-read: H_not_lt says Γ ≤ ((check ℵ₁ : bSet 𝔹) ≺ 𝒫 bSet.omega)ᶜ
-- ≺ = λ x y, (larger_than x y)ᶜ
-- So (check ℵ₁ ≺ 𝒫ω)ᶜ = ((larger_than ℵ₁ 𝒫ω)ᶜ)ᶜ = larger_than ℵ₁ 𝒫ω (since aᶜᶜ = a)
-- So H_not_lt is: Γ ≤ larger_than (check ℵ₁) 𝒫ω
-- That seems backwards from what we want (¬ ℵ₁ < 𝒫ω means ℵ₁ ≥ 𝒫ω)

-- In the original Lean 3 code: H_not_lt says Γ ≤ - ((ℵ₁)̌ ≺ 𝒫(ω))
-- where ≺ is λ x y, -(larger_than x y)
-- so (ℵ₁ ≺ 𝒫ω) = -(larger_than ℵ₁ 𝒫ω)
-- -(ℵ₁ ≺ 𝒫ω) = --(larger_than ℵ₁ 𝒫ω) = larger_than ℵ₁ 𝒫ω (in a boolean algebra)

-- So the Lean 3 H_not_lt says: Γ ≤ larger_than (ℵ₁) (𝒫ω)
-- But wait, that means ℵ₁ surjects onto 𝒫ω, which is what we have from aleph1_larger_than_continuum!
-- But the lemma name suggests this is "ℵ₁ does NOT strictly precede 𝒫ω"
-- This makes sense: ℵ₁ ≥ 𝒫ω (or more precisely, ℵ₁ surjects onto 𝒫ω) means ¬(ℵ₁ < 𝒫ω)

-- In Lean 4 with our ≺ = (larger_than _ _)ᶜ:
-- (check ℵ₁ ≺ 𝒫ω) = (larger_than check_ℵ₁ (𝒫ω))ᶜ
-- (check ℵ₁ ≺ 𝒫ω)ᶜ = (larger_than check_ℵ₁ (𝒫ω))ᶜᶜ = larger_than check_ℵ₁ (𝒫ω)
-- So the lemma says: Γ ≤ larger_than (check ℵ₁) (𝒫ω)
-- which is exactly aleph1_larger_than_continuum!

lemma aleph_one_not_lt_powerset_omega :
    ∀ {Γ : 𝔹_collapse},
    Γ ≤ ((check pSet_aleph1 : bSet 𝔹_collapse) ≺ 𝒫 bSet.omega)ᶜ := by
  -- ≺ = (larger_than _ _)ᶜ, so (x ≺ y)ᶜ = (larger_than x y)ᶜᶜ = larger_than x y
  -- i.e., ℵ₁ surjects onto 𝒫ω, which is aleph1_larger_than_continuum
  intro Γ
  -- TODO: port from src/forcing_CH.lean:632 (unfold ≺ and use aleph1_larger_than_continuum)
  sorry

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
