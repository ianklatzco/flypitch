/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/forcing.lean (567 lines) — Task 18 -/

import Flypitch4.BvmExtras
import Flypitch4.CantorSpace
import Mathlib.SetTheory.Cardinal.Pigeonhole

open scoped Cardinal
open Flypitch Flypitch.Regular

universe u

namespace bSet

-- ============================================================
-- src/forcing.lean:34-103: section cardinal_preservation
-- ============================================================

section cardinal_preservation

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/forcing.lean:36-48
lemma AE_of_check_larger_than_check'' {x y : PSet.{u}} (f : bSet 𝔹) {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ is_surj_onto (check x) (check y) f)
    (H_nonempty : ∃ z, z ∈ y) :
    ∀ i : y.Type, ∃ j : x.Type, ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  intro i
  -- is_surj_onto = is_func' ⊓ is_surj
  have H_func' : Γ ≤ is_func' (check x) (check y) f := le_trans H inf_le_left
  have H_surj : Γ ≤ is_surj (check x) (check y) f := le_trans H inf_le_right
  -- Apply is_surj at v = check (y.Func i): since check (y.Func i) ∈ check y by mem_check_of_mem
  -- get ⨆ w, w ∈ check x ⊓ pair w (check (y.Func i)) ∈ f
  have H_surj_i : Γ ≤ ⨆ w, w ∈ᴮ check x ⊓ pair w (check (y.Func i)) ∈ᴮ f := by
    have h_step := le_trans H_surj (iInf_le (f := fun v => v ∈ᴮ check y ⟹
        ⨆ w, w ∈ᴮ check x ⊓ pair w v ∈ᴮ f) (check (y.Func i)))
    exact le_trans (le_inf h_step mem_check_of_mem) (imp_inf_le _ _)
  -- Use bounded_exists to rewrite ⨆ w, w ∈ check x ⊓ ϕ w = ⨆ j, ϕ (check (x.Func j))
  rw [← @bounded_exists 𝔹 _ (check x) (fun w => pair w (check (y.Func i)) ∈ᴮ f)
    (h_congr := B_ext_pair_mem_left)] at H_surj_i
  simp only [check_bval_top, top_inf_eq] at H_surj_i
  -- H_surj_i : Γ ≤ ⨆ j : x.Type, pair (check (x.Func (check_cast j))) (check (y.Func i)) ∈ᴮ f
  -- Combine with H_func' to get ⨆ j, is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ f
  have H_combined : ⊥ < ⨆ j : (check x : bSet 𝔹).type,
      is_func f ⊓ pair ((check x : bSet 𝔹).func j) (check (y.Func i)) ∈ᴮ f := by
    apply lt_of_lt_of_le H_nonzero
    calc Γ
        ≤ is_func' (check x) (check y) f ⊓ ⨆ j, pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          le_inf H_func' H_surj_i
      _ = ⨆ j, is_func' (check x) (check y) f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          inf_iSup_eq'
      _ ≤ ⨆ j, is_func f ⊓ pair ((check x).func j) (check (y.Func i)) ∈ᴮ f :=
          iSup_mono fun j => le_inf (is_func_of_is_func' inf_le_left) inf_le_right
  obtain ⟨j, Hj⟩ := nonzero_wit H_combined
  exact ⟨check_cast j, by rwa [← check_func]⟩

-- src/forcing.lean:50-56
lemma AE_of_check_larger_than_check' {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ surjects_onto (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f := by
  -- surjects_onto (check x) (check y) = ⨆ f, is_func' (check x) (check y) f ⊓ is_surj ...
  -- Use maximum_principle to extract a specific f
  -- From surjects_onto, extract a concrete f using maximum_principle
  -- surjects_onto (check x) (check y) = ⨆ f, is_surj_onto (check x) (check y) f
  -- By maximum_principle, ∃ f, ⨆ g, is_surj_onto ... g = is_surj_onto ... f
  -- But B_ext proof for is_surj_onto f is needed; use is_function_right + simp
  -- B_ext (fun f => is_surj_onto (check x) (check y) f)
  -- = B_ext (fun f => is_func' x y f ⊓ is_surj x y f)
  -- = B_ext (fun f => (is_func f ⊓ is_total x y f) ⊓ is_surj x y f)
  -- Extract f from surjects_onto = ⨆ f, is_surj_onto (check x) (check y) f
  simp only [surjects_onto] at H
  obtain ⟨f, Hf⟩ := nonzero_wit' H_nonzero H
  -- Hf : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ
  -- Use the context Γ' = is_surj_onto f ⊓ Γ which is nonzero and ≤ is_surj_onto f
  have Hf_nonzero : ⊥ < is_surj_onto (check x) (check y) f ⊓ Γ := Hf
  have Hf_le : is_surj_onto (check x) (check y) f ⊓ Γ ≤ is_surj_onto (check x) (check y) f :=
    inf_le_left
  exact ⟨f, AE_of_check_larger_than_check'' f Hf_nonzero Hf_le H_mem⟩

-- src/forcing.lean:58-62
lemma AE_of_check_larger_than_check {x y : PSet.{u}} {Γ : 𝔹}
    (H_nonzero : ⊥ < Γ)
    (H : Γ ≤ larger_than (check x) (check y))
    (H_mem : ∃ z, z ∈ y) :
    ∃ f : bSet 𝔹, ∀ i : y.Type, ∃ j : x.Type,
      ⊥ < is_func f ⊓ pair (check (x.Func j)) (check (y.Func i)) ∈ᴮ f :=
  AE_of_check_larger_than_check' H_nonzero
    (surjects_onto_of_larger_than_and_exists_mem H
      (by obtain ⟨z, hz⟩ := H_mem; exact le_trans le_top (le_iSup_of_le (check z) (check_mem hz))))
    H_mem

-- src/forcing.lean:63-100: not_CCC_of_uncountable_fiber
variable
  (η₁ η₂ : PSet.{u}) (H_infinite : Cardinal.aleph0 ≤ #(η₁.Type))
  (H_lt : #(η₁.Type) < #(η₂.Type))
  (H_inj₂ : ∀ x y, x ≠ y → ¬ PSet.Equiv (η₂.Func x) (η₂.Func y))
  (f : bSet 𝔹) (g : η₂.Type → η₁.Type)
  (H : ∀ β : η₂.Type, (⊥ : 𝔹) < is_func f ⊓ pair (check (η₁.Func (g β))) (check (η₂.Func β)) ∈ᴮ f)

include H_infinite H_lt H_inj₂ f H in
-- src/forcing.lean:71-100
lemma not_CCC_of_uncountable_fiber
    (H_ex : ∃ ξ : η₁.Type, Cardinal.aleph0 < #↥(g⁻¹' {ξ})) : ¬ CCC 𝔹 := by
  obtain ⟨ξ, H_ξ⟩ := H_ex
  let 𝓐 : (g⁻¹' {ξ}) → 𝔹 :=
    fun β => is_func f ⊓ pair (check (η₁.Func (g β.val))) (check (η₂.Func β.val)) ∈ᴮ f
  have 𝓐_nontriv : ∀ β, ⊥ < 𝓐 β := fun β => H β.val
  have 𝓐_anti : ∀ β₁ β₂ : (g⁻¹' {ξ}), β₁ ≠ β₂ → 𝓐 β₁ ⊓ 𝓐 β₂ ≤ ⊥ := by
    intro β₁ β₂ h_sep
    apply poset_yoneda; intro Γ a
    simp only [le_inf_iff] at a
    obtain ⟨ha₁, ha₂⟩ := a
    obtain ⟨H_func₁, H_mem₁⟩ := le_inf_iff.mp ha₁
    obtain ⟨_, H_mem₂⟩ := le_inf_iff.mp ha₂
    have hg₁ : g β₁.val = ξ := β₁.property
    have hg₂ : g β₂.val = ξ := β₂.property
    rw [hg₁] at H_mem₁; rw [hg₂] at H_mem₂
    have H_le_eq : Γ ≤ check (η₂.Func β₁.val) =ᴮ check (η₂.Func β₂.val) :=
      eq_of_is_func_of_eq H_func₁ bv_refl H_mem₁ H_mem₂
    apply le_trans H_le_eq
    rw [le_bot_iff]
    exact check_bv_eq_bot_of_not_equiv (H_inj₂ _ _ (fun heq => h_sep (Subtype.ext heq)))
  intro H_CCC
  exact absurd (le_antisymm (lt_iff_le_and_ne.mp H_ξ).1
    (H_CCC _ 𝓐 𝓐_nontriv 𝓐_anti)) (lt_iff_le_and_ne.mp H_ξ).2

end cardinal_preservation

end bSet

open bSet

-- ============================================================
-- src/forcing.lean:107-121: namespace PSet
-- ============================================================

namespace PSet

-- src/forcing.lean:109: ℵ₁ (as PSet)
@[reducible] noncomputable def pSet_aleph1 : PSet.{0} := ordinalMk (Cardinal.aleph 1).ord

-- src/forcing.lean:111: ℵ₂ (as PSet)
@[reducible] noncomputable def pSet_aleph2 : PSet.{0} := ordinalMk (Cardinal.aleph 2).ord

-- src/forcing.lean:113
lemma pSet_aleph2_unfold : pSet_aleph2 = ⟨pSet_aleph2.Type, pSet_aleph2.Func⟩ := by
  cases pSet_aleph2; rfl

-- src/forcing.lean:115-120: Union lemmas (not needed for the main result)

end PSet

open PSet

-- ============================================================
-- src/forcing.lean:125-133: 𝔹_cohen and instances
-- ============================================================

/-- The Cohen boolean algebra: regular opens on Set(PSet.pSet_aleph2.Type × ℕ) -/
noncomputable def 𝔹_cohen : Type :=
  @Flypitch.RegularOpens (Set (PSet.pSet_aleph2.Type × ℕ)) inferInstance

local notation "𝔹" => 𝔹_cohen

instance H_nonempty : Nonempty (Set (PSet.pSet_aleph2.Type × ℕ)) := ⟨∅⟩

noncomputable instance 𝔹_boolean_algebra :
    NontrivialCompleteBooleanAlgebra 𝔹 :=
  @Flypitch.RegularOpens.instNontrivialCBA _ _ H_nonempty

-- src/forcing.lean:134
lemma le_iff_subset' {x y : 𝔹} : x ≤ y ↔ x.val ⊆ y.val :=
  Flypitch.RegularOpens.le_iff_subset

-- src/forcing.lean:136
lemma bot_eq_empty : (⊥ : 𝔹) = ⟨∅, isRegularOpen_empty⟩ := by
  apply Flypitch.RegularOpens.ext; rfl

-- Type equality lemmas for cast operations
-- These hold because check x has .type = x.Type by the definition of check
private lemma eq₀ : (check (PSet.pSet_aleph2) : bSet 𝔹).type = PSet.pSet_aleph2.Type :=
  check_type'

private lemma eq₁ :
    ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg (· × ℕ) eq₀

private lemma eq₂ :
    Set ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Set (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Set eq₁

private lemma eq₃ :
    Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) = Finset (PSet.pSet_aleph2.Type × ℕ) :=
  congr_arg Finset eq₁

-- src/forcing.lean:149-176: cast helper lemmas
universe w in
lemma pi₂_cast₁ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    HEq p.1 q.1 := by
  subst H'; exact heq_of_eq (congr_arg Prod.fst (eq_of_heq H))

universe w in
lemma pi₂_cast₂ {α β γ : Type w} (H' : α = β) {p : α × γ} {q : β × γ} (H : HEq p q) :
    p.2 = q.2 := by
  subst H'; exact congr_arg Prod.snd (eq_of_heq H)

universe w in
lemma compl_cast₂ {α β : Type w} {a : Set α} {b : Set β} (H' : α = β) (H : HEq aᶜ b) :
    HEq a bᶜ := by
  subst H'; exact heq_of_eq ((eq_of_heq H) ▸ (compl_compl a).symm)

lemma eq₁_cast (p : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ) :
    cast eq₁ p = (cast eq₀ p.1, p.2) := by
  -- p : (check pSet_aleph2).type × ℕ =: α × ℕ, cast eq₁ p : pSet_aleph2.Type × ℕ
  have hcast : HEq p (cast eq₁ p) := (cast_heq eq₁ p).symm
  apply Prod.ext
  · -- need (cast eq₁ p).1 = cast eq₀ p.1
    -- pi₂_cast₁ eq₀ hcast : HEq p.1 (cast eq₁ p).1
    -- cast_heq eq₀ p.1 : HEq (cast eq₀ p.1) p.1
    apply eq_of_heq
    exact (pi₂_cast₁ eq₀ hcast).symm.trans (cast_heq eq₀ p.1).symm
  · exact (pi₂_cast₂ eq₀ hcast).symm

lemma eq₁_cast' (p : PSet.pSet_aleph2.Type × ℕ) :
    cast eq₁.symm p = (cast eq₀.symm p.1, p.2) := by
  have hcast : HEq p (cast eq₁.symm p) := (cast_heq eq₁.symm p).symm
  apply Prod.ext
  · apply eq_of_heq
    exact (pi₂_cast₁ eq₀.symm hcast).symm.trans (cast_heq eq₀.symm p.1).symm
  · exact (pi₂_cast₂ eq₀.symm hcast).symm

-- src/forcing.lean:178-179
theorem 𝔹_CCC : CCC 𝔹 :=
  Flypitch.RegularOpens.CCC_regular_opens CantorSpace.countable_chain_condition_set

local notation "𝒳" => Set (PSet.pSet_aleph2.Type × ℕ)

-- src/forcing.lean:187-191
/-- The principal regular open associated to a pair (ν, n) -/
noncomputable def principal_open (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n : ℕ) : 𝔹 :=
  ⟨CantorSpace.principalOpen (cast eq₁ (ν, n)),
   isRegularOpen_of_isClopen CantorSpace.isClopen_principalOpen⟩

lemma is_clopen_principal_open {ν n} : IsClopen (principal_open ν n).val :=
  CantorSpace.isClopen_principalOpen

-- src/forcing.lean:202-203
lemma perp_eq_compl_of_clopen {β : Type*} [TopologicalSpace β] {S : Set β}
    (H : IsClopen S) : Sᵖ = Sᶜ := by
  unfold Flypitch.perp; rw [IsClosed.closure_eq H.1]

-- src/forcing.lean:205-209
lemma mem_neg_principal_open_of_not_mem {ν n S} :
    (cast eq₁ (ν, n) ∈ Sᶜ) → S ∈ ((principal_open ν n)ᶜ).val := by
  intro H
  -- (principal_open ν n)ᶜ in 𝔹 = RegularOpens has val = perp of (principal_open ν n).val
  -- Since principal_open is clopen, perp = complement
  -- (principal_open ν n)ᶜ in 𝔹 has val = perp of (principal_open ν n).val (by RegularOpens.compl_val)
  -- and perp = compl since principal_open is clopen
  have hval : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᶜ := by
    have h1 : ((principal_open ν n)ᶜ : 𝔹).val = (principal_open ν n).valᵖ :=
      Flypitch.RegularOpens.compl_val (principal_open ν n)
    rw [h1, perp_eq_compl_of_clopen is_clopen_principal_open]
  rw [hval]
  -- Goal: S ∈ (principal_open ν n).valᶜ  i.e. S ∉ (principal_open ν n).val
  -- (principal_open ν n).val = CantorSpace.principalOpen (cast eq₁ (ν,n)) = {S | cast eq₁ (ν,n) ∈ S}
  simp only [Set.mem_compl_iff, principal_open, CantorSpace.principalOpen, Set.mem_setOf_eq]
  exact H

-- src/forcing.lean:211-214: structure 𝒞
structure 𝒞 : Type where
  ins : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  out : Finset ((check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ)
  H : ins ∩ out = ∅

-- src/forcing.lean:216
@[reducible] def π₂ : (check (PSet.pSet_aleph2) : bSet 𝔹).type × ℕ → ℕ := fun x => x.2

-- src/forcing.lean:223-245: ι definition
private noncomputable def ι : 𝒞 → 𝔹 :=
  fun p => ⟨{S | (p.ins.toSet) ⊆ (cast eq₂.symm S) ∧
                  (p.out.toSet) ⊆ (cast eq₂.symm Sᶜ)},
    isRegularOpen_of_isClopen (by sorry)⟩  -- TODO: port clopen proof

open CantorSpace

-- src/forcing.lean:249-250
universe w₁ in
lemma prop_decidable_cast_lemma {α β : Type w₁} (H : α = β) {a b : α} {a' b' : β}
    (H_a : HEq a a') (H_b : HEq b b') :
    HEq (Classical.propDecidable (a = b)) (Classical.propDecidable (a' = b')) := by
  subst H; cases H_a; cases H_b; rfl

-- src/forcing.lean:252-272: 𝒞_dense_basis
lemma 𝒞_dense_basis : ∀ T ∈ @standardBasis (PSet.pSet_aleph2.Type × ℕ), ∀ _h : T ≠ ∅,
    ∃ p : 𝒞, (ι p).val ⊆ T := by
  sorry -- TODO: port from src/forcing.lean:252

-- src/forcing.lean:274-284: 𝒞_dense
lemma 𝒞_dense {b : 𝔹} (H : ⊥ < b) : ∃ p : 𝒞, ι p ≤ b := by
  have hne : b.val ≠ ∅ := by
    intro heq
    exact H.ne (Flypitch.RegularOpens.ext (Flypitch.RegularOpens.bot_val.trans heq.symm))
  obtain ⟨S_wit, H_wit⟩ := Set.nonempty_iff_ne_empty.mpr hne
  change ∃ p, (ι p).val ⊆ b.val
  rcases (is_topological_basis_standardBasis.exists_subset_of_mem_open H_wit
      (isOpen_of_isRegularOpen b.property))
    with ⟨v, Hv₁, Hv₂, Hv₃⟩
  obtain ⟨p, H_p⟩ := 𝒞_dense_basis v Hv₁ (fun hv => by rw [hv] at Hv₂; exact Hv₂)
  exact ⟨p, Set.Subset.trans H_p Hv₃⟩

-- src/forcing.lean:286-288
lemma to_set_inter {α : Type*} {p₁ p₂ : Finset α} :
    (p₁ ∩ p₂).toSet = p₁.toSet ∩ p₂.toSet := by
  ext; simp [Finset.mem_coe, Finset.mem_inter]

-- src/forcing.lean:292-299
lemma not_mem_of_inter_empty_left {α : Type*} {p₁ p₂ : Finset α}
    (H : p₁ ∩ p₂ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet := by
  intro H' H''
  have : a ∈ p₁.toSet ∩ p₂.toSet := ⟨H', H''⟩
  rw [← to_set_inter] at this
  rw [congr_arg Finset.toSet H] at this
  exact absurd this (by simp [Finset.toSet])

-- src/forcing.lean:301-303
lemma not_mem_of_inter_empty_right {α : Type*} {p₁ p₂ : Finset α}
    (H : p₂ ∩ p₁ = ∅) {a : α} : a ∈ p₁.toSet → ¬ a ∈ p₂.toSet := by
  rw [Finset.inter_comm] at H; exact not_mem_of_inter_empty_left H

-- src/forcing.lean:305-319: 𝒞_nonzero
lemma 𝒞_nonzero (p : 𝒞) : ⊥ ≠ ι p := by
  sorry -- TODO: port from src/forcing.lean:305

-- src/forcing.lean:323-350: 𝒞_disjoint_row
lemma 𝒞_disjoint_row (p : 𝒞) : ∃ n : ℕ, ∀ ξ : PSet.pSet_aleph2.Type,
    (cast eq₁.symm (ξ, n)) ∉ p.ins ∧ (cast eq₁.symm (ξ, n)) ∉ p.out := by
  sorry -- TODO: port from src/forcing.lean:323

-- src/forcing.lean:352-353
lemma 𝒞_anti {p₁ p₂ : 𝒞} : p₁.ins ⊆ p₂.ins → p₁.out ⊆ p₂.out → ι p₂ ≤ ι p₁ := by
  intro H₁ H₂
  intro S hS
  obtain ⟨hS₁, hS₂⟩ := hS
  exact ⟨fun x hx => hS₁ (H₁ hx), fun x hx => hS₂ (H₂ hx)⟩

-- ============================================================
-- src/forcing.lean:355-441: namespace cohen_real (inside namespace bSet)
-- ============================================================

namespace bSet

namespace cohen_real

/-- `cohen_real.χ ν` is the indicator function on ℕ -/
noncomputable def χ (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : ℕ → 𝔹 :=
  fun n => principal_open ν n

/-- `cohen_real.mk ν` is the subset of (ω : bSet 𝔹) -/
noncomputable def mk (ν : (check (PSet.pSet_aleph2) : bSet 𝔹).type) : bSet 𝔹 :=
  @set_of_indicator 𝔹 _ omega (fun n => χ ν n.down)

@[simp] lemma mk_type {ν} : (mk ν).type = ULift ℕ := rfl

@[simp] lemma mk_func {ν} {n} : (mk ν).func n = of_nat (n.down) := rfl

@[simp] lemma mk_bval {ν} {n} : (mk ν).bval n = (χ ν) (n.down) := rfl

/-- bSet 𝔹 believes that each `mk ν` is a subset of omega -/
lemma definite {ν} {Γ} : Γ ≤ mk ν ⊆ᴮ omega := by
  rw [subset_unfold]
  apply le_iInf; intro i
  rw [← deduction]
  simp only [mk_bval, mk_func]
  -- Goal: χ ν i.down ⊓ Γ ≤ of_nat i.down ∈ᴮ omega
  exact le_trans inf_le_left (le_trans le_top omega_definite)

/-- bSet 𝔹 believes that each `mk ν` is an element of 𝒫(ω) -/
lemma definite' {ν} {Γ} : Γ ≤ mk ν ∈ᴮ bv_powerset omega := bv_powerset_spec.mp definite

-- src/forcing.lean:379-386
lemma sep {n} {Γ} {ν₁ ν₂} (H₁ : Γ ≤ of_nat n ∈ᴮ mk ν₁)
    (H₂ : Γ ≤ (of_nat n ∈ᴮ mk ν₂)ᶜ) :
    Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ := by
  -- Show: (mk ν₁ =ᴮ mk ν₂) ⊓ Γ ≤ ⊥, which is equivalent
  -- Use le_neg_of_inf_eq_bot: to show Γ ≤ (mk ν₁ =ᴮ mk ν₂)ᶜ, show (mk ν₁ =ᴮ mk ν₂) ⊓ Γ = ⊥
  apply le_neg_of_inf_eq_bot
  rw [le_antisymm_iff]; constructor
  · -- (mk ν₁ =ᴮ mk ν₂) ⊓ Γ ≤ ⊥
    apply le_bot_iff.mpr
    -- Use subst_congr_mem_right: mk ν₁ =ᴮ mk ν₂ ⊓ of_nat n ∈ᴮ mk ν₁ ≤ of_nat n ∈ᴮ mk ν₂
    rw [eq_bot_iff]
    have hmem : mk ν₁ =ᴮ mk ν₂ ⊓ Γ ≤ of_nat n ∈ᴮ mk ν₂ :=
      le_trans (le_inf inf_le_left (le_trans inf_le_right H₁)) subst_congr_mem_right
    exact le_trans (le_inf hmem (le_trans inf_le_right H₂)) inf_compl_eq_bot.le
  · exact bot_le

-- src/forcing.lean:388-398
lemma not_mem_of_not_mem {p : 𝒞} {ν} {n} (H : (ν, n) ∈ p.out) :
    ι p ≤ (of_nat n ∈ᴮ mk ν)ᶜ := by
  rw [mem_unfold, compl_iSup]
  apply le_iInf; intro k
  rw [compl_inf]
  by_cases hk : n = k.down
  · subst hk
    simp only [mk_bval, mk_func]
    rw [bv_eq_refl, compl_top, sup_bot_eq]
    intro S hS
    apply mem_neg_principal_open_of_not_mem
    have hS₂ := hS.2 (Finset.mem_coe.mpr H)
    have key : ∀ {T1 T2 : Type} (h : T1 = T2) (T : Set T2) (x : T1),
        x ∈ cast (congr_arg Set h).symm T ↔ cast h x ∈ T := by
      intro T1 T2 h; subst h; intro T x; simp
    exact (key eq₁ Sᶜ (ν, k.down)).mp hS₂
  · have : of_nat n =ᴮ (of_nat k.down : bSet 𝔹) = ⊥ := of_nat_inj' hk
    simp only [mk_bval, mk_func, this, compl_bot, sup_top_eq]; exact le_top

-- src/forcing.lean:400-406
private lemma inj_cast_lemma (ν' : (check (PSet.pSet_aleph2) : bSet 𝔹).type) (n' : ℕ) :
    cast eq₁.symm (cast eq₀ ν', n') = (ν', n') := by
  rw [eq₁_cast']; simp [cast_cast]

/-- Whenever ν₁ ≠ ν₂ < ℵ₂, bSet 𝔹 believes that `mk ν₁` and `mk ν₂` are distinct -/
lemma inj {ν₁ ν₂} (H_neq : ν₁ ≠ ν₂) : mk ν₁ =ᴮ mk ν₂ ≤ (⊥ : 𝔹) := by
  sorry -- TODO: port from src/forcing.lean:409

end cohen_real

-- ============================================================
-- src/forcing.lean:443-567: section neg_CH
-- ============================================================

section neg_CH
-- (still inside namespace bSet)

local notation "ℵ₀" => (omega : bSet 𝔹)
local notation "𝔠" => (bv_powerset ℵ₀ : bSet 𝔹)

-- src/forcing.lean:450-457
lemma uncountable_fiber_of_regular' (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂) (α : Type u) (H_α : #α = κ₁)
    (β : Type u) (H_β : #β = κ₂) (g : β → α) :
    ∃ (ξ : α), Cardinal.aleph0 < #↥(g⁻¹' {ξ}) := by
  -- Use Cardinal.infinite_pigeonhole: if ℵ₀ ≤ #β and #α < (#β).ord.cof, then some fiber has #β
  have h₁ : Cardinal.aleph0 ≤ #β := H_β ▸ le_of_lt (lt_of_le_of_lt H_inf H_lt)
  have h₂ : #α < (#β).ord.cof := by
    rw [H_α, H_β, H]; exact H_lt
  obtain ⟨ξ, Hξ⟩ := Cardinal.infinite_pigeonhole g h₁ h₂
  -- Hξ : #(g⁻¹'{ξ}) = #β, and ℵ₀ ≤ #β = κ₂ > κ₁ ≥ ℵ₀
  refine ⟨ξ, ?_⟩
  rw [Hξ, H_β]
  exact lt_of_le_of_lt H_inf H_lt

-- src/forcing.lean:459-466
lemma uncountable_fiber_of_regular (κ₁ κ₂ : Cardinal) (H_inf : Cardinal.aleph0 ≤ κ₁)
    (H_lt : κ₁ < κ₂) (H : κ₂.ord.cof = κ₂)
    (g : (PSet.card_ex κ₂).Type → (PSet.card_ex κ₁).Type) :
    ∃ (ξ : (PSet.card_ex κ₁).Type), Cardinal.aleph0 < #↥((fun β => g β)⁻¹' {ξ}) :=
  uncountable_fiber_of_regular' κ₁ κ₂ H_inf H_lt H _
    (PSet.mk_type_mk_eq κ₁ H_inf) _ (PSet.mk_type_mk_eq κ₂ (le_of_lt (lt_of_le_of_lt H_inf H_lt))) g

-- src/forcing.lean:468-487
lemma cardinal_inequality_of_regular (κ₁ κ₂ : Cardinal)
    (H_reg₁ : Cardinal.IsRegular κ₁) (H_reg₂ : Cardinal.IsRegular κ₂)
    (H_inf : Cardinal.aleph0 ≤ κ₁) (H_lt : κ₁ < κ₂) {Γ : 𝔹} :
    Γ ≤ (larger_than (check (PSet.card_ex κ₁)) (check (PSet.card_ex κ₂)))ᶜ := by
  sorry -- TODO: port from src/forcing.lean:468

-- src/forcing.lean:489-504
lemma aleph0_lt_aleph1_bSet : (⊤ : 𝔹) ≤
    (larger_than omega (check (PSet.card_ex (Cardinal.aleph 1))))ᶜ := by
  sorry -- TODO: port from src/forcing.lean:489

-- src/forcing.lean:507-509
lemma aleph1_lt_aleph2_bSet : (⊤ : 𝔹) ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  cardinal_inequality_of_regular _ _ PSet.is_regular_aleph_one PSet.is_regular_aleph_two
    (Cardinal.aleph0_le_aleph 1) PSet.aleph_one_lt_aleph_two

lemma aleph1_lt_aleph2_bSet' {Γ : 𝔹} : Γ ≤
    (larger_than (check (PSet.card_ex (Cardinal.aleph 1)))
                 (check (PSet.card_ex (Cardinal.aleph 2))))ᶜ :=
  le_trans le_top aleph1_lt_aleph2_bSet

-- src/forcing.lean:513-529: cohen_real.mk_ext
lemma cohen_real.mk_ext : ∀ (i j : (check (PSet.pSet_aleph2) : bSet 𝔹).type),
    (check (PSet.pSet_aleph2) : bSet 𝔹).func i =ᴮ (check (PSet.pSet_aleph2) : bSet 𝔹).func j ≤
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) i =ᴮ
      (fun x : (check (PSet.pSet_aleph2) : bSet 𝔹).type => cohen_real.mk x) j := by
  intro i j; by_cases h : i = j
  · simp [h]
  · apply poset_yoneda; intro Γ a
    rw [check_func, check_func] at a
    suffices h_bot : (check (PSet.pSet_aleph2.Func (check_cast i)) : bSet 𝔹) =ᴮ
        check (PSet.pSet_aleph2.Func (check_cast j)) ≤ ⊥ by
      exact le_trans a (le_trans h_bot bot_le)
    rw [le_bot_iff]
    apply check_bv_eq_bot_of_not_equiv
    -- pSet_aleph2 = ordinalMk (aleph 2).ord
    -- pSet_aleph2.Func (check_cast i) ≠ pSet_aleph2.Func (check_cast j) when i ≠ j
    apply PSet.ordinalMk_inj (Cardinal.aleph 2).ord
    intro H; exact h (by simp [check_cast] at H ⊢; exact H)

-- src/forcing.lean:531-532
noncomputable def neg_CH_func : bSet 𝔹 :=
  @functionMk _ _ (check PSet.pSet_aleph2) (fun x => cohen_real.mk x) cohen_real.mk_ext

-- src/forcing.lean:534-546
theorem aleph2_le_powerset_omega :
    ⊤ ≤ is_func' (check PSet.pSet_aleph2) 𝔠 neg_CH_func ⊓ is_inj neg_CH_func := by
  sorry -- TODO: port from src/forcing.lean:534

-- src/forcing.lean:548-550
lemma aleph1_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 1)) : bSet 𝔹) :=
  Ord_card_ex _

lemma aleph2_Ord {Γ : 𝔹} : Γ ≤ Ord (check (PSet.card_ex (Cardinal.aleph 2)) : bSet 𝔹) :=
  Ord_card_ex _

-- src/forcing.lean:552-562
theorem neg_CH : (⊤ : 𝔹) ≤ CHᶜ := by
  simp only [CH, compl_compl]
  exact le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 1)))
    (le_inf aleph1_Ord (le_iSup_of_le (check (PSet.card_ex (Cardinal.aleph 2)))
      (le_inf (le_inf aleph0_lt_aleph1_bSet aleph1_lt_aleph2_bSet)
        (le_iSup_of_le neg_CH_func aleph2_le_powerset_omega))))

-- src/forcing.lean:564-565
theorem neg_CH₂ : (⊤ : 𝔹) ≤ CH₂ᶜ :=
  (Lattice.bv_iff_neg CH_iff_CH₂).mp neg_CH

end neg_CH

end bSet
