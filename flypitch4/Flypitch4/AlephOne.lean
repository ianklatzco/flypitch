/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
-- Lean 4 port of src/aleph_one.lean lines 1-450 — Task 19a (part 1 of 2)

import Flypitch4.BvmExtras2

open scoped Flypitch
open Lattice

universe u v

-- ============================================================
-- src/aleph_one.lean:5-241: namespace PSet
-- ============================================================

namespace PSet

section
open Cardinal

-- src/aleph_one.lean:10
/-- Foundation / regularity for pSet: every nonempty set has an ∈-minimal element. -/
lemma regularity (x : PSet.{u}) (H_nonempty : ¬ Equiv x (∅ : PSet.{u})) :
    ∃ (y : PSet) (_Hy : y ∈ x), ∀ z ∈ x, z ∉ y := by
  obtain ⟨y, Hy, Hmin⟩ := well_founded x H_nonempty
  exact ⟨y, Hy, Hmin⟩

-- src/aleph_one.lean:18
noncomputable def aleph_one : PSet := card_ex (Cardinal.aleph 1)

-- src/aleph_one.lean:20
lemma aleph_one_Ord : Ord aleph_one := Ord_mk (Cardinal.aleph 1).ord

-- src/aleph_one.lean:22
def aleph_one_weak_Ord_spec (x : PSet.{u}) : Prop :=
  Ord x ∧ (∀ y : PSet.{u}, Ord y ∧ ¬ injects_into y PSet.omega → x ⊆ y)

-- src/aleph_one.lean:25
def epsilon_trichotomy (x : PSet.{u}) : Prop :=
  ∀ (y : PSet), y ∈ x → ∀ (z : PSet), z ∈ x → Equiv y z ∨ y ∈ z ∨ z ∈ y

-- src/aleph_one.lean:27
lemma epsilon_trichotomy_of_Ord {x : PSet.{u}} (H_ord : Ord x) : epsilon_trichotomy x :=
  H_ord.left.left

-- src/aleph_one.lean:30
lemma epsilon_trichotomy_of_Ord' {x : PSet.{u}} (H_ord : Ord x) :
    ∀ {y} (_Hy : y ∈ x) {z} (_Hz : z ∈ x), Equiv y z ∨ y ∈ z ∨ z ∈ y := by
  intro y Hy z Hz
  exact epsilon_trichotomy_of_Ord H_ord y Hy z Hz

-- src/aleph_one.lean:33
lemma is_transitive_of_mem_Ord {x : PSet.{u}} (H_ord : Ord x) : is_transitive x := H_ord.right

-- src/aleph_one.lean:35
lemma mem_of_mem_subset' {x y z : PSet.{u}} (H_sub : y ⊆ z) (H_mem : x ∈ y) : x ∈ z :=
  (subset_iff_all_mem.mp H_sub) x H_mem

-- src/aleph_one.lean:38
lemma mem_of_mem_Ord' {x y z : PSet.{u}} (H_ord : Ord z) (H_mem₁ : x ∈ y) (H_mem₂ : y ∈ z) :
    x ∈ z :=
  mem_of_mem_subset' (is_transitive_of_mem_Ord H_ord y H_mem₂) H_mem₁

-- src/aleph_one.lean:44
lemma subset_of_mem_Ord' {x z : PSet.{u}} (H_ord : Ord z) (H_mem₁ : x ∈ z) : x ⊆ z :=
  is_transitive_of_mem_Ord H_ord x H_mem₁

-- src/aleph_one.lean:47
lemma Ord_of_mem_Ord' {x z : PSet.{u}} (H_mem : x ∈ z) (H : Ord z) : Ord x := by
  sorry -- TODO: port from src/aleph_one.lean:47

-- src/aleph_one.lean:56
/-- Complement: elements of x not in y -/
def pSet_compl (x y : PSet.{u}) : PSet.{u} := PSet.sep (fun z => z ∉ y) x

-- src/aleph_one.lean:58
lemma mem_pSet_compl_iff {x y z : PSet.{u}} : z ∈ pSet_compl x y ↔ z ∈ x ∧ z ∉ y :=
  mem_sep_iff (P_ext_neg P_ext_mem_left)

-- src/aleph_one.lean:61
@[reducible] def non_empty (x : PSet.{u}) : Prop := ¬ (Equiv x (∅ : PSet.{u}))

-- src/aleph_one.lean:63
lemma equiv_unfold' {x y : PSet.{u}} :
    Equiv x y ↔ (∀ z, z ∈ x → z ∈ y) ∧ (∀ z, z ∈ y → z ∈ x) := by
  rw [ext_iff]
  exact ⟨fun h => ⟨fun z hz => (h z).mp hz, fun z hz => (h z).mpr hz⟩,
         fun ⟨h₁, h₂⟩ z => ⟨h₁ z, h₂ z⟩⟩

-- src/aleph_one.lean:66
lemma nonempty_iff_exists_mem {x : PSet.{u}} : non_empty x ↔ ∃ y, y ∈ x := by
  constructor
  · exact exists_mem_of_nonempty
  · intro ⟨y, Hy⟩ H_eq
    exact PSet.notMem_empty y ((ext_iff.mp H_eq y).mp Hy)

-- src/aleph_one.lean:73
lemma nonempty_compl_of_ne {x y : PSet.{u}} (H_ne : ¬ Equiv x y) :
    (non_empty $ pSet_compl x y) ∨ (non_empty $ pSet_compl y x) := by
  simp only [non_empty, nonempty_iff_exists_mem, mem_pSet_compl_iff]
  rw [equiv_unfold', not_and_or] at H_ne
  rcases H_ne with H_ne | H_ne
  · push_neg at H_ne
    obtain ⟨z, Hz₁, Hz₂⟩ := H_ne
    exact Or.inl ⟨z, Hz₁, Hz₂⟩
  · push_neg at H_ne
    obtain ⟨z, Hz₁, Hz₂⟩ := H_ne
    exact Or.inr ⟨z, Hz₁, Hz₂⟩

-- src/aleph_one.lean:80
lemma compl_empty_of_subset {x y : PSet.{u}} (H_sub : x ⊆ y) :
    Equiv (pSet_compl x y) (∅ : PSet.{u}) := by
  classical
  by_contra H_contra
  change non_empty _ at H_contra
  obtain ⟨z, Hz⟩ := nonempty_iff_exists_mem.mp H_contra
  rw [mem_pSet_compl_iff] at Hz
  exact Hz.2 (mem_of_mem_subset' H_sub Hz.1)

-- src/aleph_one.lean:89
/-- Binary intersection -/
def pSet_binary_inter (x y : PSet.{u}) : PSet.{u} := PSet.sep (fun z => z ∈ y) x

-- src/aleph_one.lean:91
lemma mem_pSet_binary_inter_iff {x y z : PSet.{u}} :
    z ∈ pSet_binary_inter x y ↔ (z ∈ x ∧ z ∈ y) :=
  mem_sep_iff P_ext_mem_left

-- src/aleph_one.lean:94
lemma pSet_binary_inter_subset {x y : PSet.{u}} :
    pSet_binary_inter x y ⊆ x ∧ pSet_binary_inter x y ⊆ y := by
  refine ⟨?_, ?_⟩
  · rw [subset_iff_all_mem]; intro z Hz; exact (mem_pSet_binary_inter_iff.mp Hz).1
  · rw [subset_iff_all_mem]; intro z Hz; exact (mem_pSet_binary_inter_iff.mp Hz).2

-- src/aleph_one.lean:97
lemma Ord_pSet_binary_inter {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) :
    Ord (pSet_binary_inter x y) := by
  sorry -- TODO: port from src/aleph_one.lean:97

-- src/aleph_one.lean:109
lemma Ord.lt_of_ne_and_le {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y)
    (H_ne : ¬ (Equiv x y)) (H_le : x ⊆ y) : x ∈ y := by
  sorry -- TODO: port from src/aleph_one.lean:109 (complex epsilon argument)

-- src/aleph_one.lean:137
lemma Ord.le_or_le {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) : x ⊆ y ∨ y ⊆ x := by
  sorry -- TODO: port from src/aleph_one.lean:137

-- src/aleph_one.lean:155
lemma pSet_equiv_comm {x y : PSet.{u}} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

-- src/aleph_one.lean:158
lemma Ord.trichotomy {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) :
    Equiv x y ∨ x ∈ y ∨ y ∈ x := by
  classical
  rcases Ord.le_or_le H₁ H₂ with h | h
  · by_cases H_eq : Equiv x y
    · exact Or.inl H_eq
    · exact Or.inr (Or.inl (Ord.lt_of_ne_and_le H₁ H₂ H_eq h))
  · by_cases H_eq : Equiv x y
    · exact Or.inl H_eq
    · exact Or.inr (Or.inr (Ord.lt_of_ne_and_le H₂ H₁ (fun h' => H_eq h'.symm) h))

-- src/aleph_one.lean:171
lemma Ord.lt_of_le_of_lt {x y z : PSet.{u}} (Hx : Ord x) (Hy : Ord y) (Hz : Ord z)
    (H_le : x ⊆ y) (H_lt : y ∈ z) : x ∈ z := by
  rcases Ord.trichotomy Hx Hy with h | h | h
  · -- Equiv x y, y ∈ z → x ∈ z
    exact (PSet.Mem.congr_left h).mpr H_lt
  · exact mem_trans_of_transitive h H_lt Hz.right
  · -- y ∈ x: y ∈ x and x ⊆ y → y ∈ y, contradiction
    exfalso; exact PSet.mem_irrefl y (mem_of_mem_subset' H_le h)

-- src/aleph_one.lean:182
lemma Ord.le_iff_lt_or_eq {x z : PSet.{u}} (H₁ : Ord x) (H₂ : Ord z) :
    x ⊆ z ↔ x ∈ z ∨ Equiv x z := by
  classical
  constructor
  · intro H
    by_cases H_eq : Equiv x z
    · exact Or.inr H_eq
    · exact Or.inl (Ord.lt_of_ne_and_le H₁ H₂ H_eq H)
  · intro h
    rcases h with h | h
    · exact is_transitive_of_mem_Ord H₂ x h
    · exact subset_iff_all_mem.mpr (fun z' hz' => (ext_iff.mp h z').mp hz')

-- src/aleph_one.lean:195
open Cardinal in
lemma mk_injects_into_of_mk_le_omega {η : Ordinal.{u}}
    (H_le : Cardinal.mk (ordinalMk η).Type ≤ Cardinal.mk (PSet.omega : PSet.{u}).Type) :
    injects_into (ordinalMk η) PSet.omega := by
  sorry -- TODO: port from src/aleph_one.lean:195 (function.mk construction)

-- src/aleph_one.lean:216
open Cardinal in
lemma injects_into_omega_of_mem_aleph_one {z : PSet} (H_mem : z ∈ aleph_one) :
    injects_into z PSet.omega := by
  obtain ⟨w, Hw_lt, Hz_eq⟩ := equiv_mk_of_mem_mk z H_mem
  suffices injects_into (ordinalMk w) PSet.omega from
    P_ext_injects_into_left (ordinalMk w) z Hz_eq.symm this
  apply mk_injects_into_of_mk_le_omega
  rw [ordinalMk_card, mk_omega_eq_mk_omega]
  have h1 : w.card < Cardinal.aleph 1 := Cardinal.lt_ord.mp Hw_lt
  rw [aleph_one_eq_succ_aleph_zero] at h1
  exact Order.lt_succ_iff.mp h1

-- src/aleph_one.lean:226
lemma aleph_one_satisfies_spec : aleph_one_weak_Ord_spec aleph_one := by
  refine ⟨aleph_one_Ord, ?_⟩
  rintro z ⟨Hz₁, Hz₂⟩
  rw [Ord.le_iff_lt_or_eq aleph_one_Ord Hz₁]
  rcases Ord.trichotomy aleph_one_Ord Hz₁ with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exfalso; exact Hz₂ (injects_into_omega_of_mem_aleph_one h)

end

end PSet

-- ============================================================
-- src/aleph_one.lean:242-450: namespace bSet
-- ============================================================

open Cardinal bSet
namespace bSet

-- ============================================================
-- src/aleph_one.lean:256-450: section well_ordering
-- ============================================================

section well_ordering

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:260
@[reducible] def is_rel (r x : bSet 𝔹) : 𝔹 := r ⊆ᴮ prod x x

-- src/aleph_one.lean:262
def is_wo (r x : bSet 𝔹) : 𝔹 :=
  is_rel r x ⊓
  ((⨅ y, pair y x ∈ᴮ r ⟹ (⨅ z, pair z x ∈ᴮ r ⟹ (y =ᴮ z ⊔ pair y z ∈ᴮ r ⊔ pair z y ∈ᴮ r))) ⊓
   (⨅ u, u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, pair y u ∈ᴮ r ⊓ (⨅ z', pair z' u ∈ᴮ r ⟹ (pair z' y ∈ᴮ r)ᶜ))))

-- src/aleph_one.lean:266
def mem_rel (x : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ᴮ x.func pr.2)

-- src/aleph_one.lean:268
lemma mem_mem_rel_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ pair y z ∈ᴮ mem_rel x ↔ (Γ ≤ y ∈ᴮ x ∧ Γ ≤ z ∈ᴮ x ∧ Γ ≤ y ∈ᴮ z) := by
  sorry -- TODO: port from src/aleph_one.lean:268 (uses bv_cases_at, bv_split_at, bv_cc)

-- src/aleph_one.lean:286
@[simp] lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) := by
  sorry -- TODO: port from src/aleph_one.lean:286 (uses bv_intro, bv_imp_intro, bv_cc)

-- src/aleph_one.lean:297
def prod_map (x y v w : bSet 𝔹) (f g : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun (pr : (prod (prod x v) (prod y w)).type) =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (v.func pr.1.2) (w.func pr.2.2) ∈ᴮ g)

-- src/aleph_one.lean:299
def prod_map_self (x y f : bSet 𝔹) : bSet 𝔹 :=
  prod_map x y x y f f

-- src/aleph_one.lean:302
lemma B_congr_prod_map_self_left_aux {y f x x' : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ x =ᴮ x') :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ prod_map_self x y f ⟹ z ∈ᴮ prod_map_self x' y f := by
  sorry -- TODO: port from src/aleph_one.lean:302 (uses bv_cases_at etc.)

-- src/aleph_one.lean:329
@[simp] lemma B_congr_prod_map_self_left {y f : bSet 𝔹} :
    B_congr (fun x : bSet 𝔹 => prod_map_self x y f) := by
  intro x x' Γ H_eq
  apply mem_ext
  · apply B_congr_prod_map_self_left_aux; exact H_eq
  · apply B_congr_prod_map_self_left_aux; exact bv_symm H_eq

-- src/aleph_one.lean:336
lemma mem_prod_map_self_iff {x y f a₁ a₂ b₁ b₂ : bSet 𝔹} {Γ : 𝔹}
    (_H_func : Γ ≤ is_function x y f) :
    Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod_map_self x y f ↔
    Γ ≤ a₁ ∈ᴮ x ∧ Γ ≤ a₂ ∈ᴮ x ∧ Γ ≤ b₁ ∈ᴮ y ∧ Γ ≤ b₂ ∈ᴮ y ∧
    Γ ≤ pair a₁ b₁ ∈ᴮ f ∧ Γ ≤ pair a₂ b₂ ∈ᴮ f := by
  sorry -- TODO: port from src/aleph_one.lean:336 (uses bv_cases_at, bv_split_at, bv_cc)

-- src/aleph_one.lean:379
def induced_epsilon_rel (η : bSet 𝔹) (x : bSet 𝔹) (f : bSet 𝔹) : bSet 𝔹 :=
  image (mem_rel η) (prod x x) (prod_map_self η x f)

-- src/aleph_one.lean:382
lemma eq_pair_of_mem_induced_epsilon_rel {η x f pr : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pr ∈ᴮ induced_epsilon_rel η x f) :
    ∃ a b : bSet 𝔹, Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ x ∧ Γ ≤ pr =ᴮ pair a b ∧
    Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f := by
  have hmem : Γ ≤ pr ∈ᴮ prod x x :=
    mem_of_mem_subset subset.mk_subset H_mem
  obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hmem
  exact ⟨v, w, Hv, Hw, H_eq,
    bv_rw' (bv_symm H_eq) (ϕ := fun z => z ∈ᴮ induced_epsilon_rel η x f)
      (h_congr := B_ext_mem_left) (H_new := H_mem)⟩

-- src/aleph_one.lean:391
lemma mem_induced_epsilon_rel_iff {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f) :
    Γ ≤ pair a b ∈ᴮ (induced_epsilon_rel η x f) ↔
    (Γ ≤ a ∈ᴮ x) ∧ (Γ ≤ b ∈ᴮ x) ∧
    (Γ ≤ ⨆ a', a' ∈ᴮ η ⊓ ⨆ b', b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b')) := by
  sorry -- TODO: port from src/aleph_one.lean:391 (uses bv_cases_at etc.)

-- src/aleph_one.lean:425
lemma mem_induced_epsilon_rel_of_mem {η x f a b : bSet 𝔹} {Γ}
    (H_mem₁ : Γ ≤ a ∈ᴮ η) (H_mem₂ : Γ ≤ b ∈ᴮ η) (H_mem : Γ ≤ a ∈ᴮ b)
    (H_func : Γ ≤ is_function η x f) :
    Γ ≤ pair (function_eval H_func a H_mem₁) (function_eval H_func b H_mem₂) ∈ᴮ
      induced_epsilon_rel η x f := by
  rw [mem_induced_epsilon_rel_iff H_func]
  refine ⟨function_eval_mem_codomain, function_eval_mem_codomain, ?_⟩
  apply bv_use a; refine le_inf H_mem₁ ?_
  apply bv_use b; refine le_inf H_mem₂ ?_
  exact le_inf (le_inf function_eval_pair_mem function_eval_pair_mem) H_mem

-- src/aleph_one.lean:437
lemma mem_of_mem_induced_epsilon_rel {η x f a' b' a b : bSet 𝔹} {Γ}
    (H_inj : Γ ≤ is_injective_function η x f)
    (H_mem₁ : Γ ≤ pair a' a ∈ᴮ f) (H_mem₂ : Γ ≤ pair b' b ∈ᴮ f)
    (H_mem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a' ∈ᴮ b' := by
  rw [mem_induced_epsilon_rel_iff (bv_and_left H_inj)] at H_mem
  obtain ⟨_Ha_mem, _Hb_mem, _H⟩ := H_mem
  sorry -- TODO: port from src/aleph_one.lean:437 (iSup unwrapping, bv_cc)

end well_ordering

end bSet
