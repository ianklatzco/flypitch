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
  refine ⟨⟨?_, is_epsilon_well_founded x⟩, transitive_of_mem_Ord x z H H_mem⟩
  intro y₁ Hy₁ y₂ Hy₂
  apply epsilon_trichotomy_of_Ord H
  · exact mem_of_mem_Ord' H Hy₁ H_mem
  · exact mem_of_mem_Ord' H Hy₂ H_mem

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
  refine ⟨⟨?_, is_epsilon_well_founded _⟩, ?_⟩
  · intro w Hw_mem z Hz_mem
    rw [mem_pSet_binary_inter_iff] at Hw_mem Hz_mem
    exact epsilon_trichotomy_of_Ord H₁ w Hw_mem.1 z Hz_mem.1
  · intro z H_mem
    rw [mem_pSet_binary_inter_iff] at H_mem
    rw [subset_iff_all_mem]; intro w Hw
    rw [mem_pSet_binary_inter_iff]
    exact ⟨mem_of_mem_Ord' H₁ Hw H_mem.1, mem_of_mem_Ord' H₂ Hw H_mem.2⟩

-- src/aleph_one.lean:109
lemma Ord.lt_of_ne_and_le {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y)
    (H_ne : ¬ (Equiv x y)) (H_le : x ⊆ y) : x ∈ y := by
  -- The complement y \ x is nonempty since x ≠ y but x ⊆ y
  have H_compl_nonempty : non_empty (pSet_compl y x) := by
    -- nonempty_compl_of_ne H_ne : non_empty (compl x y) ∨ non_empty (compl y x)
    rcases nonempty_compl_of_ne H_ne with h | h
    · -- non_empty (pSet_compl x y), i.e., x \ y is nonempty
      -- But x ⊆ y, so x \ y is empty → contradiction
      exfalso
      obtain ⟨z, hz⟩ := nonempty_iff_exists_mem.mp h
      rw [mem_pSet_compl_iff] at hz
      exact hz.2 (mem_of_mem_subset' H_le hz.1)
    · exact h
  -- Find an ∈-minimal element z of y \ x
  obtain ⟨z, Hz₁, Hz_min⟩ := regularity _ H_compl_nonempty
  obtain ⟨Hz_mem_y, Hz_not_mem_x⟩ := mem_pSet_compl_iff.mp Hz₁
  -- Show Equiv x z, then x ∈ z ∈ y implies x ∈ y? No: Equiv x z means x ∈ y since z ∈ y
  suffices H_eq : Equiv x z by exact (PSet.Mem.congr_left H_eq).mpr Hz_mem_y
  rw [ext_iff]
  intro a
  constructor
  · intro Ha_mem_x
    -- a ∈ x ⊆ y, z ∈ y: trichotomy of a and z as members of y
    rcases epsilon_trichotomy_of_Ord' H₂ (mem_of_mem_subset' H_le Ha_mem_x) Hz_mem_y with h | h | h
    · -- Equiv a z: but a ∈ x and z ∉ x, so a ∉ x, contradiction
      -- Equiv a z means: a ∈ x ↔ z ∈ x (by Mem.congr_left h)
      have : a ∈ x ↔ z ∈ x := ⟨fun H => (PSet.Mem.congr_left h).mp H,
                                  fun H => (PSet.Mem.congr_left h).mpr H⟩
      exact absurd (this.mp Ha_mem_x) Hz_not_mem_x
    · exact h
    · -- z ∈ a ∈ x, so z ∈ x by transitivity: contradiction
      exact absurd (mem_of_mem_Ord' H₁ h Ha_mem_x) Hz_not_mem_x
  · intro Ha_mem_z
    -- a ∈ z ∈ y, so a ∈ y. If a ∉ x, then a ∈ y \ x, but z is ∈-minimal there
    by_contra Ha_not_mem_x
    have Ha_mem_yx : a ∈ pSet_compl y x :=
      mem_pSet_compl_iff.mpr ⟨mem_of_mem_Ord' H₂ Ha_mem_z Hz_mem_y, Ha_not_mem_x⟩
    exact Hz_min a Ha_mem_yx Ha_mem_z

-- src/aleph_one.lean:137
lemma Ord.le_or_le {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) : x ⊆ y ∨ y ⊆ x := by
  let w := pSet_binary_inter x y
  have w_Ord : Ord w := Ord_pSet_binary_inter H₁ H₂
  have hw : Equiv w x ∨ Equiv w y := by
    classical
    by_contra H_contra
    push_neg at H_contra
    obtain ⟨H_ne₁, H_ne₂⟩ := H_contra
    -- w ∈ x and w ∈ y
    have Hwx : w ∈ x := Ord.lt_of_ne_and_le w_Ord H₁ H_ne₁ (pSet_binary_inter_subset.1)
    have Hwy : w ∈ y := Ord.lt_of_ne_and_le w_Ord H₂ H_ne₂ (pSet_binary_inter_subset.2)
    -- w ∈ w
    have Hww : w ∈ w := mem_pSet_binary_inter_iff.mpr ⟨Hwx, Hwy⟩
    exact PSet.mem_irrefl w Hww
  rcases hw with h | h
  · left
    exact subset_iff_all_mem.mpr (fun z hz =>
      (mem_pSet_binary_inter_iff.mp ((ext_iff.mp h.symm z).mp hz)).2)
  · right
    exact subset_iff_all_mem.mpr (fun z hz =>
      (mem_pSet_binary_inter_iff.mp ((ext_iff.mp h.symm z).mp hz)).1)

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
  obtain ⟨f, Hf⟩ := injection_of_mk_le H_le
  let ψ : (ordinalMk η).Type → PSet.{u} := fun i => PSet.omega.Func (f i)
  have H_ext : ∀ i j, Equiv ((ordinalMk η).Func i) ((ordinalMk η).Func j) → Equiv (ψ i) (ψ j) := by
    intro i j H_eqv
    by_cases hij : i = j
    · subst hij; exact Equiv.refl _
    · exfalso; exact ordinalMk_inj η i j hij H_eqv
  refine ⟨function_mk.mk ψ H_ext, ?_, ?_⟩
  · apply function_mk.mk_is_func
    intro i; exact PSet.func_mem PSet.omega (f i)
  · apply function_mk.mk_inj_of_inj
    intro i₁ i₂ H_eqv
    have h := omega_inj H_eqv
    have hi := Hf h
    subst hi; exact Equiv.refl _

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
  -- mem_rel x = subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ x.func pr.2)
  unfold mem_rel
  rw [mem_subset.mk_iff]
  simp only [prod_func, prod_bval]
  constructor
  · -- MP: Γ ≤ ⨆ (i,j), pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) → each conclusion
    intro H
    refine ⟨?_, ?_, ?_⟩
    · -- y ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y ∈ x
      have hyi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ y =ᴮ x.func i :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hbi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval i :=
        inf_le_right.trans (inf_le_right.trans inf_le_left)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ y =ᴮ x.func i ⊓ x.bval i := le_inf hyi hbi
        _ ≤ y ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le i
            exact le_inf inf_le_right inf_le_left
    · -- z ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      have hzj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ z =ᴮ x.func j :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hbj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval j :=
        inf_le_right.trans (inf_le_right.trans inf_le_right)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ z =ᴮ x.func j ⊓ x.bval j := le_inf hzj hbj
        _ ≤ z ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le j
            exact le_inf inf_le_right inf_le_left
    · -- y ∈ z
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y∈z
      set T := pair y z =ᴮ pair (x.func i) (x.func j) ⊓
        (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
      have hyi : T ≤ y =ᴮ x.func i := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hzj : T ≤ z =ᴮ x.func j := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hxixj : T ≤ x.func i ∈ᴮ x.func j := inf_le_right.trans inf_le_left
      -- y = xi, xi ∈ xj, xj = z  →  y ∈ z via mem_congr
      exact mem_congr (bv_symm hyi) (bv_symm hzj) hxixj
  · -- MPI: y∈x ∧ z∈x ∧ y∈z → ⨆ ij, ...
    intro ⟨Hy, Hz, Hyz⟩
    rw [mem_unfold] at Hy Hz
    -- Use iSup_inf_iSup to combine the two iSups, then bound elementwise
    apply le_trans (le_inf (le_inf Hy Hz) Hyz)
    -- goal: (⨆ i, bi⊓y=xi) ⊓ (⨆ j, bj⊓z=xj) ⊓ y∈z ≤ ⨆ (k,l), ...
    rw [show (⨆ i : x.type, x.bval i ⊓ y =ᴮ x.func i) ⊓
              (⨆ j : x.type, x.bval j ⊓ z =ᴮ x.func j) =
              ⨆ ij : x.type × x.type, (x.bval ij.1 ⊓ y =ᴮ x.func ij.1) ⊓
                (x.bval ij.2 ⊓ z =ᴮ x.func ij.2) from iSup_inf_iSup]
    rw [inf_comm]
    apply bv_cases_right; intro ⟨i, j⟩
    apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    -- After bv_cases_right intro ⟨i, j⟩ and rw [inf_comm], context is:
    -- y∈z ⊓ ((bi⊓y=xi) ⊓ (bj⊓z=xj)) ≤ pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj))
    -- Extract parts:
    have hbeq_y : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y =ᴮ x.func i := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hbeq_z : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        z =ᴮ x.func j := inf_le_right.trans (inf_le_right.trans inf_le_right)
    have hbval_i : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval i := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hbval_j : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval j := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hyz : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y ∈ᴮ z := inf_le_left
    refine le_inf (pair_eq_pair_iff.mpr ⟨hbeq_y, hbeq_z⟩)
      (le_inf (mem_congr hbeq_y hbeq_z hyz) (le_inf hbval_i hbval_j))

-- src/aleph_one.lean:286
@[simp] lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ H_eq
  -- Use prod_ext: both subsets of prod x x
  have H_sub_x : Γ ≤ mem_rel x ⊆ᴮ prod x x := subset.mk_subset
  have H_prod_eq : Γ ≤ prod x x =ᴮ prod y y := prod_congr H_eq H_eq
  have H_sub_y : Γ ≤ mem_rel y ⊆ᴮ prod x x :=
    poset_yoneda_inv Γ subst_congr_subset_right
      (le_inf subset.mk_subset (bv_symm H_prod_eq))
  apply prod_ext H_sub_x H_sub_y
  apply le_iInf; intro v; rw [← deduction]
  apply le_iInf; intro w; rw [← deduction]
  -- ctx: Γ ⊓ v ∈ x ⊓ w ∈ x
  apply le_inf
  · -- pair v w ∈ mem_rel x → pair v w ∈ mem_rel y  (forward direction)
    rw [← deduction]
    -- Goal: Γ ⊓ v ∈ x ⊓ w ∈ x ⊓ pair v w ∈ mem_rel x ≤ pair v w ∈ mem_rel y
    -- Abbreviate the context:
    apply (mem_mem_rel_iff (x := y) (y := v) (z := w)).mpr
    -- Need: ctx ≤ v ∈ y ∧ ctx ≤ w ∈ y ∧ ctx ≤ v ∈ w
    have ctx_le_x_eq_y : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x ≤ x =ᴮ y :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x)
      (x := x) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_x_eq_y hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_x_eq_y hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩
  · -- pair v w ∈ mem_rel y → pair v w ∈ mem_rel x  (backward direction)
    rw [← deduction]
    apply (mem_mem_rel_iff (x := x) (y := v) (z := w)).mpr
    have ctx_le_y_eq_x : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y ≤ y =ᴮ x :=
      bv_symm (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq)))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y)
      (x := y) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_y_eq_x hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_y_eq_x hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩

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
set_option maxHeartbeats 400000 in
lemma mem_prod_map_self_iff {x y f a₁ a₂ b₁ b₂ : bSet 𝔹} {Γ : 𝔹}
    (_H_func : Γ ≤ is_function x y f) :
    Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod_map_self x y f ↔
    Γ ≤ a₁ ∈ᴮ x ∧ Γ ≤ a₂ ∈ᴮ x ∧ Γ ≤ b₁ ∈ᴮ y ∧ Γ ≤ b₂ ∈ᴮ y ∧
    Γ ≤ pair a₁ b₁ ∈ᴮ f ∧ Γ ≤ pair a₂ b₂ ∈ᴮ f := by
  constructor
  · -- forward: prove each of the 6 conclusions from H
    intro H
    rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
      pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl] at H
    rw [mem_subset.mk_iff₂] at H
    -- H : Γ ≤ ⨆ pr, bval pr ⊓ (pair_eq pr ⊓ χ pr)
    -- For pr = ((i₁,i₂),(j₁,j₂)):
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
    --   pair_eq = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    --   χ = pair xi₁ yj₁ ∈ f ⊓ pair xi₂ yj₂ ∈ f
    -- Each of the 6 conclusions: Γ ≤ P, proved by le_trans H (iSup_le ...)
    -- Helper: extract component equalities from the body
    -- body : bval ⊓ (peq ⊓ χ)
    -- peq : inf_le_right.trans inf_le_left
    -- after two pair_eq_pair_iff.mp: a₁=xi₁, a₂=xi₂, b₁=yj₁, b₂=yj₂
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    -- bval ⊓ (peq ⊓ (χ₁ ⊓ χ₂)) where
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
    --   peq  = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    --   χ₁   = pair xi₁ yj₁ ∈ f,   χ₂ = pair xi₂ yj₂ ∈ f
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    -- bval ⊓ (peq ⊓ (χ₁ ⊓ χ₂)) where
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)  [inf_le_left]
    --   peq  = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)  [inf_le_right.trans inf_le_left]
    --   χ₁   = pair xi₁ yj₁ ∈ f  [inf_le_right.trans inf_le_right.trans inf_le_left]
    --   χ₂   = pair xi₂ yj₂ ∈ f  [inf_le_right.trans inf_le_right.trans inf_le_right]
    -- All are proved using this tactic:
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)  [inf_le_left]
    --   peq  = pair_eq                [inf_le_right.trans inf_le_left]
    --   χ₁   = pair xi₁ yj₁ ∈ f     [inf_le_right.trans inf_le_right.trans inf_le_left]
    --   χ₂   = pair xi₂ yj₂ ∈ f     [inf_le_right.trans inf_le_right.trans inf_le_right]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    -- body structure: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    -- Chains: peq=ir.il; from peq: pair a₁ a₂ =ᴮ pair xi₁ xi₂ via eq_of_eq_pair_left
    --         from that: a₁=xi₁ via eq_of_eq_pair_left, a₂=xi₂ via eq_of_eq_pair_right
    -- bval: xb1=il.il.il, xb2=il.il.ir, yb1=il.ir.il, yb2=il.ir.ir
    -- χ1=ir.ir.il, χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq extraction: ir.il; bval: xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir
    -- χ1=ir.ir.il; χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq: ir.il; xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir
    -- χ1=ir.ir.il; χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq=ir.il; xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir; χ1=ir.ir.il; χ2=ir.ir.ir
    -- Inline approach: avoid 'have' and use exact with full chains
    -- After simp, body = ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- Use apply-based approach: each step creates a concrete goal, avoiding bidirectional inference
    -- Helper for peq extraction (used repeatedly):
    -- After simp: body ≤ peq ≡ body ≤ pair(pair a₁ a₂)(pair b₁ b₂)=ᴮpair(pair xi₁ xi₂)(pair yj₁ yj₂)
    -- via inf_le_right.trans inf_le_left.
    · -- a₁ ∈ x
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_left.trans inf_le_left)).trans (mem_mk' x i₁))
      apply eq_of_eq_pair_left'; apply eq_of_eq_pair_left'
      exact inf_le_right.trans inf_le_left
    · -- a₂ ∈ x
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans (mem_mk' x i₂))
      apply eq_of_eq_pair_right'; apply eq_of_eq_pair_left'
      exact inf_le_right.trans inf_le_left
    · -- b₁ ∈ y
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ y) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans (mem_mk' y j₁))
      apply eq_of_eq_pair_left'; apply eq_of_eq_pair_right'
      exact inf_le_right.trans inf_le_left
    · -- b₂ ∈ y
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ y) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_right.trans inf_le_right)).trans (mem_mk' y j₂))
      apply eq_of_eq_pair_right'; apply eq_of_eq_pair_right'
      exact inf_le_right.trans inf_le_left
    · -- pair a₁ b₁ ∈ f: use bv_rw' to rewrite pair a₁ b₁ to pair xi₁ yj₁ (which ∈ f)
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ f) (h_congr := B_ext_mem_left)
        (H_new := inf_le_right.trans (inf_le_right.trans inf_le_left))
      apply pair_congr
      · apply eq_of_eq_pair_left'; apply eq_of_eq_pair_left'; exact inf_le_right.trans inf_le_left
      · apply eq_of_eq_pair_left'; apply eq_of_eq_pair_right'; exact inf_le_right.trans inf_le_left
    · -- pair a₂ b₂ ∈ f: same but using χ₂
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ f) (h_congr := B_ext_mem_left)
        (H_new := inf_le_right.trans (inf_le_right.trans inf_le_right))
      apply pair_congr
      · apply eq_of_eq_pair_right'; apply eq_of_eq_pair_left'; exact inf_le_right.trans inf_le_left
      · apply eq_of_eq_pair_right'; apply eq_of_eq_pair_right'; exact inf_le_right.trans inf_le_left
  · -- backward: construct the witness index from the 6 hypotheses
    intro ⟨Ha₁, Ha₂, Hb₁, Hb₂, Hpair₁, Hpair₂⟩
    rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
      pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl]
    rw [mem_subset.mk_iff₂]
    -- Need: Γ ≤ ⨆ pr, bval pr ⊓ (pair_eq pr ⊓ χ pr)
    -- Extract witnesses via mem_unfold and sequential bv_cases_left
    rw [mem_unfold] at Ha₁ Ha₂ Hb₁ Hb₂
    -- LHS0 = (((Ha₁ ⊓ Ha₂) ⊓ Hb₁) ⊓ Hb₂) ⊓ Γ
    apply le_trans (le_inf (le_inf (le_inf (le_inf Ha₁ Ha₂) Hb₁) Hb₂) le_rfl)
    -- Extract i₁ from Ha₁: inf_le_left^3 then inf_le_left
    apply le_trans (le_inf (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))) le_rfl)
    apply bv_cases_left; intro i₁
    -- ctx1 = (x.bval i₁ ⊓ a₁=xi₁) ⊓ LHS0
    -- Extract i₂ from Ha₂ in LHS0: inf_le_right then inf_le_left^3 then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro i₂
    -- ctx2 = (x.bval i₂ ⊓ a₂=xi₂) ⊓ ctx1
    -- Extract j₁ from Hb₁ in LHS0: inf_le_right^2 then inf_le_left^2 then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro j₁
    -- ctx3 = (y.bval j₁ ⊓ b₁=yj₁) ⊓ ctx2
    -- Extract j₂ from Hb₂ in LHS0: inf_le_right^3 then inf_le_left then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro j₂
    -- ctx4 = (y.bval j₂ ⊓ b₂=yj₂) ⊓ ctx3
    -- ctx4 components (left-to-right nesting):
    --   y.bval j₂: inf_le_left.trans inf_le_left
    --   b₂=yj₂:   inf_le_left.trans inf_le_right
    --   y.bval j₁: inf_le_right.trans (inf_le_left.trans inf_le_left)
    --   b₁=yj₁:   inf_le_right.trans (inf_le_left.trans inf_le_right)
    --   x.bval i₂: inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    --   a₂=xi₂:   inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
    --   x.bval i₁: inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    --   a₁=xi₁:   inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    --   Γ:         inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    apply bv_use ((i₁, i₂), j₁, j₂)
    simp only [prod_func, prod_bval]
    apply le_inf
    · -- bval: (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
      exact le_inf (le_inf
        (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))))
        (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))))
        (le_inf
          (inf_le_right.trans (inf_le_left.trans inf_le_left))
          (inf_le_left.trans inf_le_left))
    · apply le_inf
      · -- pair equality: pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
        -- ctx4 component accesses: a₁=xi₁ at (.3.left.right), a₂=xi₂ at (.3.right), b₁=yj₁ at (.2.right), b₂=yj₂ at (.1.right)
        -- But mem_unfold gives: a₁ =ᴮ x.func i₁, not x.func i₁ =ᴮ a₁
        -- So we use them directly (no bv_symm needed):
        apply pair_eq_pair_iff.mpr; constructor
        · apply pair_eq_pair_iff.mpr; exact ⟨
            inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))),
            inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))⟩
        · apply pair_eq_pair_iff.mpr; exact ⟨
            inf_le_right.trans (inf_le_left.trans inf_le_right),
            inf_le_left.trans inf_le_right⟩
      · -- χ: pair(xi₁)(yj₁) ∈ f ⊓ pair(xi₂)(yj₂) ∈ f
        -- Γ accessible via inf_le_right^5 from ctx4; then compose with Hpair₁, Hpair₂
        apply le_inf
        · -- pair(xi₁)(yj₁) ∈ f: use mem_congr (pair a₁ b₁ =ᴮ pair xi₁ yj₁) bv_refl (pair a₁ b₁ ∈ f)
          apply mem_congr _ bv_refl
          · -- pair a₁ b₁ ∈ f via Hpair₁
            exact (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
                    (inf_le_right.trans inf_le_right)))).trans Hpair₁
          · -- pair a₁ b₁ =ᴮ pair xi₁ yj₁ via pair_congr and equalities from ctx4
            apply pair_eq_pair_iff.mpr
            exact ⟨inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))),
                   inf_le_right.trans (inf_le_left.trans inf_le_right)⟩
        · -- pair(xi₂)(yj₂) ∈ f
          apply mem_congr _ bv_refl
          · exact (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
                    (inf_le_right.trans inf_le_right)))).trans Hpair₂
          · apply pair_eq_pair_iff.mpr
            exact ⟨inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)),
                   inf_le_left.trans inf_le_right⟩

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
  obtain ⟨_Ha_mem, _Hb_mem, H⟩ := H_mem
  -- H : Γ ≤ ⨆ a'', a'' ∈ η ⊓ ⨆ b'', b'' ∈ η ⊓ (pair a'' a ∈ f ⊓ pair b'' b ∈ f ⊓ a'' ∈ b'')
  have H_inj' : Γ ≤ is_inj f := is_inj_of_is_injective_function H_inj
  apply le_trans (le_inf H le_rfl)
  apply bv_cases_left; intro a''
  -- goal: (a''∈η ⊓ ⨆ b'', b''∈η ⊓ (...)) ⊓ Γ ≤ a'∈b'
  -- extract ⨆ b'' to left
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_cases_left; intro b''
  -- goal: (b''∈η ⊓ ((pair a'' a ∈ f ⊓ pair b'' b ∈ f) ⊓ a''∈b'')) ⊓ ((a''∈η ⊓ ⨆ ..) ⊓ Γ) ≤ a'∈b'
  -- use `apply` to decompose mem_congr, so each subgoal has a concrete type
  apply mem_congr (x₁ := a'') (x₂ := b'')
  · -- prove a'' =ᴮ a' via is_inj: pair a'' a ∈ f and pair a' a ∈ f
    apply eq_of_is_inj_of_eq
    · exact inf_le_right.trans (inf_le_right.trans H_inj')
    · exact bv_refl (x := a)
    · exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    · exact inf_le_right.trans (inf_le_right.trans H_mem₁)
  · -- prove b'' =ᴮ b' via is_inj: pair b'' b ∈ f and pair b' b ∈ f
    apply eq_of_is_inj_of_eq
    · exact inf_le_right.trans (inf_le_right.trans H_inj')
    · exact bv_refl (x := b)
    · exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact inf_le_right.trans (inf_le_right.trans H_mem₂)
  · -- prove a'' ∈ b''
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- ============================================================
-- src/aleph_one.lean:451-579: remaining well_ordering lemmas
-- ============================================================

-- src/aleph_one.lean:451
lemma induced_epsilon_rel_sub_image_left {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f)
    (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a ∈ᴮ image η x f := by
  rw [mem_image_iff]; rw [mem_induced_epsilon_rel_iff H_func] at H
  obtain ⟨Ha_mem, _, H_sup⟩ := H
  refine ⟨Ha_mem, le_trans H_sup (iSup_le (fun a' => le_iSup_of_le a'
    (le_inf inf_le_left (le_trans inf_le_right (iSup_le (fun b' =>
      le_trans inf_le_right (inf_le_left.trans inf_le_left)))))))⟩

-- src/aleph_one.lean:461
lemma induced_epsilon_rel_sub_image_right {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f)
    (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ b ∈ᴮ image η x f := by
  rw [mem_image_iff]; rw [mem_induced_epsilon_rel_iff H_func] at H
  obtain ⟨_, Hb_mem, H_sup⟩ := H
  refine ⟨Hb_mem, le_trans H_sup (iSup_le (fun a' => le_trans inf_le_right (iSup_le (fun b' =>
    le_iSup_of_le b' (le_inf inf_le_left (le_trans inf_le_right
      (inf_le_left.trans inf_le_right)))))))⟩

-- src/aleph_one.lean:471
lemma image_eq_of_eq_induced_epsilon_rel_aux
    {η ρ f g : bSet 𝔹} {Γ}
    (Hη_inj : Γ ≤ is_injective_function η omega f)
    (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
    (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (H_exists_two : Γ ≤ exists_two η) :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ image η omega f ⟹ z ∈ᴮ image ρ omega g := by
  sorry -- TODO: port from src/aleph_one.lean:471

-- src/aleph_one.lean:503
lemma image_eq_of_eq_induced_epsilon_rel
    {η ρ f g : bSet 𝔹} {Γ}
    (Hη_inj : Γ ≤ is_injective_function η omega f)
    (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
    (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (H_exists_two : Γ ≤ exists_two η)
    (H_exists_two' : Γ ≤ exists_two ρ) :
    Γ ≤ image η omega f =ᴮ image ρ omega g := by
  refine mem_ext ?_ ?_
  · apply image_eq_of_eq_induced_epsilon_rel_aux Hη_inj Hρ_inj H_eq H_exists_two
  · apply image_eq_of_eq_induced_epsilon_rel_aux Hρ_inj Hη_inj (bv_symm H_eq) H_exists_two'

-- src/aleph_one.lean:515
lemma eq_of_eq_induced_epsilon_rel
    {η ρ f g : bSet 𝔹} {Γ}
    (Hη_ord : Γ ≤ Ord η) (Hρ_ord : Γ ≤ Ord ρ)
    (Hη_inj : Γ ≤ is_injective_function η omega f)
    (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
    (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (H_exists_two : Γ ≤ exists_two η)
    (H_exists_two' : Γ ≤ exists_two ρ) :
    Γ ≤ η =ᴮ ρ := by
  sorry -- TODO: port from src/aleph_one.lean:515

end well_ordering

-- ============================================================
-- src/aleph_one.lean:583-888: section a1
-- ============================================================

section a1

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:586
-- The comprehension predicate for a1
noncomputable def a1' : bSet 𝔹 :=
  comprehend
    (fun x : bSet 𝔹 => ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
      (image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
    (bv_powerset (prod omega omega))

-- src/aleph_one.lean:612
lemma a1'_AE {Γ : 𝔹} : Γ ≤ ⨅ z, z ∈ᴮ a1' ⟹
    ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
    image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ z ⊓ (z =ᴮ ∅)ᶜ := by
  -- B_ext for ϕ (changing the last argument x)
  have H_congr : B_ext (fun x : bSet 𝔹 =>
      ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
      (image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ) :=
    B_ext_iSup (h := fun η => B_ext_inf (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun f => B_ext_inf
        (h₁ := B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_bv_eq_right))
        (h₂ := B_ext_neg (h := B_ext_bv_eq_left)))))
  apply le_iInf; intro z; rw [← deduction]
  -- From z ∈ a1' (= comprehend ϕ' (bv_powerset...)), use mem_comprehend_iff
  have H_from : Γ ⊓ z ∈ᴮ (a1' : bSet 𝔹) ≤ z ∈ᴮ (a1' : bSet 𝔹) := inf_le_right
  -- a1' is definitionally equal to comprehend ϕ' (bv_powerset (prod ω ω))
  -- Use mem_comprehend_iff to convert z ∈ a1' to ⨆ χ, ...
  -- Since a1' = comprehend ... by def, mem_comprehend_iff applies directly
  rw [show (a1' : bSet 𝔹) = comprehend
      (fun x : bSet 𝔹 => ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
        (image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
      (bv_powerset (prod omega omega)) from rfl] at H_from
  rw [mem_comprehend_iff] at H_from
  apply le_trans (le_inf H_from le_rfl)
  apply bv_cases_left; intro χ
  -- ctx: (bv_powerset...).bval χ ⊓ (z =ᴮ w ⊓ ϕ' w) ⊓ Γ, where w = (bv_powerset...).func χ
  -- The type is: (bv_powerset (prod omega omega)).bval χ ⊓
  --   (z =ᴮ (bv_powerset (prod omega omega)).func χ ⊓ (⨆ η, ...)) ⊓ Γ ≤ ⨆ η, ...
  -- h_zeq: ctx ≤ z =ᴮ w  (from the left ⊓ part)
  -- h_phi: ctx ≤ ϕ' w (the nested ⨆ expression)
  -- Apply H_congr: ϕ' w ≤ ϕ' z given w =ᴮ z
  refine le_trans (le_inf ?_ ?_) (H_congr ((bv_powerset (prod omega omega)).func χ) z)
  · -- Need: ctx ≤ (bv_powerset...).func χ =ᴮ z
    -- from inf_le_left (bval ⊓ (z=w ⊓ ϕ'w)) gives z=w; bv_symm gives w=z
    exact bv_symm (inf_le_left.trans (inf_le_right.trans inf_le_left))
  · -- Need: ctx ≤ ϕ' w (the outer ⨆ at w = func χ)
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- src/aleph_one.lean:620
noncomputable def a1_func (χ : (a1' (𝔹 := 𝔹)).type) : bSet 𝔹 := ∅

-- src/aleph_one.lean:630
noncomputable def a1_aux : bSet 𝔹 := ⟨(a1' (𝔹 := 𝔹)).type, a1_func, (a1' (𝔹 := 𝔹)).bval⟩

-- src/aleph_one.lean:632
lemma Ord_of_mem_a1_aux {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ a1_aux) : Γ ≤ Ord η := by
  rw [mem_unfold] at H_mem; apply le_trans H_mem; apply iSup_le; intro χ
  have hOrd : (⊤ : 𝔹) ≤ Ord (∅ : bSet 𝔹) :=
    le_trans (le_inf zero_eq_empty Ord_zero) (B_ext_Ord _ _)
  -- a1_aux.func χ = ∅ definitionally (a1_func χ = ∅)
  -- goal: a1'.bval χ ⊓ η =ᴮ ∅ ≤ Ord η
  -- ∅ =ᴮ η ⊓ Ord ∅ ≤ Ord η, and a1'.bval χ ⊓ η =ᴮ ∅ ≤ ∅ =ᴮ η ⊓ Ord ∅
  exact le_trans (le_inf (bv_symm inf_le_right) (le_trans le_top hOrd)) (B_ext_Ord _ _)

-- src/aleph_one.lean:641
noncomputable def a1 : bSet 𝔹 := insert 0 (insert 1 a1_aux)

-- src/aleph_one.lean:643
lemma mem_a1_iff₀ {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ a1 ↔ Γ ≤ z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ a1_aux := by
  simp only [a1, mem_insert1, sup_assoc]

-- src/aleph_one.lean:646
lemma Ord_of_mem_a1 {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ a1) : Γ ≤ Ord η := by
  rw [mem_a1_iff₀] at H_mem; apply le_trans H_mem; apply sup_le; apply sup_le
  · exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top (le_top.trans Ord_zero)))
      (B_ext_Ord _ _)
  · exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top (le_top.trans Ord_one)))
      (B_ext_Ord _ _)
  · exact Ord_of_mem_a1_aux le_rfl

-- src/aleph_one.lean:655
lemma eq_zero_iff_eq_empty {Γ : 𝔹} {u : bSet 𝔹} : Γ ≤ u =ᴮ 0 ↔ Γ ≤ u =ᴮ ∅ := by
  constructor
  · intro H
    exact le_trans (le_inf H (zero_eq_empty (Γ := Γ))) bv_eq_trans
  · intro H
    exact le_trans (le_inf H (bv_symm (zero_eq_empty (Γ := Γ)))) bv_eq_trans

-- src/aleph_one.lean:662
lemma induced_rel_empty_of_eq_zero {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H_eq_zero : Γ ≤ η =ᴮ 0) : Γ ≤ induced_epsilon_rel η omega f =ᴮ ∅ := by
  rw [empty_iff_forall_not_mem]
  apply le_iInf; intro pr
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ pr ∈ᴮ induced_epsilon_rel η omega f ≤ ⊥
  set Γ' := Γ ⊓ pr ∈ᴮ induced_epsilon_rel η omega f
  have H_mem' : Γ' ≤ pr ∈ᴮ induced_epsilon_rel η omega f := inf_le_right
  have H_func' : Γ' ≤ is_function η omega f := le_trans inf_le_left H_func
  obtain ⟨a, _b, _, _, _, Hab⟩ := eq_pair_of_mem_induced_epsilon_rel H_mem'
  have Ha_img : Γ' ≤ a ∈ᴮ image η omega f :=
    induced_epsilon_rel_sub_image_left H_func' Hab
  rw [mem_image_iff] at Ha_img
  have H_eq_empty : Γ' ≤ η =ᴮ ∅ :=
    eq_zero_iff_eq_empty.mp (le_trans inf_le_left H_eq_zero)
  have H_notz : Γ' ≤ ⨅ z, (z ∈ᴮ η)ᶜ := empty_iff_forall_not_mem.mp H_eq_empty
  apply bv_absurd (⨆ z, z ∈ᴮ η ⊓ pair z a ∈ᴮ f) Ha_img.2
  rw [compl_iSup]
  apply le_iInf; intro z
  exact le_trans (le_trans H_notz (iInf_le _ z)) (compl_le_compl inf_le_left)

-- src/aleph_one.lean:679
lemma nonempty_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H : Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ ∅)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ (η =ᴮ ∅) ≤ ⊥
  have H_eq_zero : Γ ⊓ (η =ᴮ ∅) ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero (le_trans inf_le_left H_func)
      (eq_zero_iff_eq_empty.mpr inf_le_right)
  exact bv_absurd _ H_eq_zero (le_trans inf_le_left H)

-- src/aleph_one.lean:690
lemma not_zero_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H' : Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ 0)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ (η =ᴮ 0) ≤ ⊥
  have H_rel_empty : Γ ⊓ (η =ᴮ 0) ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero (le_trans inf_le_left H_func) inf_le_right
  exact bv_absurd _ H_rel_empty (le_trans inf_le_left H')

-- src/aleph_one.lean:700
lemma not_one_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H : Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ 1)ᶜ := by
  sorry -- TODO: port from src/aleph_one.lean:700

-- src/aleph_one.lean:723
lemma nonempty_induced_rel_iff_not_zero_and_not_one {η f : bSet 𝔹} {Γ : 𝔹}
    (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ is_function η omega f) :
    Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ ↔
    (Γ ≤ (η =ᴮ 0)ᶜ ∧ Γ ≤ (η =ᴮ 1)ᶜ) := by
  sorry -- TODO: port from src/aleph_one.lean:723

-- src/aleph_one.lean:746
/-- a1 contains every ordinal η which injects into ω -/
lemma mem_a1_of_injects_into_omega_aux {Γ : 𝔹} {η : bSet 𝔹}
    (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ ⨆ f, is_injective_function η omega f)
    (H_not_zero : Γ ≤ (η =ᴮ 0)ᶜ) (H_not_one : Γ ≤ (η =ᴮ 1)ᶜ) :
    Γ ≤ η ∈ᴮ a1_aux := by
  sorry -- TODO: port from src/aleph_one.lean:746

-- src/aleph_one.lean:777
lemma mem_a1_iff {Γ : 𝔹} {η : bSet 𝔹} (H_ord : Γ ≤ Ord η) :
    Γ ≤ η ∈ᴮ a1 ↔ Γ ≤ ⨆ f, is_injective_function η omega f := by
  sorry -- TODO: port from src/aleph_one.lean:777

-- src/aleph_one.lean:802
lemma a1_transitive {Γ : 𝔹} : Γ ≤ is_transitive a1 := by
  sorry -- TODO: port from src/aleph_one.lean:802

-- src/aleph_one.lean:818
lemma a1_ewo {Γ : 𝔹} : Γ ≤ ewo a1 := by
  unfold ewo epsilon_well_orders
  refine le_inf ?_ ?_
  · -- epsilon_trichotomy a1: all members of a1 are Ords and ordinals satisfy trichotomy
    apply epsilon_trichotomy_of_sub_Ord
    apply le_iInf; intro x; rw [← deduction]
    exact Ord_of_mem_a1 inf_le_right
  · -- epsilon_well_founded a1: regularity gives well-foundedness for any sub-Ord
    exact epsilon_wf_of_sub_Ord a1

-- src/aleph_one.lean:826
lemma a1_Ord {Γ : 𝔹} : Γ ≤ Ord a1 := le_inf a1_ewo a1_transitive

-- src/aleph_one.lean:828
lemma a1_not_le_omega {Γ : 𝔹} : Γ ≤ (injects_into a1 omega)ᶜ := by
  sorry -- TODO: port from src/aleph_one.lean:828

-- src/aleph_one.lean:834
lemma a1_spec {Γ : 𝔹} : Γ ≤ aleph_one_Ord_spec a1 := by
  sorry -- TODO: port from src/aleph_one.lean:834

-- src/aleph_one.lean:862
lemma a1_le_of_omega_lt {Γ : 𝔹} : Γ ≤ le_of_omega_lt a1 := by
  sorry -- TODO: port from src/aleph_one.lean:862

end a1

-- ============================================================
-- src/aleph_one.lean:890-926: final section
-- ============================================================

section

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:894
lemma injects_into_omega_of_mem_aleph_one_check {Γ : 𝔹} {z : bSet 𝔹}
    (H_mem : Γ ≤ z ∈ᴮ (check PSet.aleph_one : bSet 𝔹)) : Γ ≤ injects_into z bSet.omega := by
  rw [mem_unfold] at H_mem
  apply le_trans H_mem
  apply iSup_le; intro η
  simp only [check_bval_top, top_inf_eq, check_func]
  -- Goal: z =ᴮ check (PSet.aleph_one.Func (check_cast η)) ≤ injects_into z omega
  -- check (PSet.aleph_one.Func (check_cast η)) injects into omega (PSet fact)
  have h_pset : PSet.injects_into (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η)) PSet.omega :=
    PSet.injects_into_omega_of_mem_aleph_one (PSet.func_mem PSet.aleph_one (check_cast (𝔹 := 𝔹) η))
  -- Lift to bSet
  have h_inj : (⊤ : 𝔹) ≤ injects_into (check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η)))
      bSet.omega := check_injects_into h_pset
  -- From z =ᴮ w and injects_into w omega ≥ ⊤, derive injects_into z omega
  calc z =ᴮ check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η))
      ≤ check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η)) =ᴮ z ⊓
          injects_into (check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η))) bSet.omega :=
        le_inf (bv_symm le_rfl) (le_trans le_top h_inj)
    _ ≤ injects_into z bSet.omega := B_ext_injects_into_left _ _

-- src/aleph_one.lean:905
lemma mem_aleph_one_of_injects_into_omega {x : bSet 𝔹} {Γ : 𝔹}
    (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) {z : bSet 𝔹}
    (H_x_Ord : Γ ≤ Ord x) (H_z_Ord : Γ ≤ Ord z)
    (H_inj : Γ ≤ injects_into z bSet.omega) : Γ ≤ z ∈ᴮ x := by
  -- Proof by contradiction: assume z ∉ x, then x ⊆ z → x injects into omega → contradiction
  have hbot : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ ⊥ := by
    -- By Ord.resolve_lt: (z ∈ x)ᶜ → x ∈ z ⊔ x = z
    have H_z_Ord' : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ Ord z := le_trans inf_le_left H_z_Ord
    have H_x_Ord' : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ Ord x := le_trans inf_le_left H_x_Ord
    have H_not_mem : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ (z ∈ᴮ x)ᶜ := inf_le_right
    have H_tri := Ord.resolve_lt H_z_Ord' H_x_Ord' H_not_mem
    -- H_tri : Γ ⊓ (z ∈ x)ᶜ ≤ x ∈ z ⊔ x = z, so x ⊆ z
    have H_sub : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ x ⊆ᴮ z := by
      rw [Ord.le_iff_lt_or_eq H_x_Ord' H_z_Ord']
      exact H_tri.trans (sup_le le_sup_left le_sup_right)
    -- injects_into x omega
    have H_inj_x : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ injects_into x bSet.omega :=
      injects_into_trans (injects_into_of_subset H_sub) (le_trans inf_le_left H_inj)
    -- aleph_one_Ord_spec x says (injects_into x omega)ᶜ
    exact bv_absurd _ H_inj_x (le_trans inf_le_left (bv_and_left H_aleph_one))
  -- Convert hbot to conclusion
  have : Γ ≤ (z ∈ᴮ x)ᶜ ⟹ ⊥ := deduction.mp hbot
  rwa [imp_bot, compl_compl] at this

-- src/aleph_one.lean:915
lemma aleph_one_check_sub_aleph_one_aux {x : bSet 𝔹} {Γ : 𝔹}
    (H_ord : Γ ≤ Ord x) (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) :
    Γ ≤ (check PSet.aleph_one : bSet 𝔹) ⊆ᴮ x := by
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  -- goal: Γ ⊓ w ∈ᴮ (check PSet.aleph_one) ≤ w ∈ᴮ x
  apply mem_aleph_one_of_injects_into_omega (le_trans inf_le_left H_aleph_one)
    (le_trans inf_le_left H_ord)
  · -- Ord w: w ∈ check PSet.aleph_one and PSet.aleph_one is an Ord
    exact Ord_of_mem_Ord inf_le_right (check_Ord PSet.aleph_one_Ord)
  · -- injects_into w omega
    exact injects_into_omega_of_mem_aleph_one_check inf_le_right

end

end bSet
