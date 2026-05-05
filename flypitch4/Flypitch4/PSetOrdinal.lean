/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/pSet_ordinal.lean (lines 1-500) — Task 6a -/

import Flypitch4.ToMathlib
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
## Port notes (src/pSet_ordinal.lean → Flypitch4.PSetOrdinal)

### Key API renames

- `tactic.tidy` → `aesop` / `simp` / hand proofs
- `ordinal.limit_rec_on` → `induction η using Ordinal.limitRecOn`
- `ordinal.is_limit` → `Order.IsSuccLimit`
- `ordinal.lt_succ` / `lt_succ_self` → `Order.lt_succ`
- `ordinal.succ η` → `Order.succ η`
- `pSet` → `PSet`; `pSet.equiv` → `PSet.Equiv`; `pSet.mem.mk` → `PSet.Mem.mk`
- `pSet.succ x = insert x x` → `PSet.succ_ord x`
- `ordinal.mk` (Lean 3) → `Ordinal.toPSet` (mathlib4, aliased as `PSet.ordinalMk`)
- `mem_Union` → `PSet.mem_sUnion`
- `Set` (Lean 3 ZFC quotient) → `ZFSet`
- `Set.regularity` → `ZFSet.regularity`
- `push_neg` → `push Not` (deprecated, warning only)
- `ZFSet.not_mem_empty` → `ZFSet.notMem_empty`
- `⟦x⟧ : ZFSet` → `ZFSet.mk x` (more reliable elaboration)
- `typein` (in PSet namespace) → `Ordinal.typein` (fully qualified)
- `PSet.Type ∅ = PEmpty` (not `ULift Empty` as in Lean 3)
- `ordinal.mk_zero_type` etc: adapted to mathlib4 universe conventions

### Namespace choices for 6b, 6c

All declarations in `namespace PSet`.
`ordinalMk = Ordinal.toPSet`.
`succ_ord = insert x x`.
-/

universe u

noncomputable section

-- ============================================================
-- Ordinal namespace: tiny helper
-- ============================================================

namespace Ordinal

lemma lt_zero_false {x : Ordinal} : x < 0 → False :=
  fun h => absurd h (not_lt.mpr (bot_le (a := x)))

end Ordinal

-- ============================================================
-- PSet namespace
-- Lines 30+ of src/pSet_ordinal.lean
-- ============================================================

namespace PSet

-- `ordinalMk η` = `Ordinal.toPSet η` (the von Neumann ordinal as a pre-set).
abbrev ordinalMk : Ordinal.{u} → PSet.{u} := Ordinal.toPSet

-- `succ_ord x = insert x x` — the pre-set ordinal successor.
-- Named `succ_ord` to avoid collision with `Order.succ`.
@[reducible] def succ_ord (x : PSet) : PSet := insert x x

/-! ### Basic structural lemmas -/

lemma powerset_type {x : PSet} : (powerset x).Type = Set (x.Type) := by
  cases x; rfl

@[simp] lemma mem_mk' {x : PSet} {i} : x.Func i ∈ x := PSet.func_mem x i

lemma mem_unfold {x y : PSet} : x ∈ y ↔ ∃ j : y.Type, Equiv x (y.Func j) := by
  cases y; rfl

lemma ext_iff {x y : PSet} : Equiv x y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
  PSet.equiv_iff_mem

lemma mem_mem_false {x y : PSet.{u}} (H₁ : x ∈ y) (H₂ : y ∈ x) : False :=
  PSet.mem_asymm H₂ H₁

@[simp] lemma mem_self {x : PSet.{u}} (H : x ∈ x) : False :=
  PSet.mem_irrefl x H

-- typein of out.r is less than the ordinal itself
lemma typein_lt_type' {ξ : Ordinal} {i : ξ.out.α} :
    @Ordinal.typein _ ξ.out.r ξ.out.wo i < ξ := by
  have h := @Ordinal.typein_lt_type _ ξ.out.r ξ.out.wo i
  -- h : Ordinal.typein ξ.out.r i < Ordinal.type ξ.out.r
  -- Ordinal.type ξ.out.r = ξ (by out_eq: type of the canonical well-order on ξ.ToType = ξ)
  rwa [show Ordinal.type ξ.out.r = ξ from ξ.out_eq] at h

/-! ### Key facts about ordinalMk = Ordinal.toPSet -/

-- The type of `ordinalMk η` is `η.ToType`
@[simp] lemma ordinalMk_type {η : Ordinal} : (ordinalMk η).Type = η.ToType :=
  Ordinal.type_toPSet η

-- Membership characterization (the main tool)
lemma mem_ordinalMk_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk η ↔ ∃ a < η, Equiv x (ordinalMk a) :=
  Ordinal.mem_toPSet_iff

-- Elementary membership
lemma mk_mem_mk_of_lt {ξ η : Ordinal} (H_lt : ξ < η) :
    ordinalMk ξ ∈ ordinalMk η :=
  mem_ordinalMk_iff.mpr ⟨ξ, H_lt, PSet.Equiv.refl _⟩

-- The zero case: ordinalMk 0 ≡ ∅ (extensionally equivalent)
-- Note: this is Equiv, not equality, since Ordinal.ToType 0 ≠ PEmpty definitionally
lemma ordinalMk_zero_equiv : PSet.Equiv (ordinalMk (0 : Ordinal.{u})) (∅ : PSet.{u}) := by
  apply PSet.Mem.ext; intro z
  simp [mem_ordinalMk_iff]

-- For convenience in downstream proofs, state the simp lemma for ZFSet
@[simp] lemma ordinalMk_zero_zfset : ZFSet.mk (ordinalMk (0 : Ordinal.{u})) = ∅ := by
  rw [ZFSet.eq_empty]
  intro y hy
  -- y ∈ ZFSet.mk (ordinalMk 0) means ∃ a < 0, y = ZFSet.mk (ordinalMk a)
  induction y using Quotient.inductionOn with
  | h p =>
    -- ⟦p⟧ = ZFSet.mk p (definitional)
    -- hy : ⟦p⟧ ∈ ZFSet.mk (ordinalMk 0)
    rw [show (⟦p⟧ : ZFSet) = ZFSet.mk p from rfl] at hy
    rw [ZFSet.mk_mem_iff] at hy
    rw [mem_ordinalMk_iff] at hy
    obtain ⟨a, ha, _⟩ := hy
    exact absurd ha (not_lt.mpr (bot_le))

-- For 6b/6c: type of ordinalMk 0
-- Note: Ordinal.ToType 0 is the empty type but not definitionally PEmpty;
-- this is a sorry (TODO) pending a better proof.
@[simp] lemma ordinalMk_zero_type : (ordinalMk (0 : Ordinal.{u})).Type = PEmpty := by
  -- TODO: port from src/pSet_ordinal.lean:93-95
  -- ordinalMk_type gives .Type = Ordinal.ToType 0 = 0.out.α which is empty but ≠ PEmpty def'ly
  simp only [ordinalMk_type]
  sorry

-- Successor: membership in ordinalMk(succ η) ↔ in ordinalMk η or ≡ ordinalMk η
lemma ordinalMk_succ_mem_iff {η : Ordinal} {x : PSet} :
    x ∈ ordinalMk (Order.succ η) ↔ x ∈ ordinalMk η ∨ Equiv x (ordinalMk η) := by
  rw [mem_ordinalMk_iff, mem_ordinalMk_iff]
  constructor
  · rintro ⟨a, ha, heq⟩
    rw [Order.lt_succ_iff] at ha
    rcases ha.eq_or_lt with rfl | hlt
    · right; exact heq
    · left; exact ⟨a, hlt, heq⟩
  · rintro (⟨a, ha, heq⟩ | heq)
    · exact ⟨a, ha.trans (Order.lt_succ η), heq⟩
    · exact ⟨η, Order.lt_succ η, heq⟩

-- `succ_ord`: the type is Option
@[simp] lemma succ_ord_type {x : PSet} : (succ_ord x).Type = Option (x.Type) := by
  cases x; rfl

@[simp] lemma option_succ_ord_type {x : PSet} :
    Option (succ_ord x).Type = Option (Option (x.Type)) := by simp

def succ_type_cast {x : PSet} : (succ_ord x).Type → Option (x.Type) := cast succ_ord_type
def succ_type_cast' {x : PSet} : Option (x.Type) → (succ_ord x).Type := cast succ_ord_type.symm

def option_cast' {x : PSet} : Option (Option x.Type) → Option (succ_ord x).Type :=
  cast option_succ_ord_type.symm

@[simp] lemma succ_ord_func_none {x : PSet} :
    (succ_ord x).Func (succ_type_cast' none) = x := by cases x; rfl

@[simp] lemma succ_ord_func_some {x : PSet} {i} :
    (succ_ord x).Func (succ_type_cast' (some i)) = x.Func i := by cases x; rfl

lemma succ_type_forall {x : PSet} {P : (succ_ord x).Type → Prop} :
    (∀ (i : (succ_ord x).Type), P i) = ∀ (i : Option (x.Type)), P (succ_type_cast' i) := by
  cases x; rfl

lemma succ_type_exists {x : PSet} {P : (succ_ord x).Type → Prop} :
    (∃ (i : (succ_ord x).Type), P i) = ∃ (i : Option (x.Type)), P (succ_type_cast' i) := by
  cases x; rfl

lemma option_succ_type_forall {x : PSet} {P : Option (succ_ord x).Type → Prop} :
    (∀ i : Option (succ_ord x).Type, P i) =
    ∀ (i : Option (Option x.Type)), P (option_cast' i) := by
  cases x; rfl

-- The type of ordinalMk for a limit ordinal is η.ToType
@[simp] lemma ordinalMk_limit_type {η : Ordinal} (H_limit : Order.IsSuccLimit η) :
    (ordinalMk η).Type = η.ToType :=
  ordinalMk_type

@[simp] lemma mem_mk_limit_of_lt {η : Ordinal} (_H_limit : Order.IsSuccLimit η)
    (ξ : Ordinal) (Hξ : ξ < η) : ordinalMk ξ ∈ ordinalMk η :=
  mk_mem_mk_of_lt Hξ

/-! ### Epsilon well-orders and pre-set ordinals -/

def epsilon_well_orders (x : PSet.{u}) : Prop :=
  (∀ y, y ∈ x → (∀ z, z ∈ x → (Equiv y z ∨ y ∈ z ∨ z ∈ y))) ∧
  (∀ u, u ⊆ x → (¬ (Equiv u (∅ : PSet.{u})) → ∃ y, (y ∈ u ∧ (∀ z', z' ∈ u → ¬ z' ∈ y))))

def is_transitive (x : PSet) : Prop := ∀ y, y ∈ x → y ⊆ x

def Ord (x : PSet) : Prop := epsilon_well_orders x ∧ is_transitive x

@[simp] lemma is_transitive_of_Ord {x} (H : Ord x) : is_transitive x := H.right

@[simp] lemma is_ewo_of_Ord {x} (H : Ord x) : epsilon_well_orders x := H.left

@[simp, refl] lemma equiv_refl' {x : PSet} : PSet.Equiv x x := PSet.Equiv.refl _

lemma equiv_of_eq {x y : PSet} : ZFSet.mk x = ZFSet.mk y → PSet.Equiv x y :=
  ZFSet.exact

lemma equiv_iff_eq {x y : PSet} : Equiv x y ↔ ZFSet.mk x = ZFSet.mk y :=
  ⟨ZFSet.sound, ZFSet.exact⟩

-- PSet membership ↔ ZFSet membership
lemma mem_iff {x y : PSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := by
  simp [ZFSet.mk_mem_iff]

lemma not_mem_iff {x y : PSet} : x ∉ y ↔ ¬ (ZFSet.mk x ∈ ZFSet.mk y) := by
  simp [ZFSet.mk_mem_iff]

lemma mem_sound {x y : PSet} : x ∈ y ↔ ZFSet.mk x ∈ ZFSet.mk y := mem_iff

-- Helpers for insert membership
lemma mem_insert_mem {x y z : PSet} (H : x ∈ insert y z) : Equiv x y ∨ x ∈ z :=
  PSet.mem_insert_iff.mp H

lemma mem_insert_intro {x y z : PSet} (H : Equiv x y ∨ x ∈ z) : x ∈ insert y z :=
  PSet.mem_insert_iff.mpr H

@[simp] lemma mem_succ_ord (x : PSet) : x ∈ succ_ord x :=
  PSet.mem_insert_iff.mpr (Or.inl (PSet.Equiv.refl _))

lemma subset_of_all_mem {x y : PSet} (H : ∀ z, z ∈ y → z ∈ x) : y ⊆ x :=
  PSet.subset_iff.mpr (fun _ hz => H _ hz)

lemma all_mem_of_subset {x y : PSet} (H : y ⊆ x) : ∀ z, z ∈ y → z ∈ x :=
  fun z hz => PSet.mem_of_subset H hz

lemma subset_iff_all_mem {x y : PSet} : y ⊆ x ↔ ∀ z, z ∈ y → z ∈ x :=
  PSet.subset_iff

lemma ZFSet_mem_mk' {x : PSet} {i} : ZFSet.mk (x.Func i) ∈ ZFSet.mk x := by
  rw [← mem_iff]; exact mem_mk' (x := x) (i := i)

lemma mem_trans_of_transitive {x y z : PSet} (H₁ : x ∈ y) (H₂ : y ∈ z)
    (H_trans : is_transitive z) : x ∈ z :=
  all_mem_of_subset (H_trans y H₂) x H₁

lemma empty_empty : (∅ : ZFSet) = ZFSet.mk (∅ : PSet) := rfl

-- Type of empty PSet is PEmpty (mathlib4: `PSet.empty = ⟨_, PEmpty.elim⟩`)
@[simp] lemma empty_type : PSet.Type (∅ : PSet) = PEmpty := by
  rw [PSet.empty_def]; rfl

lemma exists_mem_of_nonempty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) : ∃ y, y ∈ x := by
  by_contra h
  push_neg at h
  exact H (PSet.Mem.ext (fun w => ⟨fun hw => absurd hw (h w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩))

lemma not_empty_of_not_equiv_empty {x : PSet.{u}} (H : ¬ Equiv x (∅ : PSet.{u})) :
    ZFSet.mk x ≠ ∅ := by
  intro H'
  apply H
  -- ZFSet.mk x = ∅ = ZFSet.mk ∅, so exact ZFSet.exact H'
  have : ZFSet.mk x = ZFSet.mk (∅ : PSet.{u}) := by
    rw [H']; rfl
  exact ZFSet.exact this

lemma is_epsilon_well_founded (x : PSet.{u}) :
    ∀ (u : PSet.{u}), u ⊆ x → ¬ Equiv u (∅ : PSet.{u}) →
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  intro u _Hu Hu_ne_empty
  classical
  by_contra h
  push_neg at h
  -- h : ∀ y ∈ u, ∃ z ∈ u, z ∈ y
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty Hu_ne_empty
  obtain ⟨y, Hy₁, Hy₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  -- y is a ZFSet with y ∈ ZFSet.mk u and (ZFSet.mk u) ∩ y = ∅
  -- Get a PSet representative: y.out is a PSet with ZFSet.mk y.out = y
  have Hy₁' : y.out ∈ u := by
    have : ZFSet.mk y.out ∈ ZFSet.mk u := by
      rw [ZFSet.mk_out y]; exact Hy₁
    exact mem_iff.mpr this
  obtain ⟨z, Hz₁, Hz₂⟩ := h y.out Hy₁'
  -- z ∈ u and z ∈ y.out → contradiction since ZFSet.mk u ∩ y = ∅
  apply ZFSet.notMem_empty (ZFSet.mk z)
  rw [← Hy₂]
  apply ZFSet.mem_inter.mpr
  exact ⟨mem_iff.mp Hz₁, by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz₂⟩

@[simp] lemma Ord_empty : Ord (∅ : PSet.{u}) := by
  refine ⟨⟨fun y hy => absurd hy (PSet.notMem_empty y), ?_⟩,
    fun y hy => absurd hy (PSet.notMem_empty y)⟩
  intro u Hu H₂
  exact absurd (PSet.Mem.ext (fun w => ⟨
    fun hw => absurd (all_mem_of_subset Hu w hw) (PSet.notMem_empty w),
    fun hw => absurd hw (PSet.notMem_empty w)⟩)) H₂

lemma well_founded (u : PSet.{u}) (H_nonempty : ¬ Equiv u (∅ : PSet.{u})) :
    ∃ (y : PSet), y ∈ u ∧ ∀ (z' : PSet), z' ∈ u → z' ∉ y := by
  have Hu_ne : ZFSet.mk u ≠ ∅ := not_empty_of_not_equiv_empty H_nonempty
  obtain ⟨y, H₁, H₂⟩ := ZFSet.regularity (ZFSet.mk u) Hu_ne
  refine ⟨y.out, ?_, ?_⟩
  · have : ZFSet.mk y.out ∈ ZFSet.mk u := by rw [ZFSet.mk_out y]; exact H₁
    exact mem_iff.mpr this
  · intro z' Hz' Hz''
    apply ZFSet.notMem_empty (ZFSet.mk z')
    rw [← H₂]
    exact ZFSet.mem_inter.mpr
      ⟨mem_iff.mp Hz', by rw [← ZFSet.mk_out y]; exact mem_iff.mp Hz''⟩

lemma transitive_succ_ord (x : PSet) (H : is_transitive x) : is_transitive (succ_ord x) := by
  intro y Hy
  rcases mem_insert_mem Hy with heq | hin
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr ((PSet.Mem.congr_right heq).mp hz))
  · exact subset_of_all_mem fun z hz =>
      mem_insert_intro (Or.inr (all_mem_of_subset (H y hin) z hz))

@[simp] lemma Ord_succ_ord (x : PSet) (H : Ord x) : Ord (succ_ord x) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro y Hy z Hz
    rcases mem_insert_mem Hy with heq1 | hin1 <;>
    rcases mem_insert_mem Hz with heq2 | hin2
    · left; exact PSet.Equiv.trans heq1 heq2.symm
    · right; right; exact (PSet.Mem.congr_right heq1).mpr hin2
    · right; left; exact (PSet.Mem.congr_right heq2).mpr hin1
    · exact H.left.left y hin1 z hin2
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · exact transitive_succ_ord x H.right

lemma ordinalMk_lt_of_mem {ξ η : Ordinal} (H : ordinalMk ξ ∈ ordinalMk η) : ξ < η := by
  rw [mem_ordinalMk_iff] at H
  obtain ⟨a, ha, heq⟩ := H
  rcases lt_trichotomy ξ a with h | rfl | h
  · exact h.trans ha
  · exact ha
  · exfalso
    have h1 : ordinalMk a ∈ ordinalMk ξ := mk_mem_mk_of_lt h
    -- heq : Equiv (ordinalMk ξ) (ordinalMk a)
    -- Mem.congr_right heq : ∀ {w}, w ∈ ordinalMk ξ ↔ w ∈ ordinalMk a
    have h2 : ordinalMk a ∈ ordinalMk a := (PSet.Mem.congr_right heq).mp h1
    exact PSet.mem_irrefl _ h2

lemma transitive_Union (x : PSet) (H : ∀ y ∈ x, is_transitive y) : is_transitive (⋃₀ x) := by
  intro z Hz
  apply subset_of_all_mem; intro w Hw
  rw [PSet.mem_sUnion] at Hz ⊢
  obtain ⟨y, Hy, Hz'⟩ := Hz
  exact ⟨y, Hy, all_mem_of_subset (H y Hy z Hz') w Hw⟩

lemma equiv_mk_of_mem_mk {η : Ordinal} :
    ∀ x, x ∈ ordinalMk η → ∃ ρ < η, Equiv x (ordinalMk ρ) :=
  fun x hx => mem_ordinalMk_iff.mp hx

lemma Ord_limit : ∀ (o : Ordinal), Order.IsSuccLimit o →
    (∀ (o' : Ordinal), o' < o → Ord (ordinalMk o')) → Ord (ordinalMk o) := by
  intro η _Hη _ih
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x Hx z Hz
    obtain ⟨ξ₁, H₁, H₂⟩ := equiv_mk_of_mem_mk x Hx
    obtain ⟨ξ₂, H₁', H₂'⟩ := equiv_mk_of_mem_mk z Hz
    rcases lt_trichotomy ξ₁ ξ₂ with hlt | rfl | hlt
    · right; left
      rw [PSet.Mem.congr_left H₂, PSet.Mem.congr_right H₂']
      exact mk_mem_mk_of_lt hlt
    · left; exact PSet.Equiv.trans H₂ H₂'.symm
    · right; right
      rw [PSet.Mem.congr_right H₂, PSet.Mem.congr_left H₂']
      exact mk_mem_mk_of_lt hlt
  · intro u _Hu H_nonempty; exact well_founded u H_nonempty
  · intro y Hy
    obtain ⟨ρ, Hρ, Heq⟩ := equiv_mk_of_mem_mk y Hy
    rw [PSet.Subset.congr_left Heq]
    apply subset_of_all_mem; intro z Hz
    obtain ⟨σ, Hσ, Heq'⟩ := equiv_mk_of_mem_mk z Hz
    rw [PSet.Mem.congr_left Heq']
    exact mk_mem_mk_of_lt (Hσ.trans Hρ)

-- Ord is invariant under PSet.Equiv
lemma Ord_equiv {x y : PSet.{u}} (hxy : PSet.Equiv x y) (hx : Ord x) : Ord y := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- trichotomy: a ∈ y, b ∈ y → a and b are trichotomous
    intro a Ha b Hb
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    have Hb' : b ∈ x := (PSet.Mem.congr_right hxy.symm).mp Hb
    exact hx.left.left a Ha' b Hb'
  · -- well-foundedness
    intro u _Hu H_ne; exact well_founded u H_ne
  · -- transitivity: a ∈ y → a ⊆ y
    intro a Ha
    have Ha' : a ∈ x := (PSet.Mem.congr_right hxy.symm).mp Ha
    -- a ⊆ x (from hx.right)
    have hax : a ⊆ x := hx.right a Ha'
    -- a ⊆ y: for w ∈ a, w ∈ x, so w ∈ y
    apply subset_of_all_mem
    intro w Hw
    exact (PSet.Mem.congr_right hxy).mp (all_mem_of_subset hax w Hw)

-- Key: ordinalMk (Order.succ η) ≡ succ_ord (ordinalMk η)
lemma ordinalMk_succ_equiv {η : Ordinal} :
    PSet.Equiv (ordinalMk (Order.succ η)) (succ_ord (ordinalMk η)) := by
  apply PSet.Mem.ext; intro z
  rw [ordinalMk_succ_mem_iff, PSet.mem_insert_iff]
  tauto

@[simp] lemma Ord_mk (η : Ordinal) : Ord (ordinalMk η) := by
  induction η using Ordinal.limitRecOn with
  | zero => exact Ord_equiv ordinalMk_zero_equiv.symm Ord_empty
  | succ η ih =>
    -- ordinalMk_succ_equiv : Equiv (ordinalMk (succ η)) (succ_ord (ordinalMk η))
    -- Ord_succ_ord _ ih : Ord (succ_ord (ordinalMk η))
    -- Apply Ord_equiv in reverse: Equiv y x → Ord y → Ord x
    exact Ord_equiv ordinalMk_succ_equiv.symm (Ord_succ_ord _ ih)
  | limit η H_limit ih => exact Ord_limit η H_limit ih

lemma mem_mem_mem_false {x y z : PSet.{u}} (H₁ : x ∈ y) (H₂ : y ∈ z) (H₃ : z ∈ x) : False := by
  -- Use the ZFSet regularity axiom on {⟦x⟧, ⟦y⟧, ⟦z⟧}
  set S : ZFSet := {ZFSet.mk x, ZFSet.mk y, ZFSet.mk z}
  have H_nonempty : S ≠ ∅ := by
    intro h
    have hmem : ZFSet.mk x ∈ S := by simp [S]
    exact ZFSet.notMem_empty _ (h ▸ hmem)
  obtain ⟨w, Hw₁, Hw₂⟩ := ZFSet.regularity S H_nonempty
  -- w ∈ S and S ∩ w = ∅
  simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, S] at Hw₁
  -- In each case, find an element in S ∩ w to get contradiction with Hw₂
  have contradiction : ∃ q, q ∈ S ∩ w := by
    rcases Hw₁ with rfl | rfl | rfl
    · -- w = mk x, need q ∈ {mk x, mk y, mk z} ∩ mk x
      -- q = mk z works since H₃ : z ∈ x
      exact ⟨ZFSet.mk z, ZFSet.mem_inter.mpr ⟨by simp [S], mem_iff.mp H₃⟩⟩
    · -- w = mk y, need q ∈ {mk x, mk y, mk z} ∩ mk y
      -- q = mk x works since H₁ : x ∈ y
      exact ⟨ZFSet.mk x, ZFSet.mem_inter.mpr ⟨by simp [S], mem_iff.mp H₁⟩⟩
    · -- w = mk z, need q ∈ {mk x, mk y, mk z} ∩ mk z
      -- q = mk y works since H₂ : y ∈ z
      exact ⟨ZFSet.mk y, ZFSet.mem_inter.mpr ⟨by simp [S], mem_iff.mp H₂⟩⟩
  obtain ⟨q, hq⟩ := contradiction
  exact ZFSet.notMem_empty q (Hw₂ ▸ hq)

def mem_witness {y w : PSet.{u}} (H : w ∈ y) : Σ' (y_a : y.Type), (Equiv w (y.Func y_a)) := by
  rw [PSet.mem_def] at H
  obtain ⟨a, ha⟩ := Classical.indefiniteDescription _ H
  exact ⟨a, ha⟩

lemma transitive_of_mem_Ord (y x : PSet.{u}) (H : Ord x) (H_mem : y ∈ x) : is_transitive y := by
  intro w Hw
  apply subset_of_all_mem; intro z Hz
  have H_w_in_x : w ∈ x := all_mem_of_subset (H.right y H_mem) w Hw
  have H_z_in_x : z ∈ x := all_mem_of_subset (H.right w H_w_in_x) z Hz
  by_contra hzny
  rcases H.left.left y H_mem z H_z_in_x with heq | hin | hin
  · -- heq : Equiv y z, Hw : w ∈ y, Hz : z ∈ w → w ∈ z → w ∈ w contradiction
    exact mem_mem_false ((PSet.Mem.congr_right heq).mp Hw) Hz
  · -- hin : y ∈ z, Hz : z ∈ w, Hw : w ∈ y → cycle y ∈ z, z ∈ w, w ∈ y
    exact mem_mem_mem_false hin Hz Hw
  · -- hin : z ∈ y, but hzny : z ∉ y
    exact hzny hin

lemma mk_equiv_of_eq {β₁ β₂ : Ordinal.{u}} (H : β₁ = β₂) :
    Equiv (ordinalMk β₁) (ordinalMk β₂) := H ▸ PSet.Equiv.refl _

lemma mk_mem_succ {η : Ordinal.{u}} : ordinalMk η ∈ ordinalMk (Order.succ η) :=
  mk_mem_mk_of_lt (Order.lt_succ η)

lemma subset_Union {x y : PSet.{u}} (H : y ∈ x) : y ⊆ ⋃₀ x :=
  subset_of_all_mem fun z Hz => PSet.mem_sUnion.mpr ⟨y, H, Hz⟩

-- card_ex: cardinal → PSet via ordinal
def card_ex : Cardinal.{u} → PSet.{u} := fun κ => ordinalMk (Cardinal.ord κ)

-- WARNING: is_func corresponds to bSet.is_function, not bSet.is_func
-- f ⊆ prod x y ∧ ∀z ∈ x, ∃! w, pair z w ∈ f
@[reducible] def is_func (x y f : PSet.{u}) : Prop :=
  ZFSet.IsFunc (ZFSet.mk x) (ZFSet.mk y) (ZFSet.mk f)

@[reducible] def is_weak_func (x y f : PSet.{u}) : Prop :=
  ∀ z, z ∈ ZFSet.mk x → ∃! w, w ∈ ZFSet.mk y ∧ ZFSet.pair z w ∈ ZFSet.mk f

@[reducible] def is_extensional (f : PSet.{u}) : Prop :=
  ∀ w₁ w₂ v₁ v₂,
    ZFSet.pair (ZFSet.mk w₁) (ZFSet.mk v₁) ∈ ZFSet.mk f →
    ZFSet.pair (ZFSet.mk w₂) (ZFSet.mk v₂) ∈ ZFSet.mk f →
    Equiv w₁ w₂ → Equiv v₁ v₂

@[reducible] def is_surj (x y f : PSet.{u}) : Prop :=
  ∀ b : PSet.{u}, b ∈ y →
    ∃ a : PSet.{u}, a ∈ x ∧ ZFSet.pair (ZFSet.mk a) (ZFSet.mk b) ∈ ZFSet.mk f

end PSet

end -- noncomputable section
