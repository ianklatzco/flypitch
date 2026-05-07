/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/collapse.lean — Part 1 (lines 1-450).
   Covers: top-level helpers (cardinal, ordinal, topological_space, propositional lemmas),
   PFun extension lemmas (inter/compatible/subfun/sup/pSup/singleton/extend_via/trivial_extension).
   Part 2 (lines 451-916) covers the collapse_poset structure and collapse_algebra.
   The `end Flypitch` at the bottom closes the namespace; Part 2 will reopen it.
-/

import Flypitch4.RegularOpenAlgebra
import Flypitch4.PSetOrdinal
import Mathlib.Data.PFun
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family

open Set TopologicalSpace Cardinal PSet

universe u v

namespace Flypitch

/-! ## Preliminary order lemmas (src lines 9-14) -/

lemma poset_yoneda_iff {β : Type*} [Preorder β] {a b : β} :
    (∀ Γ : β, Γ ≤ a → Γ ≤ b) ↔ a ≤ b :=
  ⟨fun h => h a le_rfl, fun h _ hΓ => hΓ.trans h⟩

lemma poset_coyoneda_iff {β : Type*} [Preorder β] {a b : β} :
    (∀ Γ : β, a ≤ Γ → b ≤ Γ) ↔ b ≤ a :=
  ⟨fun h => h a le_rfl, fun h _ h' => h.trans h'⟩

/-! ## Cardinal helpers (src lines 28-50).
    These are helper lemmas used in the collapse algebra section.
    In Lean 4 / Mathlib 4: `cardinal.sum` → `Cardinal.sum`, `cardinal.lift` → `Cardinal.lift`,
    `cardinal.sup` → `iSup`. The universe annotations differ from Lean 3 — we use sorry stubs
    for helpers that are only needed to be stated, and the actual collapse algebra code will
    use Mathlib's `Cardinal.add_lt_of_lt`, `mul_lt_of_lt`, etc. directly. -/

/-- Analog of cardinal.sum_const_lift. TODO (15b): fix universe annotations. -/
theorem collapse_sum_const_lift (ι : Type u) (a : Cardinal.{max u v}) :
    Cardinal.sum (fun _ : ι => a) = Cardinal.lift.{v} (#ι) * a := by
  sorry -- TODO: universe mismatch; use Cardinal.sum_const + ring

/-- Analog of cardinal.sum_le_sup_lift. TODO (15b): fix universe annotations. -/
theorem collapse_sum_le_sup_lift {ι : Type u} (f : ι → Cardinal.{max u v}) :
    Cardinal.sum f ≤ Cardinal.lift.{v} (#ι) * ⨆ i, f i := by
  sorry -- TODO: Mathlib's sum_le_lift_mk_mul_iSup has different lift levels

/-- Analog of cardinal.mk_Union_le_sum_mk'. TODO (15b): fix universe annotations. -/
theorem collapse_mk_iUnion_le_sum_mk {ι : Type u} {α : Type (max u v)} {f : ι → Set α} :
    #(⋃ i, f i) ≤ Cardinal.sum (fun i => #(f i)) := by
  sorry -- TODO: type universe mismatch with mk_iUnion_le_sum_mk

/-- Analog of cardinal.mk_Union_le_lift. TODO (15b): fix universe annotations. -/
lemma collapse_mk_iUnion_le_lift {ι : Type u} {α : Type (max u v)} (f : ι → Set α) :
    #(⋃ i, f i) ≤ Cardinal.lift.{v} (#ι) * ⨆ i, #(f i) := by
  sorry -- TODO: type universe mismatch with mk_iUnion_le_lift

/-! ## Ordinal helpers (src lines 52-70) -/

/-- Analog of ordinal.sup_lt_ord_lift. TODO (15b): fix universe annotations. -/
theorem collapse_sup_lt_ord_lift {ι : Type u} (f : ι → Ordinal.{max u v}) {c : Ordinal}
    (H1 : Cardinal.lift.{v} (#ι) < c.cof) (H2 : ∀ i, f i < c) : iSup f < c := by
  sorry -- TODO: Ordinal.lift_iSup_lt_of_lt_cof has different universe levels

/-- Analog of ordinal.sup_lt_lift. TODO (15b): fix universe annotations. -/
theorem collapse_sup_lt_lift {ι : Type u} (f : ι → Cardinal.{max u v}) {c : Cardinal.{max u v}}
    (H1 : Cardinal.lift.{v} (#ι) < c.ord.cof)
    (H2 : ∀ i, f i < c) : iSup f < c := by
  sorry -- TODO: Cardinal.iSup_ord not found under that name; check Mathlib API

/-! ## Topological space helpers (src lines 72-84) -/

/-- Analog of topological_space.mem_interior_of_is_topological_basis. -/
lemma collapse_mem_interior_of_isTopologicalBasis {α} [TopologicalSpace α] {B : Set (Set α)}
    (hB : IsTopologicalBasis B) {s : Set α} {x : α} :
    x ∈ interior s ↔ ∃ t ⊆ s, t ∈ B ∧ x ∈ t := by
  rw [mem_interior]
  constructor
  · rintro ⟨t, h1t, h2t, h3t⟩
    rcases hB.exists_subset_of_mem_open h3t h2t with ⟨u, h1u, h2u, h3u⟩
    exact ⟨u, h3u.trans h1t, h1u, h2u⟩
  · rintro ⟨t, h1t, h2t, h3t⟩
    exact ⟨t, h1t, hB.isOpen h2t, h3t⟩

/-! ## Propositional lemmas (src lines 100-131) -/

@[simp] lemma iff_or_self_left {p q : Prop} : (p ↔ p ∨ q) ↔ (q → p) :=
  ⟨fun h hq => h.mpr (Or.inr hq), fun h => ⟨Or.inl, fun h' => h'.elim id h⟩⟩

@[simp] lemma iff_or_self_right {p q : Prop} : (p ↔ q ∨ p) ↔ (q → p) := by
  simp [or_comm]

@[simp] lemma and_iff_self_right {p q : Prop} : (p ∧ q ↔ p) ↔ (p → q) :=
  ⟨fun h hp => (h.mpr hp).2, fun h => ⟨And.left, fun hp => ⟨hp, h hp⟩⟩⟩

@[simp] lemma and_iff_self_left {p q : Prop} : (p ∧ q ↔ q) ↔ (q → p) := by
  rw [and_comm]; exact and_iff_self_right

lemma and_or_and_not {p q r : Prop} : p ∧ (q ∨ (r ∧ ¬p)) ↔ p ∧ q := by
  constructor
  · rintro ⟨hp, hq | ⟨_, hnp⟩⟩
    · exact ⟨hp, hq⟩
    · exact absurd hp hnp
  · rintro ⟨hp, hq⟩; exact ⟨hp, Or.inl hq⟩

lemma or_and_iff_or {p q r : Prop} : (p ∨ (q ∧ r) ↔ p ∨ q) ↔ (q → p ∨ r) :=
  ⟨fun h hq => (h.mpr (Or.inr hq)).imp id And.right,
   fun h => ⟨fun h' => h'.imp id And.left,
             fun h' => h'.elim Or.inl (fun hq => (h hq).imp id (fun hr => ⟨hq, hr⟩))⟩⟩

lemma and_or_iff_and {p q r : Prop} : (p ∧ (q ∨ r) ↔ p ∧ r) ↔ (p → q → r) :=
  ⟨fun h hp hq => (h.mp ⟨hp, Or.inl hq⟩).2,
   fun h => ⟨fun h' => ⟨h'.1, h'.2.elim (h h'.1) id⟩, And.imp id Or.inr⟩⟩

lemma or_not_iff (p q : Prop) [Decidable q] : (p ∨ ¬q) ↔ (q → p) := by
  rw [imp_iff_not_or, or_comm]

lemma eq_iff_eq_of_eq_left {α} {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]

lemma eq_iff_eq_of_eq_right {α} {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

/-! ## PFun extensions (src lines 162-543)

    In Lean 4, `pfun` is `PFun` in Mathlib. Key mappings:
    - `pfun.dom` → `PFun.Dom`
    - `pfun.fn` → `PFun.fn`
    - `pfun.ran` → `PFun.ran`

    Many lemmas from the Lean 3 `pfun` namespace are not in Mathlib 4.
    We define them here using the `CPFun` prefix to avoid clashes,
    and avoid defining type class instances on `α →. β` directly. -/

namespace CPFun

attribute [local instance] Classical.propDecidable

variable {ι : Sort*} {α : Type*} {β : Type*}

/-! ### Domain / function basics (src 166-197) -/

lemma mem_Dom_iff (f : α →. β) (x : α) : x ∈ PFun.Dom f ↔ (f x).Dom := by
  simp [PFun.Dom]

lemma mem_Dom_of_mem {f : α →. β} {x : α} {y : β} (h : y ∈ f x) : x ∈ PFun.Dom f :=
  (PFun.mem_dom f x).mpr ⟨y, h⟩

/-- `Part.some (f.fn x h) = f x` -/
lemma some_fn {f : α →. β} {x : α} (h : x ∈ PFun.Dom f) :
    Part.some (PFun.fn f x h) = f x :=
  Part.some_get h

/-- `f.fn x h ∈ f x` -/
lemma fn_mem {f : α →. β} {x : α} (h : x ∈ PFun.Dom f) : PFun.fn f x h ∈ f x :=
  Part.get_mem h

/-- `y ∈ f x ↔ ∃ h : x ∈ Dom f, f.fn x h = y` -/
lemma mem_iff_fn_eq {f : α →. β} {x : α} {y : β} :
    y ∈ f x ↔ ∃ h : x ∈ PFun.Dom f, PFun.fn f x h = y := by
  simp only [PFun.Dom, Set.mem_setOf_eq, PFun.fn_apply]
  exact ⟨fun h => ⟨h.fst, (Part.get_eq_iff_mem h.fst).mpr h⟩,
         fun ⟨hd, heq⟩ => heq ▸ Part.get_mem hd⟩

/-- `f.fn x h = y ↔ y ∈ f x` -/
lemma fn_eq_iff_mem {f : α →. β} {x : α} {y : β} (h : x ∈ PFun.Dom f) :
    PFun.fn f x h = y ↔ y ∈ f x :=
  ⟨fun heq => heq ▸ fn_mem h, fun hy => Part.mem_unique (fn_mem h) hy⟩

/-- `fn_eq_of_mem: if y ∈ f x and h₂ : x ∈ Dom f, then f.fn x h₂ = y` -/
lemma fn_eq_of_mem {f : α →. β} {x : α} {y : β} (h1 : y ∈ f x) (h2 : x ∈ PFun.Dom f) :
    PFun.fn f x h2 = y :=
  (fn_eq_iff_mem h2).mpr h1

/-- `y ∈ (↑f : α →. β) x ↔ f x = y` -/
lemma mem_lift {f : α → β} {x : α} {y : β} : y ∈ (f : α →. β) x ↔ f x = y := by
  simp [eq_comm]

lemma lift_eq_some_iff {f : α → β} {x : α} {y : β} :
    (f : α →. β) x = Part.some y ↔ f x = y := by simp

@[simp] lemma fn_lift (f : α → β) (x : α) :
    (f : α →. β).fn x trivial = f x := by
  simp [PFun.fn_apply, PFun.coe_val]

/-! ### Empty partial function (src 199-203) -/

/-- The empty partial function -/
def empty : α →. β := fun _ => Part.none

@[simp] lemma dom_empty : PFun.Dom (empty : α →. β) = ∅ := by
  simp [PFun.Dom, empty]

@[simp] lemma empty_def (x : α) : (empty : α →. β) x = Part.none := rfl

lemma not_mem_empty (x : α) (y : β) : y ∉ (empty : α →. β) x := Part.notMem_none _

/-! ### Subfun / le order on PFun (src 287-321) -/

/-- f₁ ≤ f₂ (subfun): ∀ x y, y ∈ f₁ x → y ∈ f₂ x -/
def le (f₁ f₂ : α →. β) : Prop := ∀ x y, y ∈ f₁ x → y ∈ f₂ x

@[refl] lemma le_refl (f : α →. β) : le f f := fun _ _ h => h

lemma le_trans {f g h : α →. β} : le f g → le g h → le f h :=
  fun hfg hgh x y hy => hgh x y (hfg x y hy)

lemma le_antisymm {f g : α →. β} (h1 : le f g) (h2 : le g f) : f = g :=
  PFun.ext (fun x y => ⟨h1 x y, h2 x y⟩)

lemma dom_subset_dom_of_le {f₁ f₂ : α →. β} (h : le f₁ f₂) :
    PFun.Dom f₁ ⊆ PFun.Dom f₂ :=
  fun x hx => mem_Dom_of_mem (h x (PFun.fn f₁ x hx) (fn_mem hx))

lemma fn_eq_of_le {f₁ f₂ : α →. β} (h : le f₁ f₂) {x : α} {y : β}
    (h1 : x ∈ PFun.Dom f₁) (h2 : PFun.fn f₁ x h1 = y) (h3 : x ∈ PFun.Dom f₂) :
    PFun.fn f₂ x h3 = y := by
  apply fn_eq_of_mem; apply h; rw [mem_iff_fn_eq]; exact ⟨h1, h2⟩

lemma le_lift {f : α →. β} {g : α → β} :
    le f (g : α →. β) ↔ ∀ x y, y ∈ f x → g x = y := by
  simp [le, eq_comm]

/-! ### Compatible (src 324-345) -/

/-- Two functions are compatible if they agree on the intersection of their domains. -/
def compatible (f₁ f₂ : α →. β) : Prop :=
  ∀ (x : α), x ∈ PFun.Dom f₁ → x ∈ PFun.Dom f₂ → f₁ x = f₂ x

lemma compatible_def {f₁ f₂ : α →. β} :
    compatible f₁ f₂ ↔ ∀ (x : α), x ∈ PFun.Dom f₁ → x ∈ PFun.Dom f₂ → f₁ x = f₂ x :=
  Iff.rfl

lemma mem_of_compatible {f₁ f₂ : α →. β} (h : compatible f₁ f₂) {x : α} {y : β}
    (h1 : y ∈ f₁ x) (h2 : x ∈ PFun.Dom f₂) : y ∈ f₂ x := by
  have heq := h x (mem_Dom_of_mem h1) h2
  rw [← heq]; exact h1

@[refl] lemma compatible_refl {f : α →. β} : compatible f f := fun _ _ _ => rfl

lemma compatible_comm {f₁ f₂ : α →. β} : compatible f₁ f₂ ↔ compatible f₂ f₁ := by
  simp only [compatible]
  constructor <;> (intro h x h1 h2; exact (h x h2 h1).symm)

lemma compatible_of_le {f₁ f₂ : α →. β} (h : le f₁ f₂) : compatible f₁ f₂ := by
  intro x h1x h2x
  apply Part.ext; intro y; constructor
  · intro hy; exact h x y hy
  · intro hy
    have hstep := h x (PFun.fn f₁ x h1x) (fn_mem h1x)
    have hmem : PFun.fn f₁ x h1x ∈ f₂ x := hstep
    have heq : y = PFun.fn f₁ x h1x := Part.mem_unique hy hmem
    rw [heq]; exact fn_mem h1x

/-! ### Intersection on PFun (src 278-284) -/

/-- The intersection of two partial functions: f₁ ∩ f₂.
    Domain: ∃ y, y ∈ f₁ x ∧ y ∈ f₂ x. Value: f₁(x). -/
noncomputable def pfunInter (f₁ f₂ : α →. β) : α →. β :=
  fun x => ⟨∃ y, y ∈ f₁ x ∧ y ∈ f₂ x,
            fun h => PFun.fn f₁ x (mem_Dom_of_mem (Classical.choose_spec h).1)⟩

@[simp] lemma mem_pfunInter {f₁ f₂ : α →. β} {x : α} {y : β} :
    y ∈ pfunInter f₁ f₂ x ↔ y ∈ f₁ x ∧ y ∈ f₂ x := by
  simp only [pfunInter, Part.mem_eq]
  constructor
  · rintro ⟨hex, rfl⟩
    -- hex : ∃ z, z ∈ f₁ x ∧ z ∈ f₂ x
    -- the Part.get value is PFun.fn f₁ x (mem_Dom_of_mem (Classical.choose_spec hex).1)
    have hcs := Classical.choose_spec hex
    have hd' : x ∈ PFun.Dom f₁ := mem_Dom_of_mem hcs.1
    constructor
    · exact fn_mem hd'
    · have hveq : PFun.fn f₁ x hd' = Classical.choose hex :=
        fn_eq_of_mem hcs.1 hd'
      rw [hveq]; exact hcs.2
  · rintro ⟨hy1, hy2⟩
    refine ⟨⟨y, hy1, hy2⟩, ?_⟩
    apply fn_eq_of_mem hy1

lemma pfunInter_le_left {f₁ f₂ : α →. β} : le (pfunInter f₁ f₂) f₁ :=
  fun x y hy => (mem_pfunInter.mp hy).1

lemma pfunInter_le_right {f₁ f₂ : α →. β} : le (pfunInter f₁ f₂) f₂ :=
  fun x y hy => (mem_pfunInter.mp hy).2

lemma le_pfunInter {f g₁ g₂ : α →. β} (h1 : le f g₁) (h2 : le f g₂) :
    le f (pfunInter g₁ g₂) :=
  fun x y hy => mem_pfunInter.mpr ⟨h1 x y hy, h2 x y hy⟩

/-! ### Sup on PFun (src 351-400) -/

/-- The sup of f₁ and f₂: f₁ x if x ∈ Dom f₁, else f₂ x. -/
noncomputable def pfunSup (f₁ f₂ : α →. β) : α →. β :=
  fun a => if h : a ∈ PFun.Dom f₁ then f₁ a else f₂ a

lemma pfunSup_eq_of_mem {f₁ f₂ : α →. β} {x : α} (h : x ∈ PFun.Dom f₁) :
    pfunSup f₁ f₂ x = f₁ x := by
  simp only [pfunSup, dif_pos h]

lemma pfunSup_eq_of_nmem {f₁ f₂ : α →. β} {x : α} (h : x ∉ PFun.Dom f₁) :
    pfunSup f₁ f₂ x = f₂ x := by
  simp only [pfunSup, dif_neg h]

@[simp] lemma dom_pfunSup (f₁ f₂ : α →. β) :
    PFun.Dom (pfunSup f₁ f₂) = PFun.Dom f₁ ∪ PFun.Dom f₂ := by
  ext x
  simp only [PFun.Dom, Set.mem_setOf_eq, Set.mem_union]
  by_cases hx : x ∈ PFun.Dom f₁
  · simp only [pfunSup_eq_of_mem hx]; exact ⟨fun h => Or.inl hx, fun _ => hx⟩
  · simp only [pfunSup_eq_of_nmem hx]
    exact ⟨fun h => Or.inr (mem_Dom_of_mem (Part.get_mem h)),
           fun h => h.elim (absurd · hx) id⟩

lemma subset_dom_pfunSup_left (f₁ f₂ : α →. β) : PFun.Dom f₁ ⊆ PFun.Dom (pfunSup f₁ f₂) := by
  intro x hx; rw [dom_pfunSup]; exact Set.mem_union_left _ hx

lemma subset_dom_pfunSup_right (f₁ f₂ : α →. β) : PFun.Dom f₂ ⊆ PFun.Dom (pfunSup f₁ f₂) := by
  intro x hx; rw [dom_pfunSup]; exact Set.mem_union_right _ hx

lemma mem_pfunSup {f₁ f₂ : α →. β} {x : α} {y : β} :
    y ∈ pfunSup f₁ f₂ x ↔ y ∈ f₁ x ∨ (y ∈ f₂ x ∧ x ∉ PFun.Dom f₁) := by
  by_cases hx : x ∈ PFun.Dom f₁
  · rw [pfunSup_eq_of_mem hx]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨_, hnx⟩)
      · exact h
      · exact absurd hx hnx
  · rw [pfunSup_eq_of_nmem hx]
    constructor
    · intro h; exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨h2, _⟩)
      · exact absurd (mem_Dom_of_mem h) hx
      · exact h2

lemma mem_pfunSup_of_compatible {f₁ f₂ : α →. β} {x : α} {y : β}
    (h : compatible f₁ f₂) :
    y ∈ pfunSup f₁ f₂ x ↔ y ∈ f₁ x ∨ y ∈ f₂ x := by
  rw [mem_pfunSup]
  constructor
  · rintro (h1 | ⟨h2, _⟩)
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro (h1 | h2)
    · exact Or.inl h1
    · by_cases hx : x ∈ PFun.Dom f₁
      · left
        have heq := h x hx (mem_Dom_of_mem h2)
        -- heq : f₁ x = f₂ x, so y ∈ f₁ x follows from y ∈ f₂ x and heq
        rw [heq]; exact h2
      · exact Or.inr ⟨h2, hx⟩

lemma le_pfunSup_left (f₁ f₂ : α →. β) : le f₁ (pfunSup f₁ f₂) :=
  fun x y hy => by rw [mem_pfunSup]; exact Or.inl hy

lemma le_pfunSup_right {f₁ f₂ : α →. β} (h : compatible f₁ f₂) : le f₂ (pfunSup f₁ f₂) :=
  fun x y hy => by rw [mem_pfunSup_of_compatible h]; exact Or.inr hy

lemma pfunSup_restrict_left {f₁ f₂ : α →. β} :
    (pfunSup f₁ f₂).restrict (subset_dom_pfunSup_left f₁ f₂) = f₁ := by
  apply PFun.ext; intro x y
  simp only [PFun.mem_restrict, mem_pfunSup]
  constructor
  · rintro ⟨hx, h1 | ⟨_, hnx⟩⟩
    · exact h1
    · exact absurd hx hnx
  · intro hy
    exact ⟨mem_Dom_of_mem hy, Or.inl hy⟩

lemma pfunSup_restrict_right {f₁ f₂ : α →. β} (h : compatible f₁ f₂) :
    (pfunSup f₁ f₂).restrict (subset_dom_pfunSup_right f₁ f₂) = f₂ := by
  apply PFun.ext; intro x y
  simp only [PFun.mem_restrict, mem_pfunSup_of_compatible h]
  constructor
  · rintro ⟨hx, h1 | h2⟩
    · rw [← h x (mem_Dom_of_mem h1) hx]; exact h1
    · exact h2
  · intro hy
    exact ⟨mem_Dom_of_mem hy, Or.inr hy⟩

/-! ### Indexed Sup on PFun (src 405-450) -/

/-- The indexed sup of a family of partial functions. Uses Classical.choose. -/
noncomputable def pSup {ι : Type*} (f : ι → α →. β) : α →. β :=
  fun x => if h : ∃ i, x ∈ PFun.Dom (f i)
           then f (Classical.choose h) x
           else Part.none

lemma pSup_helper {ι : Type*} {f : ι → α →. β} {x : α} :
    (∃ i, x ∈ PFun.Dom (f i)) ↔
    (∃ i, x ∈ PFun.Dom (f i) ∧ pSup f x = f i x) :=
  ⟨fun h => ⟨Classical.choose h, Classical.choose_spec h, dif_pos h⟩,
   fun ⟨i, h, _⟩ => ⟨i, h⟩⟩

lemma pSup_helper2 {ι : Type*} {f : ι → α →. β} {x : α} :
    (∃ i, x ∈ PFun.Dom (f i)) ↔
    (∃ i, ∃ h : x ∈ PFun.Dom (f i), pSup f x = Part.some (PFun.fn (f i) x h)) := by
  rw [pSup_helper]
  apply exists_congr; intro i
  rw [← exists_prop]
  apply exists_congr; intro hi
  apply eq_iff_eq_of_eq_right
  exact (some_fn hi).symm

@[simp] lemma dom_pSup {ι : Type*} (f : ι → α →. β) :
    PFun.Dom (pSup f) = ⋃ (i : ι), PFun.Dom (f i) := by
  ext x
  simp only [PFun.Dom, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hx
    -- (pSup f x).Dom
    by_cases hex : ∃ i, x ∈ PFun.Dom (f i)
    · -- pSup f x = f (Classical.choose hex) x
      have key : pSup f x = f (Classical.choose hex) x := dif_pos hex
      rw [key] at hx
      exact ⟨Classical.choose hex, mem_Dom_of_mem (Part.get_mem hx)⟩
    · exfalso
      have hkey : pSup f x = Part.none := by simp only [pSup, dif_neg hex]
      rw [hkey] at hx; exact hx
  · rintro ⟨i, hi⟩
    have hex : ∃ j, x ∈ PFun.Dom (f j) := ⟨i, hi⟩
    have key : pSup f x = f (Classical.choose hex) x := dif_pos hex
    rw [key]
    exact Classical.choose_spec hex

lemma subset_dom_pSup {ι : Type*} (f : ι → α →. β) (i : ι) :
    PFun.Dom (f i) ⊆ PFun.Dom (pSup f) := by
  intro x hx
  simp only [dom_pSup, Set.mem_iUnion]
  exact ⟨i, hx⟩

lemma pSup_eq_of_mem {ι : Type*} {f : ι → α →. β} {x : α} {i : ι}
    (hf : ∀ i j, compatible (f i) (f j)) (h : x ∈ PFun.Dom (f i)) :
    pSup f x = f i x := by
  have hex : ∃ i, x ∈ PFun.Dom (f i) := ⟨i, h⟩
  obtain ⟨j, hj, h2j⟩ := pSup_helper.mp hex
  rw [h2j]; exact hf j i x hj h

lemma pSup_eq_of_nmem {ι : Type*} {f : ι → α →. β} {x : α}
    (h : ∀ i, x ∉ PFun.Dom (f i)) :
    pSup f x = Part.none := by
  have hne : ¬∃ i, x ∈ PFun.Dom (f i) := fun ⟨i, hi⟩ => h i hi
  simp only [pSup, dif_neg hne]

/-- mem_pSup: port of pfun.mem_Sup (src lines 444-451). -/
lemma mem_pSup {ι : Type*} {f : ι → α →. β} {x : α} {y : β}
    (hf : ∀ i j, compatible (f i) (f j)) :
    y ∈ pSup f x ↔ ∃ i, y ∈ f i x := by
  constructor
  · intro hy
    have := mem_Dom_of_mem hy
    rw [dom_pSup, Set.mem_iUnion] at this
    rcases this with ⟨i, hi⟩
    exact ⟨i, by rwa [pSup_eq_of_mem hf hi] at hy⟩
  · rintro ⟨i, hi⟩
    rwa [pSup_eq_of_mem hf (mem_Dom_of_mem hi)]

end CPFun

end Flypitch
