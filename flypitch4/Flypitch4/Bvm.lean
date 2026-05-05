/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/bvm.lean lines 1-700 — Task 10a -/

import Flypitch4.PSetOrdinal
import Flypitch4.BvTauto
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Zorn

open scoped Flypitch

/-! ## Namespace Lattice — natural deduction lemmas in BA -/

namespace Lattice

section natded
variable {𝔹 : Type*} [CompleteBooleanAlgebra 𝔹]

-- src/bvm.lean:21
lemma supr_imp_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
    (⨆ (i : ι), s i) ⟹ b = ⨅ (i : ι), s i ⟹ b := by
  unfold imp; rw [compl_iSup, iInf_sup_eq']

-- src/bvm.lean:25
lemma imp_infi_eq {ι : Type*} {s : ι → 𝔹} {b : 𝔹} :
    (b ⟹ (⨅ i, s i)) = ⨅ i, b ⟹ s i := by
  unfold imp; rw [sup_iInf_eq']

-- src/bvm.lean:29
lemma bv_Or_elim {ι : Type*} {s : ι → 𝔹} {c : 𝔹}
    (H : ∀ i : ι, s i ≤ c) : (⨆ (i : ι), s i) ≤ c :=
  iSup_le H

-- src/bvm.lean:33
lemma bv_And_intro {ι : Type*} {s : ι → 𝔹} {c : 𝔹}
    (H : ∀ i : ι, c ≤ s i) : c ≤ ⨅ (i : ι), s i :=
  le_iInf H

-- src/bvm.lean:37
lemma bv_or_elim {b₁ b₂ c : 𝔹} (h : b₁ ≤ c) (h' : b₂ ≤ c) : b₁ ⊔ b₂ ≤ c :=
  sup_le h h'

-- src/bvm.lean:40
lemma bv_or_elim_left {b₁ b₂ c d : 𝔹} (h₁ : b₁ ⊓ d ≤ c) (h₂ : b₂ ⊓ d ≤ c) :
    (b₁ ⊔ b₂) ⊓ d ≤ c := by
  rw [deduction]; apply sup_le <;> rw [← deduction] <;> assumption

-- src/bvm.lean:43
lemma bv_or_elim_right {b₁ b₂ c d : 𝔹} (h₁ : d ⊓ b₁ ≤ c) (h₂ : d ⊓ b₂ ≤ c) :
    d ⊓ (b₁ ⊔ b₂) ≤ c := by
  rw [inf_comm]; rw [inf_comm] at h₁ h₂; exact bv_or_elim_left h₁ h₂

-- src/bvm.lean:46
lemma bv_exfalso {a b : 𝔹} (h : a ≤ ⊥) : a ≤ b :=
  le_trans h bot_le

-- src/bvm.lean:49
lemma bv_cases_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, s i ⊓ c ≤ b) :
    ((⨆ (i : ι), s i) ⊓ c) ≤ b := by
  rw [deduction]; apply iSup_le; intro i; rw [← deduction]; exact h i

-- src/bvm.lean:53
lemma bv_cases_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (h : ∀ i : ι, c ⊓ s i ≤ b) :
    (c ⊓ (⨆ (i : ι), s i)) ≤ b := by
  rw [inf_comm]; exact bv_cases_left (fun i => by rw [inf_comm]; exact h i)

-- src/bvm.lean:57
lemma bv_specialize {ι : Type*} {s : ι → 𝔹} (i : ι) {b : 𝔹} (h : s i ≤ b) :
    (⨅ (i : ι), s i) ≤ b :=
  iInf_le_of_le i h

-- src/bvm.lean:61
lemma bv_specialize_twice {ι : Type*} {s : ι → 𝔹} (i j : ι) {b : 𝔹}
    (h : s i ⊓ s j ≤ b) : (⨅ (i : ι), s i) ≤ b :=
  calc (⨅ k, s k) ≤ s i ⊓ s j := le_inf (iInf_le _ i) (iInf_le _ j)
    _ ≤ b := h

-- src/bvm.lean:68
lemma bv_specialize_left {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
    (h : s i ⊓ c ≤ b) : (⨅ (i : ι), s i) ⊓ c ≤ b := by
  rw [deduction]; exact bv_specialize i (by rwa [← deduction])

-- src/bvm.lean:72
lemma bv_specialize_left_twice {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i j : ι)
    (h : s i ⊓ s j ⊓ c ≤ b) : (⨅ (i : ι), s i) ⊓ c ≤ b := by
  rw [deduction]; exact bv_specialize_twice i j (by rwa [← deduction])

-- src/bvm.lean:78
lemma bv_specialize_right {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i : ι)
    (h : c ⊓ s i ≤ b) : c ⊓ (⨅ (i : ι), s i) ≤ b := by
  rw [inf_comm]; exact bv_specialize_left i (by rwa [inf_comm])

-- src/bvm.lean:82
lemma bv_specialize_right_twice {ι : Type*} {s : ι → 𝔹} {c b : 𝔹} (i j : ι)
    (h : c ⊓ (s i ⊓ s j) ≤ b) : c ⊓ (⨅ (i : ι), s i) ≤ b := by
  rw [inf_comm]; exact bv_specialize_left_twice i j (by rwa [← inf_comm])

-- src/bvm.lean:88
lemma bv_imp_elim {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ b := imp_inf_le a b

-- src/bvm.lean:91
lemma bv_imp_elim' {a b : 𝔹} : (a ⟹ b) ⊓ a ≤ a ⊓ b :=
  le_inf inf_le_right bv_imp_elim

-- src/bvm.lean:94
lemma bv_cancel_antecedent {a b c : 𝔹} (h : b ≤ c) : a ⟹ b ≤ a ⟹ c := by
  rw [← deduction]; exact le_trans bv_imp_elim h

-- src/bvm.lean:97
lemma bv_imp_iff {Γ b₁ b₂ : 𝔹} :
    Γ ≤ b₁ ⟹ b₂ ↔ (∀ {Γ' : 𝔹}, Γ' ≤ Γ → Γ' ≤ b₁ → Γ' ≤ b₂) := by
  constructor
  · intro H Γ' H_le H'
    rw [← deduction] at H
    exact le_trans (le_inf H_le H') H
  · intro H
    rw [← deduction]; exact H inf_le_left inf_le_right

-- src/bvm.lean:107
lemma bv_biimp_iff {b₁ b₂ : 𝔹} {Γ : 𝔹} :
    (Γ ≤ (b₁ ⇔ b₂)) ↔ (∀ {Γ' : 𝔹}, Γ' ≤ Γ → (Γ' ≤ b₁ ↔ Γ' ≤ b₂)) := by
  constructor
  · intro H
    have Hmp : Γ ≤ b₁ ⟹ b₂ := le_trans H inf_le_left
    have Hmpr : Γ ≤ b₂ ⟹ b₁ := le_trans H inf_le_right
    intro Γ' H_le
    exact ⟨bv_imp_iff.mp Hmp H_le, bv_imp_iff.mp Hmpr H_le⟩
  · intro H
    apply le_inf
    · rw [bv_imp_iff]; exact fun H_le H' => (H H_le).mp H'
    · rw [bv_imp_iff]; exact fun H_le H' => (H H_le).mpr H'

-- src/bvm.lean:122
lemma bv_and_intro {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) : a ≤ b₁ ⊓ b₂ :=
  le_inf h₁ h₂

-- src/bvm.lean:124
lemma bv_or_left {a b₁ b₂ : 𝔹} (h₁ : a ≤ b₁) : a ≤ b₁ ⊔ b₂ :=
  le_trans h₁ le_sup_left

-- src/bvm.lean:126
lemma bv_or_right {a b₁ b₂ : 𝔹} (h₂ : a ≤ b₂) : a ≤ b₁ ⊔ b₂ :=
  le_trans h₂ le_sup_right

-- src/bvm.lean:128 (bv_and.left → bv_and_left)
lemma bv_and_left {a b : 𝔹} {Γ : 𝔹} (H : Γ ≤ a ⊓ b) : Γ ≤ a :=
  le_trans H inf_le_left

-- src/bvm.lean:131 (bv_and.right → bv_and_right)
lemma bv_and_right {a b : 𝔹} {Γ : 𝔹} (H : Γ ≤ a ⊓ b) : Γ ≤ b :=
  le_trans H inf_le_right

-- src/bvm.lean:134
lemma from_empty_context {a b : 𝔹} (h : ⊤ ≤ b) : a ≤ b :=
  le_trans le_top h

-- src/bvm.lean:137
lemma bv_imp_intro_lemma {a b c : 𝔹} (h : a ⊓ b ≤ c) : a ≤ b ⟹ c := by
  rwa [deduction] at h

-- src/bvm.lean:140
lemma bv_have {a b c : 𝔹} (h : a ≤ b) (h' : a ⊓ b ≤ c) : a ≤ c :=
  le_trans (le_inf le_rfl h) h'

-- src/bvm.lean:143
lemma bv_have_true {a b c : 𝔹} (h₁ : ⊤ ≤ b) (h₂ : a ⊓ b ≤ c) : a ≤ c := by
  have hb : b = ⊤ := le_antisymm le_top h₁
  rw [hb, inf_top_eq] at h₂; exact h₂

-- src/bvm.lean:146
lemma bv_use {ι} (i : ι) {s : ι → 𝔹} {b : 𝔹} (h : b ≤ s i) : b ≤ ⨆ (j : ι), s j :=
  le_trans h (le_iSup _ i)

-- src/bvm.lean:149
lemma bv_context_apply {β : Type*} [CompleteBooleanAlgebra β] {Γ a₁ a₂ : β}
    (h₁ : Γ ≤ a₁ ⟹ a₂) (h₂ : Γ ≤ a₁) : Γ ≤ a₂ :=
  context_imp_elim h₁ h₂

-- src/bvm.lean:152
lemma bv_Or_imp {Γ : 𝔹} {ι} {ϕ₁ ϕ₂ : ι → 𝔹} (H_sub : Γ ≤ ⨅ x, ϕ₁ x ⟹ ϕ₂ x)
    (H : Γ ≤ ⨆ x, ϕ₁ x) : Γ ≤ ⨆ x, ϕ₂ x := by
  sorry -- TODO: port from src/bvm.lean:152-153 (uses bv_cases_at which is a deferred tactic)

-- src/bvm.lean:155
lemma bv_iff_neg {b₁ b₂ : 𝔹} (H : ∀ {Γ : 𝔹}, Γ ≤ b₁ ↔ Γ ≤ b₂) :
    ∀ {Γ : 𝔹}, Γ ≤ b₁ᶜ ↔ Γ ≤ b₂ᶜ := by
  intro Γ
  simp only [← imp_bot]
  have h12 : b₁ ≤ b₂ := (H (Γ := b₁)).mp le_rfl
  have h21 : b₂ ≤ b₁ := (H (Γ := b₂)).mpr le_rfl
  exact ⟨fun h => le_trans h (imp_le_of_left_le (h := h21)),
         fun h => le_trans h (imp_le_of_left_le (h := h12))⟩

end natded
end Lattice

open Lattice

universe u

/-! ## pSet namespace — small additions -/

namespace PSet

-- src/bvm.lean:173-184
/-- If two pre-sets `x` and `y` are not equivalent, then either there exists a member of x
which is not equivalent to any member of y, or there exists a member of y which is not
equivalent to any member of x -/
lemma not_equiv {x y : PSet} (h_neq : ¬ PSet.Equiv x y) :
    (∃ a : x.Type, ∀ a' : y.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) ∨
    (∃ a' : y.Type, ∀ a : x.Type, ¬ PSet.Equiv (x.Func a) (y.Func a')) := by
  rw [PSet.equiv_iff] at h_neq
  by_cases hleft : ∀ i : x.Type, ∃ j : y.Type, PSet.Equiv (x.Func i) (y.Func j)
  · right
    have hright : ¬ ∀ j : y.Type, ∃ i : x.Type, PSet.Equiv (x.Func i) (y.Func j) := by
      intro hright; exact h_neq ⟨hleft, hright⟩
    simp only [not_forall, not_exists] at hright
    obtain ⟨a', ha'⟩ := hright
    exact ⟨a', ha'⟩
  · left
    simp only [not_forall, not_exists] at hleft
    obtain ⟨a, ha⟩ := hleft
    exact ⟨a, ha⟩

end PSet

/-! ## bSet — boolean-valued model of ZFC -/

-- τ is a B-name if and only if τ is a set of pairs of the form ⟨σ, b⟩, where σ is
-- a B-name and b ∈ B.
inductive bSet (𝔹 : Type u) [CompleteBooleanAlgebra 𝔹] : Type (u + 1)
  | mk (α : Type u) (A : α → bSet 𝔹) (B : α → 𝔹) : bSet 𝔹

namespace bSet

open scoped Flypitch

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

noncomputable instance decidable_eq_𝔹 : DecidableEq 𝔹 :=
  fun _ _ => Classical.propDecidable _

-- src/bvm.lean:203
/-- The underlying type of a bSet -/
@[simp] def type : bSet 𝔹 → Type u
  | ⟨α, _, _⟩ => α

-- src/bvm.lean:206
@[simp] lemma type_iInf {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {C : α → 𝔹} :
    (⨅ (a : (mk α A B).type), C a) = ⨅ (a : α), C a := rfl

-- src/bvm.lean:208
@[simp] lemma type_iSup {α : Type u} {A : α → bSet 𝔹} {B : α → 𝔹} {C : α → 𝔹} :
    (⨆ (a : (mk α A B).type), C a) = ⨆ (a : α), C a := rfl

-- src/bvm.lean:211
/-- The indexing function of a bSet -/
@[simp] def func : ∀ x : bSet 𝔹, x.type → bSet 𝔹
  | ⟨_, A, _⟩ => A

-- src/bvm.lean:215
/-- The boolean truth-value function of a bSet -/
@[simp] def bval : ∀ x : bSet 𝔹, x.type → 𝔹
  | ⟨_, _, B⟩ => B

-- src/bvm.lean:218
@[simp] def mk_type_func_bval : ∀ x : bSet 𝔹, mk x.type x.func x.bval = x :=
  fun x => by cases x; rfl

-- src/bvm.lean:221
def empty : bSet 𝔹 :=
  ⟨ULift Empty, (ULift.down · |>.elim), (ULift.down · |>.elim)⟩

instance nonempty_bSet : Nonempty (@bSet 𝔹 _) := ⟨empty⟩

instance has_empty_bSet : EmptyCollection (bSet 𝔹) := ⟨empty⟩

-- src/bvm.lean:229
@[simp] lemma forall_over_empty (ϕ : (empty : bSet 𝔹).type → 𝔹) : (⨅ a, ϕ a) = ⊤ := by
  apply top_unique; apply le_iInf; intro a; exact a.down.elim

-- src/bvm.lean:232
@[simp] lemma exists_over_empty (ϕ : (empty : bSet 𝔹).type → 𝔹) : (⨆ a, ϕ a) = ⊥ := by
  apply bot_unique; apply iSup_le; intro i; exact i.down.elim

-- src/bvm.lean:238
/-- Two Boolean-valued pre-sets are extensionally equivalent if every
element of the first family is extensionally equivalent to
  some element of the second family and vice-versa. -/
def bv_eq : ∀ (x y : bSet 𝔹), 𝔹
  | ⟨α, A, B⟩, ⟨α', A', B'⟩ =>
    (⨅ a : α, B a ⟹ ⨆ a', B' a' ⊓ bv_eq (A a) (A' a')) ⊓
    (⨅ a' : α', B' a' ⟹ ⨆ a, B a ⊓ bv_eq (A a) (A' a'))

scoped infixl:79 " =ᴮ " => bv_eq

def bv_eq' (Γ : 𝔹) : bSet 𝔹 → bSet 𝔹 → Prop := fun x y => Γ ≤ x =ᴮ y

-- src/bvm.lean:255
@[simp] theorem bv_eq_refl : ∀ x : bSet 𝔹, x =ᴮ x = ⊤ := by
  intro x
  induction x with
  | mk α A B ih =>
    simp only [bv_eq, inf_eq_top_iff, iInf_eq_top]
    constructor
    all_goals intro i
    all_goals rw [imp_top_iff_le]
    all_goals exact le_iSup_of_le i (le_inf le_rfl (ih i ▸ le_top))

@[simp] lemma bv_refl {Γ : 𝔹} {x : bSet 𝔹} : Γ ≤ x =ᴮ x :=
  le_trans le_top (by simp)

@[simp] lemma bv_eq_top_of_eq {x y : bSet 𝔹} (h_eq : x = y) : x =ᴮ y = ⊤ := by
  subst h_eq; simp

-- src/bvm.lean:269
@[reducible] def empty' : bSet 𝔹 := mk PUnit (fun _ => ∅) (fun _ => ⊥)

-- src/bvm.lean:278
/-- `x ∈ y` as Boolean-valued pre-sets if `x` is extensionally equivalent to a member
  of the family `y`. -/
def mem : bSet 𝔹 → bSet 𝔹 → 𝔹
  | a, ⟨α', A', B'⟩ => ⨆ a', B' a' ⊓ a =ᴮ A' a'

-- src/bvm.lean:281
@[reducible] def empty'' : bSet 𝔹 :=
  mk (ULift Bool) (fun _ => ∅) fun x =>
    match x.down with
    | false => ⊥
    | true => ⊤

scoped infixl:80 " ∈ᴮ " => mem

-- src/bvm.lean:286
lemma mem_unfold {u v : bSet 𝔹} : u ∈ᴮ v = ⨆ (i : v.type), v.bval i ⊓ u =ᴮ v.func i := by
  cases v; simp [mem, bv_eq]

-- src/bvm.lean:295
theorem mem_mk {α : Type u} (A : α → bSet 𝔹) (B : α → 𝔹) (a : α) :
    B a ≤ A a ∈ᴮ mk α A B :=
  le_iSup_of_le a (by simp)

-- src/bvm.lean:298
theorem mem_mk' (x : bSet 𝔹) (a : x.type) : x.bval a ≤ x.func a ∈ᴮ x := by
  cases x; exact mem_mk _ _ _

-- src/bvm.lean:302
@[simp] theorem mem_mk'' {x : bSet 𝔹} {a : x.type} {Γ : 𝔹} :
    Γ ≤ x.bval a → Γ ≤ x.func a ∈ᴮ x :=
  poset_yoneda_inv Γ (mem_mk' x a)

-- src/bvm.lean:305
@[reducible] protected def subset : bSet 𝔹 → bSet 𝔹 → 𝔹
  | ⟨α, A, B⟩, b => ⨅ a : α, B a ⟹ (A a ∈ᴮ b)

scoped infixl:80 " ⊆ᴮ " => bSet.subset

-- src/bvm.lean:310
lemma subset_unfold {x u : bSet 𝔹} :
    x ⊆ᴮ u = (⨅ (j : x.type), x.bval j ⟹ x.func j ∈ᴮ u) := by
  cases x; simp [bSet.subset]

-- src/bvm.lean:313
@[simp] protected def insert : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, b, ⟨α, A, B⟩ => ⟨Option α, fun o => Option.rec u A o, fun o => Option.rec b B o⟩

-- src/bvm.lean:316
protected def insert' : bSet 𝔹 → 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, b, ⟨α, A, B⟩ => ⟨Unit ⊕ α, Sum.rec (fun _ => u) A, Sum.rec (fun _ => b) B⟩

-- src/bvm.lean:319
@[reducible] protected def insert1 : bSet 𝔹 → bSet 𝔹 → bSet 𝔹
  | u, v => bSet.insert u ⊤ v

-- src/bvm.lean:322
lemma insert1_unfold {u v : bSet 𝔹} :
    bSet.insert1 u v =
    ⟨Option v.type, fun o => Option.rec u v.func o, fun o => Option.rec ⊤ v.bval o⟩ := by
  cases v; simp [bSet.insert1, bSet.insert]

-- src/bvm.lean:328
instance insert_bSet : Insert (bSet 𝔹) (bSet 𝔹) :=
  ⟨fun u v => bSet.insert1 u v⟩

-- src/bvm.lean:331
@[simp] lemma insert_unfold {y z : bSet 𝔹} : insert y z = bSet.insert y ⊤ z := rfl

-- src/bvm.lean:334
@[simp] theorem mem_insert {x y z : bSet 𝔹} {b : 𝔹} :
    x ∈ᴮ bSet.insert y b z = (b ⊓ x =ᴮ y) ⊔ x ∈ᴮ z := by
  cases y; cases z
  simp only [bSet.insert, mem]
  rw [iSup_option]

-- src/bvm.lean:338
@[simp] theorem mem_insert1 {x y z : bSet 𝔹} : x ∈ᴮ insert y z = x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [insert_unfold, mem_insert, top_inf_eq]

-- src/bvm.lean:341
@[simp] theorem mem_insert1' {x y z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ x ∈ᴮ insert y z ↔ Γ ≤ x =ᴮ y ⊔ x ∈ᴮ z := by
  rw [mem_insert1]

-- src/bvm.lean:354
private def bv_eq_symm_aux : ∀ (x y : bSet 𝔹), x =ᴮ y = y =ᴮ x
  | ⟨α, A, B⟩, ⟨α', A', B'⟩ => by
    have : ∀ a a', A' a' =ᴮ A a = A a =ᴮ A' a' := fun a a' => (bv_eq_symm_aux (A a) (A' a')).symm
    simp only [bv_eq, this, inf_comm]

theorem bv_eq_symm {x y : bSet 𝔹} : x =ᴮ y = y =ᴮ x := bv_eq_symm_aux x y

-- src/bvm.lean:361
theorem bv_eq_unfold (x y : bSet 𝔹) :
    x =ᴮ y = (⨅ (a : x.type), x.bval a ⟹ (x.func a ∈ᴮ y))
            ⊓ (⨅ (a' : y.type), (y.bval a' ⟹ (y.func a' ∈ᴮ x))) := by
  cases x; cases y; simp [mem, bv_eq, bv_eq_symm]

-- src/bvm.lean:366
theorem bSet_axiom_of_extensionality (x y : bSet 𝔹) :
    (⨅ (z : bSet 𝔹), (z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (z ∈ᴮ y ⟹ z ∈ᴮ x)) ≤ x =ᴮ y := by
  rw [bv_eq_unfold]
  apply le_inf <;> apply le_iInf <;> intro i
  · apply iInf_le_of_le (x.func i)
    apply inf_le_left.trans
    apply imp_le_of_left_le
    cases x with | mk xα xA xB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i (le_inf le_rfl (by simp))
  · apply iInf_le_of_le (y.func i)
    apply inf_le_right.trans
    apply imp_le_of_left_le
    cases y with | mk yα yA yB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i (le_inf le_rfl (by simp))

-- src/bvm.lean:381
lemma eq_of_subset_subset (x y : bSet 𝔹) : x ⊆ᴮ y ⊓ y ⊆ᴮ x ≤ x =ᴮ y := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

-- src/bvm.lean:387
lemma subset_subset_of_eq (x y : bSet 𝔹) : x =ᴮ y ≤ x ⊆ᴮ y ⊓ y ⊆ᴮ x := by
  rw [bv_eq_unfold, subset_unfold, subset_unfold]

-- src/bvm.lean:393
theorem eq_iff_subset_subset {x y : bSet 𝔹} : x =ᴮ y = x ⊆ᴮ y ⊓ y ⊆ᴮ x :=
  le_antisymm (subset_subset_of_eq x y) (eq_of_subset_subset x y)

-- src/bvm.lean:396
lemma subset_subset_of_eq' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) :
    Γ ≤ x ⊆ᴮ y ∧ Γ ≤ y ⊆ᴮ x := by
  rw [eq_iff_subset_subset] at H
  exact ⟨le_trans H inf_le_left, le_trans H inf_le_right⟩

-- src/bvm.lean:399
lemma subset_of_eq {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) : Γ ≤ x ⊆ᴮ y :=
  (subset_subset_of_eq' H).left

-- src/bvm.lean:402
@[simp] lemma subset_self {x : bSet 𝔹} {Γ : 𝔹} : Γ ≤ x ⊆ᴮ x :=
  le_trans le_top (by rw [show ⊤ = x =ᴮ x by simp, eq_iff_subset_subset]; exact inf_le_left)

-- src/bvm.lean:406
theorem subset_ext {x y : bSet 𝔹} {Γ : 𝔹} (h₁ : Γ ≤ x ⊆ᴮ y) (h₂ : Γ ≤ y ⊆ᴮ x) :
    Γ ≤ x =ᴮ y := by
  rw [eq_iff_subset_subset]; exact le_inf h₁ h₂

-- src/bvm.lean:413
-- Complex induction using bv_intro patterns; sorry-stubbed for Task 10a
theorem bv_eq_trans {x y z : bSet 𝔹} : (x =ᴮ y ⊓ y =ᴮ z) ≤ x =ᴮ z := by
  sorry -- TODO: port from src/bvm.lean:413-470 (complex induction, bv_intro)

-- src/bvm.lean:472
lemma bv_trans {Γ : 𝔹} {a₁ a₂ a₃ : bSet 𝔹} (H₁ : Γ ≤ a₁ =ᴮ a₂) (H₂ : Γ ≤ a₂ =ᴮ a₃) :
    Γ ≤ a₁ =ᴮ a₃ :=
  le_trans (le_inf H₁ H₂) bv_eq_trans

-- src/bvm.lean:476
@[symm] lemma bv_symm {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) : Γ ≤ y =ᴮ x := by
  rwa [bv_eq_symm]

-- src/bvm.lean:478
lemma bv_rw {x y : bSet 𝔹} (H : x =ᴮ y = ⊤) (ϕ : bSet 𝔹 → 𝔹)
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} : ϕ y = ϕ x := by
  apply le_antisymm
  · -- ϕ y ≤ ϕ x: use h_congr y x with y =ᴮ x = ⊤
    have : y =ᴮ x = ⊤ := by rw [bv_eq_symm]; exact H
    calc ϕ y ≤ ⊤ ⊓ ϕ y := by simp
      _ = (y =ᴮ x) ⊓ ϕ y := by rw [this]
      _ ≤ ϕ x := h_congr y x
  · -- ϕ x ≤ ϕ y: use h_congr x y with x =ᴮ y = ⊤
    calc ϕ x ≤ ⊤ ⊓ ϕ x := by simp
      _ = (x =ᴮ y) ⊓ ϕ x := by rw [H]
      _ ≤ ϕ y := h_congr x y

-- src/bvm.lean:485
/-- If u = v and u ∈ w, then this implies that v ∈ w -/
lemma subst_congr_mem_left {u v w : bSet 𝔹} : u =ᴮ v ⊓ u ∈ᴮ w ≤ v ∈ᴮ w := by
  sorry -- TODO: port from src/bvm.lean:485-491 (requires bv_eq_trans)

-- src/bvm.lean:493
@[simp] lemma subst_congr_mem_left' {Γ : 𝔹} {u v w : bSet 𝔹} :
    Γ ≤ u =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ v ∈ᴮ w :=
  fun h₁ h₂ => poset_yoneda_inv Γ subst_congr_mem_left (le_inf h₁ h₂)

-- src/bvm.lean:504
/-- If v = w and u ∈ v, then this implies that u ∈ w -/
lemma subst_congr_mem_right {u v w : bSet 𝔹} : (v =ᴮ w ⊓ u ∈ᴮ v) ≤ u ∈ᴮ w := by
  sorry -- TODO: port from src/bvm.lean:504-512 (requires subst_congr_mem_left)

-- src/bvm.lean:514
@[simp] lemma subst_congr_mem_right' {Γ : 𝔹} {u v w : bSet 𝔹} :
    Γ ≤ w =ᴮ v → Γ ≤ u ∈ᴮ w → Γ ≤ u ∈ᴮ v :=
  fun h₁ h₂ => poset_yoneda_inv Γ subst_congr_mem_right (le_inf h₁ h₂)

-- src/bvm.lean:518
lemma bounded_forall {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
    (⨅ (i_x : v.type), (v.bval i_x ⟹ ϕ (v.func i_x))) =
    (⨅ (x : bSet 𝔹), x ∈ᴮ v ⟹ ϕ x) := by
  apply le_antisymm
  · apply le_iInf; intro x
    cases v with | mk vα vA vB =>
    simp only [bval, func, mem]
    rw [supr_imp_eq]
    apply le_iInf; intro i_y
    apply iInf_le_of_le i_y
    rw [← deduction, ← inf_assoc]
    apply le_trans
    · exact inf_le_inf bv_imp_elim le_rfl
    rw [inf_comm, bv_eq_symm]
    exact h_congr _ _
  · apply le_iInf; intro i_x'
    apply iInf_le_of_le (func v i_x')
    apply imp_le_of_left_le
    cases v with | mk vα vA vB =>
    simp only [func, bval, mem]
    exact le_iSup_of_le i_x' (le_inf le_rfl (by simp))

-- src/bvm.lean:531
lemma bounded_exists {v : bSet 𝔹} {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} :
    (⨆ (i_x : v.type), (v.bval i_x ⊓ ϕ (v.func i_x))) =
    (⨆ (x : bSet 𝔹), x ∈ᴮ v ⊓ ϕ x) := by
  apply le_antisymm
  · apply iSup_le; intro i_x
    apply le_iSup_of_le (v.func i_x)
    exact le_inf (inf_le_left.trans (mem_mk' v i_x)) inf_le_right
  · apply iSup_le; intro x
    rw [mem_unfold]
    apply bv_cases_left (h := fun i_x => ?_)
    -- goal: v.bval i_x ⊓ x =ᴮ v.func i_x ⊓ ϕ x ≤ ⨆ i, v.bval i ⊓ ϕ (v.func i)
    apply le_iSup_of_le i_x
    -- goal: v.bval i_x ⊓ x =ᴮ v.func i_x ⊓ ϕ x ≤ v.bval i_x ⊓ ϕ (v.func i_x)
    apply le_inf
    · exact inf_le_left.trans inf_le_left
    · -- (v.bval i_x ⊓ x =ᴮ v.func i_x) ⊓ ϕ x ≤ ϕ (v.func i_x)
      -- via (x =ᴮ v.func i_x) ⊓ ϕ x ≤ ϕ (v.func i_x) = h_congr x (v.func i_x)
      have : (v.bval i_x ⊓ x =ᴮ v.func i_x) ⊓ ϕ x ≤ x =ᴮ v.func i_x ⊓ ϕ x :=
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
      exact le_trans this (h_congr x (v.func i_x))

-- src/bvm.lean:544
-- Uses bv_eq_trans (sorried) — sorry-stubbed
lemma mem_unfold' {u v : bSet 𝔹} : u ∈ᴮ v = ⨆ z, z ∈ᴮ v ⊓ u =ᴮ z := by
  sorry -- TODO: port from src/bvm.lean:544-547 (requires bv_eq_trans)

-- src/bvm.lean:549
lemma subset_unfold' {x u : bSet 𝔹} : x ⊆ᴮ u = ⨅ (w : bSet 𝔹), w ∈ᴮ x ⟹ w ∈ᴮ u := by
  simp only [subset_unfold]
  rw [bounded_forall (h_congr := fun a b => subst_congr_mem_left)]

-- src/bvm.lean:555
lemma bv_eq_unfold' {x y : bSet 𝔹} :
    x =ᴮ y = (⨅ z, z ∈ᴮ x ⟹ z ∈ᴮ y) ⊓ (⨅ z, z ∈ᴮ y ⟹ z ∈ᴮ x) := by
  rw [eq_iff_subset_subset, subset_unfold', subset_unfold']

-- src/bvm.lean:560
theorem mem_ext {x y : bSet 𝔹} {Γ : 𝔹}
    (h₁ : Γ ≤ ⨅ z, z ∈ᴮ x ⟹ z ∈ᴮ y)
    (h₂ : Γ ≤ ⨅ z, z ∈ᴮ y ⟹ z ∈ᴮ x) : Γ ≤ x =ᴮ y := by
  rw [bv_eq_unfold']; exact le_inf h₁ h₂

-- src/bvm.lean:563
@[simp] lemma subset_self_eq_top {x : bSet 𝔹} : x ⊆ᴮ x = ⊤ :=
  top_unique subset_self

-- src/bvm.lean:566
lemma subset_trans {x y z : bSet 𝔹} : x ⊆ᴮ y ⊓ y ⊆ᴮ z ≤ x ⊆ᴮ z := by
  simp only [subset_unfold']
  apply le_iInf; intro w
  rw [← deduction]
  -- Goal: (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x ≤ w ∈ᴮ z
  have hxy_spec : (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ≤ w ∈ᴮ x ⟹ w ∈ᴮ y := iInf_le _ w
  have hyz_spec : (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ≤ w ∈ᴮ y ⟹ w ∈ᴮ z := iInf_le _ w
  have hxy : (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x
      ≤ w ∈ᴮ y :=
    le_trans (le_inf ((inf_le_left.trans inf_le_left).trans hxy_spec) inf_le_right) bv_imp_elim
  calc (⨅ w', w' ∈ᴮ x ⟹ w' ∈ᴮ y) ⊓ (⨅ w', w' ∈ᴮ y ⟹ w' ∈ᴮ z) ⊓ w ∈ᴮ x
      ≤ (w ∈ᴮ y ⟹ w ∈ᴮ z) ⊓ w ∈ᴮ y :=
        le_inf ((inf_le_left.trans inf_le_right).trans hyz_spec) hxy
    _ ≤ w ∈ᴮ z := bv_imp_elim

-- src/bvm.lean:576
lemma subset_trans' {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₁ : Γ ≤ x ⊆ᴮ y) (H₂ : Γ ≤ y ⊆ᴮ z) : Γ ≤ x ⊆ᴮ z :=
  poset_yoneda_inv Γ subset_trans (le_inf H₁ H₂)

-- src/bvm.lean:587
lemma mem_of_mem_subset {x y z : bSet 𝔹} {Γ : 𝔹}
    (H₂ : Γ ≤ y ⊆ᴮ z) (H₁ : Γ ≤ x ∈ᴮ y) : Γ ≤ x ∈ᴮ z := by
  rw [subset_unfold'] at H₂
  exact context_imp_elim (context_specialize H₂ x) H₁

-- src/bvm.lean:603
lemma subst_congr_subset_left {x v u : bSet 𝔹} :
    ((v ⊆ᴮ u) ⊓ (x =ᴮ v) : 𝔹) ≤ (x ⊆ᴮ u) := by
  sorry -- TODO: port from src/bvm.lean:603-614

-- src/bvm.lean:616
lemma subst_congr_subset_right {x v u : bSet 𝔹} :
    ((v ⊆ᴮ u) ⊓ (u =ᴮ x) : 𝔹) ≤ (v ⊆ᴮ x) := by
  sorry -- TODO: port from src/bvm.lean:616-622

-- src/bvm.lean:626
lemma bv_rw'₀ {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
  poset_yoneda_inv Γ (h_congr _ _) (le_inf (by rwa [bv_eq_symm]) H_new)

-- src/bvm.lean:634
@[reducible] def B_ext (ϕ : bSet 𝔹 → 𝔹) : Prop :=
  ∀ x y, x =ᴮ y ⊓ ϕ x ≤ ϕ y

-- src/bvm.lean:639
lemma bv_rw' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    {h_congr : B_ext ϕ} {H_new : Γ ≤ ϕ y} : Γ ≤ ϕ x :=
  bv_rw'₀ H (h_congr := h_congr) (H_new := H_new)

-- src/bvm.lean:642
@[simp] lemma B_ext_bv_eq_left {y : bSet 𝔹} : B_ext (fun x => x =ᴮ y) :=
  fun _ _ => by rw [bv_eq_symm (x := _) (y := _)]; exact bv_eq_trans

-- src/bvm.lean:645
@[simp] lemma B_ext_bv_eq_right {x : bSet 𝔹} : B_ext (fun y => x =ᴮ y) :=
  fun _ _ => by rw [inf_comm]; exact bv_eq_trans

-- src/bvm.lean:648
@[simp] lemma B_ext_mem_left {y : bSet 𝔹} : B_ext (fun x => x ∈ᴮ y) :=
  fun _ _ => subst_congr_mem_left

-- src/bvm.lean:651
@[simp] lemma B_ext_mem_right {x : bSet 𝔹} : B_ext (fun y => x ∈ᴮ y) :=
  fun _ _ => subst_congr_mem_right

-- src/bvm.lean:654
@[simp] lemma B_ext_subset_left {y : bSet 𝔹} : B_ext (fun x => x ⊆ᴮ y) :=
  fun _ _ => by rw [inf_comm, bv_eq_symm]; exact subst_congr_subset_left

-- src/bvm.lean:657
@[simp] lemma B_ext_subset_right {x : bSet 𝔹} : B_ext (fun y => x ⊆ᴮ y) :=
  fun _ _ => by rw [inf_comm]; exact subst_congr_subset_right

-- src/bvm.lean:660
@[simp] lemma B_ext_sup {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
    B_ext (fun x => ϕ₁ x ⊔ ϕ₂ x) := by
  intros x y
  rw [inf_comm, deduction]
  apply sup_le
  · rw [← deduction]; exact le_trans (by rw [inf_comm]; exact h₁ x y) le_sup_left
  · rw [← deduction]; exact le_trans (by rw [inf_comm]; exact h₂ x y) le_sup_right

-- src/bvm.lean:668
@[simp] lemma B_ext_inf {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} (h₁ : B_ext ϕ₁) (h₂ : B_ext ϕ₂) :
    B_ext (fun x => ϕ₁ x ⊓ ϕ₂ x) := by
  intros x y
  apply le_inf
  · exact le_trans (inf_le_inf_left _ inf_le_left) (h₁ x y)
  · exact le_trans (inf_le_inf_left _ inf_le_right) (h₂ x y)

-- src/bvm.lean:676
@[simp] lemma B_ext_imp {ϕ₁ ϕ₂ : bSet 𝔹 → 𝔹} {h₁ : B_ext ϕ₁} {h₂ : B_ext ϕ₂} :
    B_ext (fun x => ϕ₁ x ⟹ ϕ₂ x) := by
  intros x y
  rw [← deduction]
  -- x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₂ y
  -- Step: ϕ₁ y → ϕ₁ x (via h₁ with y =ᴮ x)
  -- Step: (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ x → ϕ₂ x (bv_imp_elim)
  -- Step: ϕ₂ x → ϕ₂ y (via h₂ with x =ᴮ y)
  have step1 : x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₁ x := by
    apply le_trans _ (h₁ y x)
    · exact le_inf (inf_le_left.trans (by rw [bv_eq_symm]; exact inf_le_left)) inf_le_right
  have step2 : x =ᴮ y ⊓ (ϕ₁ x ⟹ ϕ₂ x) ⊓ ϕ₁ y ≤ ϕ₂ x :=
    le_trans (le_inf (inf_le_left.trans inf_le_right) step1) bv_imp_elim
  exact le_trans (le_inf (inf_le_left.trans inf_le_left) step2) (h₂ x y)

-- src/bvm.lean:684
@[simp] lemma B_ext_const {b : 𝔹} : B_ext (fun _ : bSet 𝔹 => b) :=
  fun _ _ => inf_le_right

-- src/bvm.lean:687
@[simp] lemma B_ext_neg {ϕ₁ : bSet 𝔹 → 𝔹} {h : B_ext ϕ₁} : B_ext (fun x => (ϕ₁ x)ᶜ) := by
  simp only [← imp_bot]
  exact B_ext_imp (h₁ := h) (h₂ := B_ext_const)

-- src/bvm.lean:690
@[simp] lemma B_ext_iInf {ι : Type*} {Ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext (Ψ i)} :
    B_ext (fun x => ⨅ i, Ψ i x) := by
  intros x y
  apply le_iInf; intro i
  apply bv_specialize_right i
  exact h i x y

-- src/bvm.lean:693
@[simp] lemma B_ext_iSup {ι : Type*} {ψ : ι → (bSet 𝔹 → 𝔹)} {h : ∀ i, B_ext (ψ i)} :
    B_ext (fun x => ⨆ i, ψ i x) := by
  intros x y
  apply bv_cases_right; intro i
  apply bv_use i
  exact h i x y

-- src/bvm.lean:698
@[reducible] def B_congr (t : bSet 𝔹 → bSet 𝔹) : Prop :=
  ∀ {x₁ x₂ : bSet 𝔹} {Γ : 𝔹}, Γ ≤ x₁ =ᴮ x₂ → Γ ≤ t x₁ =ᴮ t x₂

-- src/bvm.lean:702 (dropping the meta-tactic autoParam on H and H')
@[simp] lemma B_ext_term (ϕ : bSet 𝔹 → 𝔹) (t : bSet 𝔹 → bSet 𝔹)
    (H : B_ext ϕ) (H' : B_congr t) :
    B_ext (fun z => ϕ (t z)) := by
  intros x y
  -- x =ᴮ y ⊓ ϕ (t x) ≤ ϕ (t y)
  calc x =ᴮ y ⊓ ϕ (t x)
      ≤ t x =ᴮ t y ⊓ ϕ (t x) :=
        le_inf (H' inf_le_left) inf_le_right
    _ ≤ ϕ (t y) := H (t x) (t y)

-- src/bvm.lean:712
lemma bv_rw'' {x y : bSet 𝔹} {Γ : 𝔹} (H : Γ ≤ x =ᴮ y) {ϕ : bSet 𝔹 → 𝔹}
    (H_new : Γ ≤ ϕ x) (h_congr : B_ext ϕ) : Γ ≤ ϕ y :=
  poset_yoneda_inv Γ (h_congr x y) (le_inf H H_new)

-- src/bvm.lean:719
lemma mem_congr {Γ : 𝔹} {x₁ x₂ y₁ y₂ : bSet 𝔹}
    (H₁ : Γ ≤ x₁ =ᴮ y₁) (H₂ : Γ ≤ x₂ =ᴮ y₂) (H₃ : Γ ≤ x₁ ∈ᴮ x₂) :
    Γ ≤ y₁ ∈ᴮ y₂ := by
  apply bv_rw' (H := by rwa [bv_eq_symm]) (h_congr := B_ext_mem_left)
  apply bv_rw' (H := by rwa [bv_eq_symm]) (h_congr := B_ext_mem_right)
  exact H₃

-- src/bvm.lean:723
@[reducible, instance] def b_setoid (Γ : 𝔹) : Setoid (bSet 𝔹) :=
  { r := bv_eq' Γ
    iseqv := ⟨fun _ => bv_refl, fun h => bv_symm h, fun h1 h2 => bv_trans h1 h2⟩ }

-- src/bvm.lean:727
lemma bv_cc_mk_iff {Γ : 𝔹} {x y : bSet 𝔹} :
    Γ ≤ x =ᴮ y ↔ (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x) = (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) := by
  constructor
  · intro h; exact Quotient.sound h
  · intro h; exact Quotient.exact h

-- src/bvm.lean:729
lemma bv_cc_mk {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x =ᴮ y) :
    (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x) = (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) :=
  bv_cc_mk_iff.mp H

-- src/bvm.lean:732
def b_setoid_mem (Γ : 𝔹) :
    Quotient (b_setoid Γ) → Quotient (b_setoid Γ) → Prop :=
  Quotient.lift₂ (fun x y => Γ ≤ x ∈ᴮ y)
    (by intros a₁ b₁ a₂ b₂ H_eqv₁ H_eqv₂
        apply propext; constructor <;> intro H
        · exact mem_congr H_eqv₁ H_eqv₂ H
        · exact mem_congr (bv_symm H_eqv₁) (bv_symm H_eqv₂) H)

-- src/bvm.lean:742
lemma bv_cc_mk_mem_iff {Γ : 𝔹} {x y : bSet 𝔹} :
    Γ ≤ x ∈ᴮ y ↔ b_setoid_mem Γ (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x)
      (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) := by
  rfl

-- src/bvm.lean:746
lemma bv_cc_mk_mem {Γ : 𝔹} {x y : bSet 𝔹} (H : Γ ≤ x ∈ᴮ y) :
    b_setoid_mem Γ (@Quotient.mk (bSet 𝔹) (b_setoid Γ) x) (@Quotient.mk (bSet 𝔹) (b_setoid Γ) y) :=
  bv_cc_mk_mem_iff.mp H

end bSet
