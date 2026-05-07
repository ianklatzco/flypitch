/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/zfc.lean (552 lines) — Task 22 -/

import Flypitch4.Bfol
import Flypitch4.Forcing
import Flypitch4.ForcingCH

open Fol bSet

universe u

-- ============================================================
-- The language of ZFC (src/zfc.lean:32-46)
-- ============================================================

/-- Relation symbols of ZFC (just membership ∈). -/
inductive ZFC_rel : ℕ → Type 1
  | ε : ZFC_rel 2

/-- Function symbols of ZFC. -/
inductive ZFC_func : ℕ → Type 1
  | emptyset : ZFC_func 0
  | pr       : ZFC_func 2
  | ω        : ZFC_func 0
  | P        : ZFC_func 1
  | Union    : ZFC_func 1

/-- The language of ZFC set theory. -/
def L_ZFC : Language.{1} :=
  { functions := ZFC_func, relations := ZFC_rel }

-- ============================================================
-- The Boolean-valued V model (src/zfc.lean:48-113)
-- ============================================================

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

/-- Interpret L_ZFC function symbols in bSet β. -/
def bSet_model_fun_map : ∀ {n : ℕ}, L_ZFC.functions n → DVec (bSet β) n → bSet β
  | _, ZFC_func.emptyset, _  => bSet.empty
  | _, ZFC_func.pr, DVec.cons x (DVec.cons y DVec.nil) => pair x y
  | _, ZFC_func.ω, _ => bSet.omega
  | _, ZFC_func.P, DVec.cons x DVec.nil => bv_powerset x
  | _, ZFC_func.Union, DVec.cons x DVec.nil => bv_union x

/-- Interpret L_ZFC relation symbols in bSet β. -/
def bSet_model_rel_map : ∀ {n : ℕ}, L_ZFC.relations n → DVec (bSet β) n → β
  | _, ZFC_rel.ε, DVec.cons x (DVec.cons y DVec.nil) => x ∈ᴮ y

variable (β)

/-- The Boolean-valued model V(β) of ZFC. -/
noncomputable def V : bStructure L_ZFC β :=
  { carrier   := bSet β
    fun_map   := bSet_model_fun_map
    rel_map   := bSet_model_rel_map
    eq        := (· =ᴮ ·)
    eq_refl   := fun x => bv_eq_refl x
    eq_symm   := fun x y => bv_eq_symm
    eq_trans  := fun y => bv_eq_trans
    fun_congr := by
      intro n F x y
      cases F with
      | emptyset =>
        cases x; cases y; simp [DVec.map2, DVec.fInf_nil]
      | pr =>
        cases x with | cons x₁ xs₁ =>
        cases xs₁ with | cons x₂ xs₂ =>
        cases xs₂ with | nil =>
        cases y with | cons y₁ ys₁ =>
        cases ys₁ with | cons y₂ ys₂ =>
        cases ys₂ with | nil =>
        simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq,
                   bSet_model_fun_map]
        exact fun Γ h => pair_congr (inf_le_left.trans h) (inf_le_right.trans h)
      | ω =>
        cases x; cases y; simp [DVec.map2, DVec.fInf_nil]
      | P =>
        cases x with | cons x₁ xs₁ =>
        cases xs₁ with | nil =>
        cases y with | cons y₁ ys₁ =>
        cases ys₁ with | nil =>
        simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq,
                   bSet_model_fun_map]
        exact fun Γ h => bv_powerset_congr h
      | Union =>
        cases x with | cons x₁ xs₁ =>
        cases xs₁ with | nil =>
        cases y with | cons y₁ ys₁ =>
        cases ys₁ with | nil =>
        simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq,
                   bSet_model_fun_map]
        exact fun Γ h => bv_union_congr h
    rel_congr := by
      intro n R x y
      cases R with
      | ε =>
        cases x with | cons x₁ xs₁ =>
        cases xs₁ with | cons x₂ xs₂ =>
        cases xs₂ with | nil =>
        cases y with | cons y₁ ys₁ =>
        cases ys₁ with | cons y₂ ys₂ =>
        cases ys₂ with | nil =>
        simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq,
                   bSet_model_rel_map]
        exact fun Γ h => mem_congr (inf_le_left.trans h) (inf_le_right.trans h) inf_le_right
  }

@[simp] lemma carrier_V : ↥(V β) = bSet β := rfl
@[simp] lemma V_forall {C : (V β) → β} : (⨅ (x : V β), C x) = ⨅ (x : bSet β), C x := rfl
@[simp] lemma V_exists {C : (V β) → β} : (⨆ (x : V β), C x) = ⨆ (x : bSet β), C x := rfl
@[simp] lemma V_eq {a b : V β} : (V β).eq a b = a =ᴮ b := rfl

instance V_β_nonempty : Nonempty (V β) := ⟨bSet.empty⟩

variable {β}

-- ============================================================
-- Bounded terms/formulas for L_ZFC (src/zfc.lean:115-140)
-- ============================================================

def emptyset' {n} : bounded_term L_ZFC n := bd_const ZFC_func.emptyset
notation "∅'" => emptyset'

def omega' {n} : bounded_term L_ZFC n := bd_const ZFC_func.ω
notation "ω'" => omega'

def Powerset {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.P) t
notation "P'" => Powerset

/-- Boolean membership formula: t₁ ∈ t₂ -/
def mem' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  @bounded_formula_of_relation L_ZFC 2 n ZFC_rel.ε t₁ t₂

/-- Bounded pair term -/
def pair' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  @bounded_term_of_function L_ZFC 2 n ZFC_func.pr t₁ t₂

/-- Bounded union term -/
def union' {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.Union) t
notation "⋃'" => union'

/-- Subset formula: t₁ ⊆ t₂ -/
def subset'' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₁ ↑ᵇ' 1 # 0))
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₂ ↑ᵇ' 1 # 0)))

-- ============================================================
-- Simp lemmas for boolean_realize (src/zfc.lean:142-176)
-- ============================================================

@[simp] lemma boolean_realize_bounded_formula_mem' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (mem' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ∈ᴮ
    boolean_realize_bounded_term v t₂ DVec.nil := by
  simp [mem', bounded_formula_of_relation, Arity'.of_dvector_map,
        boolean_realize_bounded_formula_bd_apps_rel, bSet_model_rel_map]

@[simp] lemma boolean_realize_bounded_term_Union' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (⋃' t) DVec.nil =
    bv_union (boolean_realize_bounded_term v t DVec.nil) := by
  simp [union', bSet_model_fun_map]

@[simp] lemma boolean_realize_bounded_term_Powerset' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (P' t) DVec.nil =
    bv_powerset (boolean_realize_bounded_term v t DVec.nil) := by
  simp [Powerset, bSet_model_fun_map]

@[simp] lemma boolean_realize_bounded_term_omega' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ω' DVec.nil = bSet.omega := by
  simp [omega', bd_const, bSet_model_fun_map]

@[simp] lemma boolean_realize_bounded_term_emptyset' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ∅' DVec.nil = bSet.empty := by
  simp [emptyset', bd_const, bSet_model_fun_map]

@[simp] lemma boolean_realize_bounded_term_pair' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (pair' t₁ t₂) DVec.nil =
    pair (boolean_realize_bounded_term v t₁ DVec.nil)
         (boolean_realize_bounded_term v t₂ DVec.nil) := by
  simp [pair', bounded_term_of_function, Arity'.of_dvector_map,
        boolean_realize_bounded_term_bd_apps, bSet_model_fun_map]

@[simp] lemma boolean_realize_bounded_formula_subset' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (subset'' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ⊆ᴮ boolean_realize_bounded_term v t₂ DVec.nil := by
  simp [subset'', subset_unfold']

@[simp] lemma fin_0 {n : ℕ} : (0 : Fin (n + 1)).1 = 0 := rfl
@[simp] lemma fin_1 {n : ℕ} : (1 : Fin (n + 2)).1 = 1 := rfl
@[simp] lemma fin_2 {n : ℕ} : (2 : Fin (n + 3)).1 = 2 := rfl
@[simp] lemma fin_3 {n : ℕ} : (3 : Fin (n + 4)).1 = 3 := rfl

-- ============================================================
-- Ordinal predicates (src/zfc.lean:307-327)
-- ============================================================

def is_transitive_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
                 (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))

def epsilon_trichotomy_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
    (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
      (bd_or
        (bd_or (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
               (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))))

def epsilon_well_founded_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
    (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
      (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
          (bd_not (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))))))))

def ewo_f : bounded_formula L_ZFC 1 := bd_and epsilon_trichotomy_f epsilon_well_founded_f

def Ord_f : bounded_formula L_ZFC 1 := bd_and ewo_f is_transitive_f

@[simp] lemma Ord_f_is_Ord {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) Ord_f DVec.nil = Ord x := by
  simp [Ord_f, ewo_f, is_transitive_f, epsilon_well_founded_f, epsilon_trichotomy_f,
        Ord, epsilon_well_orders, is_transitive]
  rfl

-- ============================================================
-- The ZFC axioms as sentences (src/zfc.lean:179-382)
-- ============================================================

-- axiom of emptyset: ∀ x, x ∉ ∅
def axiom_of_emptyset : sentence L_ZFC :=
  bd_all (bd_not (mem' (bd_var ⟨0, by omega⟩) ∅'))

lemma bSet_models_emptyset : ⊤ ⊩[V β] axiom_of_emptyset := by
  change ⊤ ≤ _
  simp only [axiom_of_emptyset, boolean_realize_sentence_all,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula,
             V_eq, boolean_realize_bounded_term_emptyset']
  intro x
  exact empty_spec

-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w
def axiom_of_ordered_pairs : sentence L_ZFC :=
  bd_all (bd_all (bd_all (bd_all
    (bd_biimp
      (bd_equal (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))
                (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
      (bd_and
        (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_equal (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)))))))

lemma bSet_models_ordered_pairs : ⊤ ⊩[V β] axiom_of_ordered_pairs := by
  change ⊤ ≤ _
  simp only [axiom_of_ordered_pairs, boolean_realize_sentence_all,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula, V_eq, boolean_realize_bounded_term_pair']
  intro a b x y
  constructor
  · exact fun h => ⟨eq_of_eq_pair_left h, eq_of_eq_pair_right h⟩
  · exact fun ⟨h₁, h₂⟩ => pair_congr h₁ h₂

-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
def axiom_of_extensionality : sentence L_ZFC :=
  bd_all (bd_all
    (bd_imp
      (bd_all (bd_biimp
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))
      (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))))

lemma bSet_models_extensionality : ⊤ ⊩[V β] axiom_of_extensionality := by
  simp only [forced_in, axiom_of_extensionality, boolean_realize_sentence,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             V_eq]
  exact bSet_axiom_of_extensionality

-- axiom schema of strong collection (src/zfc.lean:208-211)
def axiom_of_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) : sentence L_ZFC :=
  bd_alls (n + 1) $
    bd_imp
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_ex (ϕ ↑ᶠᵇ' 1 # 2))))
      (bd_ex
        (bd_and
          (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
              (ϕ ↑ᶠᵇ' 2 # 2)))))
          (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
              (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, by omega⟩))))))))

lemma lift2_helper {n l} (f : bounded_preformula L_ZFC n l) {k} (m : ℕ) :
    (f ↑ᶠᵇ' (k + 2) # m).fst = ((f ↑ᶠᵇ' (k + 1) # m) ↑ᶠᵇ' 1 # m).fst := by
  simp only [lift_bounded_formula_fst]
  rw [lift_formula_at2_medium] <;> omega

lemma B_ext_left_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 1))
    (xs : DVec (V β) n) (x y : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons x xs) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons y xs) ϕ DVec.nil := by
  -- Reduce to boolean_realize_bounded_formula_congr via the diagonal iInf
  have key : x =ᴮ y = ⨅ (m : Fin (n + 1)), (V β).eq
      ((DVec.cons x xs).nth m.1 m.2) ((DVec.cons y xs).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf
      intro ⟨m, hm⟩
      cases m with
      | zero => simp [DVec.nth, V_eq]
      | succ k =>
        simp only [DVec.nth, DVec.cons, V_eq]
        exact bv_refl
    · have h := iInf_le (fun m : Fin (n+1) => (V β).eq
          ((DVec.cons x xs).nth m.1 m.2) ((DVec.cons y xs).nth m.1 m.2)) ⟨0, Nat.zero_lt_succ _⟩
      simp [DVec.nth, V_eq] at h
      exact h
  rw [key]
  exact boolean_realize_bounded_formula_congr (V_β_nonempty) _ _ ϕ DVec.nil

lemma B_ext_right_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2))
    (xs : DVec (V β) n) (x y z : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons z (DVec.cons x xs)) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons z (DVec.cons y xs)) ϕ DVec.nil := by
  have key : x =ᴮ y = ⨅ (m : Fin (n + 2)), (V β).eq
      ((DVec.cons z (DVec.cons x xs)).nth m.1 m.2)
      ((DVec.cons z (DVec.cons y xs)).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf
      intro ⟨m, hm⟩
      cases m with
      | zero =>
        simp only [DVec.nth, DVec.cons, V_eq]
        exact bv_refl
      | succ k =>
        cases k with
        | zero => simp [DVec.nth, V_eq]
        | succ j =>
          simp only [DVec.nth, DVec.cons, V_eq]
          exact bv_refl
    · have h := iInf_le (fun m : Fin (n+2) => (V β).eq
          ((DVec.cons z (DVec.cons x xs)).nth m.1 m.2)
          ((DVec.cons z (DVec.cons y xs)).nth m.1 m.2)) ⟨1, by omega⟩
      simp [DVec.nth, V_eq] at h
      exact h
  rw [key]
  exact boolean_realize_bounded_formula_congr (V_β_nonempty) _ _ ϕ DVec.nil

lemma bSet_models_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) :
    ⊤ ⊩[V β] axiom_of_collection ϕ := by
  change ⊤ ≤ _
  simp only [axiom_of_collection, boolean_realize_sentence_bd_alls]
  intro xs
  -- xs : DVec (V β) (n+1); write xs = DVec.cons u xs'
  obtain ⟨u, xs', rfl⟩ := DVec.head_tail xs
  simp only [boolean_realize_bounded_formula_and, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
             boolean_realize_formula_insert_lift2, boolean_realize_subst_formula0,
             lift2_helper, fin_2, V_eq, V_forall, V_exists]
  apply bSet_axiom_of_collection
    (fun a b => boolean_realize_bounded_formula (DVec.cons b (DVec.cons a xs')) ϕ DVec.nil)
  · intro x y z; exact B_ext_left_realize_bounded_formula ϕ xs' x y
  · intro x y z; exact B_ext_right_realize_bounded_formula ϕ xs' x y z

-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y
def axiom_of_union : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, by omega⟩) (union' (bd_var ⟨1, by omega⟩)))
      (bd_ex (bd_and
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))))))

lemma bSet_models_union : ⊤ ⊩[V β] axiom_of_union := by
  simp only [forced_in, axiom_of_union, boolean_realize_sentence,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_biimp,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_term_Union',
             V_eq, V_forall, V_exists]
  intro u x
  have hspec := bv_union_spec' u (Γ := ⊤) |>.trans (iInf_le _ x)
  simp only [bv_biimp_iff, top_le_iff] at hspec ⊢
  simp only [boolean_realize_bounded_formula_biimp, bv_biimp_iff]
  constructor
  · intro h
    exact (hspec.mp (le_of_eq h.symm))
  · intro h
    exact le_antisymm (le_top.trans (hspec.mpr (le_top.trans h))) le_top

-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z
def axiom_of_powerset : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, by omega⟩) (Powerset (bd_var ⟨1, by omega⟩)))
      (bd_all (bd_imp
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))))))

lemma bSet_models_powerset : ⊤ ⊩[V β] axiom_of_powerset := by
  simp only [forced_in, axiom_of_powerset, boolean_realize_sentence,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_biimp,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_term_Powerset',
             V_eq, V_forall]
  intro z y
  rw [subset_unfold']
  exact le_antisymm
    (le_inf (fun {Γ} h => (bv_powerset_spec.mpr le_rfl).trans (le_top.trans (le_top.trans h)))
            (fun {Γ} h => (bv_powerset_spec.mp le_rfl).trans (le_top.trans (le_top.trans h))))
    (fun {Γ} h => by
      simp only [bihimp, himp_eq, sup_comm, inf_comm] at *
      exact le_top)

-- axiom of infinity (src/zfc.lean:332-347)
def axiom_of_infinity : sentence L_ZFC :=
  bd_and
    (bd_and
      (bd_and
        (mem' ∅' ω')
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) ω')
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, by omega⟩) ω')
            (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))
      (bd_ex (bd_and Ord_f (bd_equal ω' (bd_var ⟨0, by omega⟩)))))
    (bd_all (bd_imp Ord_f (bd_imp
      (bd_and (mem' ∅' (bd_var ⟨0, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
            (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))
      (subset'' ω' (bd_var ⟨0, by omega⟩)))))

lemma bSet_models_infinity : ⊤ ⊩[V β] axiom_of_infinity := by
  simp only [forced_in, axiom_of_infinity, boolean_realize_sentence,
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_term_omega', boolean_realize_bounded_term_emptyset',
             Ord_f_is_Ord, boolean_realize_bounded_formula_subset',
             V_eq, V_forall, V_exists]
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · -- ∅ ∈ ω
    exact contains_empty_check_omega
  · -- ∀ x ∈ ω, ∃ y ∈ ω, x ∈ y
    have := bSet_axiom_of_infinity'.trans inf_le_right
    simpa using this
  · -- ∃ α, Ord(α) ∧ ω = α
    apply bv_use bSet.omega
    exact le_inf Ord_omega bv_refl
  · -- ∀ α, Ord(α) → (∅ ∈ α ∧ ∀ x ∈ α, ∃ y ∈ α, x ∈ y) → ω ⊆ α
    exact omega_least_is_limit

-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y
def axiom_of_regularity : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
    (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (bd_not (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))))))

lemma bSet_models_regularity : ⊤ ⊩[V β] axiom_of_regularity := by
  change ⊤ ≤ _
  simp only [axiom_of_regularity, boolean_realize_sentence_all,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_term_emptyset',
             V_eq]
  intro x
  rw [← deduction, top_inf_eq]
  exact bSet_axiom_of_regularity x

-- Zorn's lemma (src/zfc.lean:363-376)
def zorns_lemma : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
    (bd_imp
      (bd_all (bd_imp
        (bd_and (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
          (bd_all (bd_all (bd_imp
            (bd_and (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨2, by omega⟩))
                    (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩)))
            (bd_or (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
                   (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))))))
        (mem' (union' (bd_var ⟨0, by omega⟩)) (bd_var ⟨1, by omega⟩))))
      (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
          (bd_imp (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
            (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))))

lemma bSet_models_Zorn : ⊤ ⊩[V β] zorns_lemma := by
  simp only [forced_in, zorns_lemma, boolean_realize_sentence,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_or, boolean_realize_bounded_formula_biimp,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_formula_subset',
             boolean_realize_bounded_term_Union', boolean_realize_bounded_term_emptyset',
             V_eq, V_forall, V_exists]
  exact bSet_zorns_lemma'

-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================

/-- The theory ZFC: a set of L_ZFC-sentences. -/
def ZFC : SentTheory L_ZFC :=
  {axiom_of_emptyset, axiom_of_ordered_pairs, axiom_of_extensionality, axiom_of_union,
   axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma} ∪
  ⋃ (n : ℕ), axiom_of_collection '' (Set.univ : Set (bounded_formula L_ZFC (n + 2)))

/-- The fundamental theorem of forcing: bSet β models all of ZFC. -/
theorem bSet_models_ZFC : ⊤ ⊩ₜ[V β] ZFC := by
  simp only [all_forced_in]
  apply le_iInf; intro f; apply le_iInf; intro hf
  simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
             Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and] at hf
  rcases hf with (hf | ⟨n, ϕ, rfl⟩)
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bSet_models_emptyset
    · exact bSet_models_ordered_pairs
    · exact bSet_models_extensionality
    · exact bSet_models_union
    · exact bSet_models_powerset
    · exact bSet_models_infinity
    · exact bSet_models_regularity
    · exact bSet_models_Zorn
  · exact bSet_models_collection _

/-- ZFC is consistent. -/
theorem ZFC_consistent {β : Type 0} [NontrivialCompleteBooleanAlgebra β] :
    SentTheory.is_consistent ZFC :=
  consis_of_exists_bmodel (β := β) (S := V β) bSet_models_ZFC

-- ============================================================
-- Functional-relation formulas (src/zfc.lean:402-470)
-- ============================================================

def is_func_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (mem' (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨4, by omega⟩))
        (mem' (pair' (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨4, by omega⟩)))
      (bd_imp (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))
              (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))

@[simp] lemma realize_is_func_f {f : V β} :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_func_f DVec.nil = is_func f := by
  simp [is_func_f, is_func, boolean_realize_bounded_formula_mem',
        boolean_realize_bounded_term_pair']

def is_total'_f : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f DVec.nil =
    is_total x y f := by
  simp [is_total'_f, is_total, boolean_realize_bounded_formula_mem',
        boolean_realize_bounded_term_pair']

def is_total'_f₂ : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨4, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f₂ DVec.nil =
    is_total y x f := by
  simp [is_total'_f₂, is_total, boolean_realize_bounded_formula_mem',
        boolean_realize_bounded_term_pair']

def is_func'_f : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f

def is_func'_f₂ : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f₂

@[simp] lemma realize_is_func'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f DVec.nil =
    is_func' x y f := by
  simp [is_func'_f, is_func']

@[simp] lemma realize_is_func'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f₂ DVec.nil =
    is_func' y x f := by
  simp [is_func'_f₂, is_func']

/-- at_most_f [y, x] ↔ larger_than x y (surjection from subset of y onto x) -/
def at_most_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_ex
    (bd_and
      (bd_and
        (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨3, by omega⟩))
        (is_func'_f₂.cast (by omega)))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
        (bd_ex (bd_and
          (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
          (mem' (pair' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨2, by omega⟩))))))))

@[simp] lemma realize_at_most_f {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) at_most_f DVec.nil =
    larger_than x y := by
  simp [larger_than, at_most_f, is_func, boolean_realize_bounded_formula_subset',
        boolean_realize_bounded_formula_mem', boolean_realize_bounded_term_pair']

def is_inj_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (bd_and
          (mem' (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨4, by omega⟩))
          (mem' (pair' (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨4, by omega⟩)))
        (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
      (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))))))

@[simp] lemma realize_is_inj_f (f : V β) :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_inj_f DVec.nil = is_inj f := by
  simp [is_inj_f, is_inj, boolean_realize_bounded_formula_mem',
        boolean_realize_bounded_term_pair']

def injects_into_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_and is_func'_f (is_inj_f.cast (by omega)))

@[simp] lemma realize_injects_into {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) injects_into_f DVec.nil =
    injects_into x y := by
  simp [injects_into_f, injects_into]

def non_empty_f : bounded_formula L_ZFC 1 := bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅')

@[simp] lemma non_empty_f_is_non_empty {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) non_empty_f DVec.nil = not_empty x := by
  simp [non_empty_f, not_empty, boolean_realize_bounded_term_emptyset']

-- ============================================================
-- The CH formula (src/zfc.lean:481-502)
-- ============================================================

/-- The continuum hypothesis as an L_ZFC sentence. -/
def CH_f : sentence L_ZFC :=
  bd_all (bd_imp Ord_f
    (bd_or
      (substmax_bounded_formula at_most_f ω')
      (subst0_bounded_formula at_most_f (Powerset omega'))))

lemma CH_f_is_CH : ⟦CH_f⟧[V β] = CH₂ := by
  sorry -- TODO: port from src/zfc.lean:485-496

lemma CH_f_sound {Γ : β} : (Γ ⊩[V β] CH_f) ↔ Γ ≤ CH₂ := by
  change _ ≤ _ ↔ _ ≤ _
  rw [CH_f_is_CH]

lemma neg_CH_f_sound {Γ : β} : (Γ ⊩[V β] (bd_not CH_f : sentence L_ZFC)) ↔ Γ ≤ CH₂ᶜ := by
  change _ ≤ _ ↔ _ ≤ _
  rw [boolean_realize_sentence_not, CH_f_is_CH]

-- ============================================================
-- CH is unprovable from ZFC (src/zfc.lean:508-536)
-- ============================================================

open PSet Cardinal

section CH_unprovable

local notation "𝔹" => 𝔹_cohen

lemma V_𝔹_cohen_models_neg_CH : ⊤ ⊩[V 𝔹] (bd_not CH_f : sentence L_ZFC) := by
  rw [neg_CH_f_sound]; exact neg_CH₂

instance V_𝔹_nonempty : Nonempty (V 𝔹) := ⟨bSet.empty⟩

theorem CH_f_unprovable : ¬ (ZFC ⊢ₛ' CH_f) :=
  unprovable_of_model_neg (V 𝔹) bSet_models_ZFC nontrivial_bot_lt_top V_𝔹_cohen_models_neg_CH

end CH_unprovable

open collapse_algebra

section neg_CH_unprovable

instance V_𝔹_collapse_nonempty : Nonempty (V 𝔹_collapse) := ⟨bSet.empty⟩

lemma V_𝔹_collapse_models_CH : ⊤ ⊩[V 𝔹_collapse] CH_f := by
  rw [CH_f_sound]; exact CH₂_true

theorem neg_CH_f_unprovable : ¬ (ZFC ⊢ₛ' (bd_not CH_f : sentence L_ZFC)) := by
  apply unprovable_of_model_neg (V 𝔹_collapse) bSet_models_ZFC nontrivial_bot_lt_top
  rw [forced_in_not]
  exact V_𝔹_collapse_models_CH

end neg_CH_unprovable

-- ============================================================
-- CH as a first-order formula (src/zfc.lean:538-552)
-- ============================================================

section CH_formula_sec

def Powerset_t : term L_ZFC → term L_ZFC := preterm.app (preterm.func ZFC_func.P)
def omega_t : term L_ZFC := preterm.func ZFC_func.ω
def leq_f : formula L_ZFC := at_most_f.fst
def is_ordinal : formula L_ZFC := Ord_f.fst

def CH_formula : formula L_ZFC :=
  ∀' (is_ordinal ⟹ or' (leq_f[omega_t // 1]f) (leq_f[Powerset_t omega_t // 0]f))

lemma CH_f_fst : CH_f.fst = CH_formula := by
  simp [CH_f, CH_formula, substmax_bounded_formula_fst, subst0_bounded_formula_fst,
        Ord_f, at_most_f, omega', Powerset]

end CH_formula_sec
