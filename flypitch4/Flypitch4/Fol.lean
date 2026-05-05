/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/fol.lean (lines 23-508): Language, preterm, term-level material. -/

import Flypitch4.ToMathlib

universe u v

namespace Fol

/-! ## Valuation helpers (subst_realize) -/

/-- Given a valuation v, a nat n, and an x : S, return v truncated to its first n values,
    with the rest of the values replaced by x. -/
def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
  if k < n then v k else if n < k then v (k - 1) else x

@[simp] lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) :
    Fol.subst_realize v x n k = v k := by
  simp only [subst_realize, H, if_true]

@[simp] lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) :
    Fol.subst_realize v x n k = v (k - 1) := by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [subst_realize, h, if_false, H, if_true]

@[simp] lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) :
    Fol.subst_realize v x n n = x := by
  simp only [subst_realize, lt_irrefl, if_false]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀ k, v k = v' k) (x : S)
    (n k : ℕ) : Fol.subst_realize v x n k = Fol.subst_realize v' x n k := by
  rcases Nat.lt_trichotomy k n with h | h | h
  · simp [subst_realize, h, hv k]
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h, hv (k - 1)]

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
    Fol.subst_realize (Fol.subst_realize v x' (n₁ + n₂)) x n₁ k =
    Fol.subst_realize (Fol.subst_realize v x n₁) x' (n₁ + n₂ + 1) k := by
  simp only [subst_realize]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all [subst_realize] <;> omega

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
    Fol.subst_realize (Fol.subst_realize v x' n) x 0 k =
    Fol.subst_realize (Fol.subst_realize v x 0) x' (n + 1) k := by
  have h := subst_realize2 v x x' 0 n k
  simp only [Nat.zero_add] at h
  exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ} (hv : ∀ k, k < n → v₁ k = v₂ k)
    (x : S) {k : ℕ} (hk : k < n + 1) :
    Fol.subst_realize v₁ x 0 k = Fol.subst_realize v₂ x 0 k := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [subst_realize, h, hv k (Nat.lt_of_succ_lt_succ hk)]

lemma lift_subst_realize_cancel {S : Type u} (v : ℕ → S) (k : ℕ) :
    Fol.subst_realize (fun n => v (n + 1)) (v 0) 0 k = v k := by
  cases k with
  | zero => simp [subst_realize]
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [subst_realize, h]

lemma subst_fin_realize_eq {S : Type u} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) (x : S) (k : ℕ) (hk : k < n + 1) :
    (DVec.cons x v₁).nth k hk = Fol.subst_realize v₂ x 0 k := by
  cases k with
  | zero => simp [DVec.nth, subst_realize]
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp only [DVec.nth, subst_realize, Nat.lt_irrefl, if_false, h, if_true, Nat.add_sub_cancel]
    exact hv k (Nat.lt_of_succ_lt_succ hk)

/-! ## Language -/

structure Language : Type (u + 1) where
  functions : ℕ → Type u
  relations : ℕ → Type u

def Language.constants (L : Language.{u}) := L.functions 0

variable (L : Language.{u})

/-! ## preterm and term -/

/-- `preterm L l` is a partially applied term. If applied to `l` terms, it becomes a term (l=0).
    We use de Bruijn variables. -/
inductive preterm : ℕ → Type u
  | var : ∀ (k : ℕ), preterm 0
  | func : ∀ {l : ℕ} (f : L.functions l), preterm l
  | app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l

@[reducible] def term := preterm L 0

variable {L}

prefix:max "&" => Fol.preterm.var

@[simp] def apps : ∀ {l}, preterm L l → DVec (term L) l → term L
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => apps (preterm.app t t') ts

@[simp] lemma apps_zero (t : term L) (ts : DVec (term L) 0) : apps t ts = t := by
  cases ts; rfl

lemma apps_eq_app {l} (t : preterm L (l + 1)) (s : term L) (ts : DVec (term L) l) :
    ∃ t' s', apps t (DVec.cons s ts) = preterm.app t' s' := by
  induction ts generalizing s with
  | nil => exact ⟨t, s, rfl⟩
  | cons t' ts ih => exact ih (preterm.app t s) t'

namespace preterm

@[simp] def change_arity' : ∀ {l l'} (_ : l = l') (t : preterm L l), preterm L l'
  | _, _, h, var k => by subst h; exact var k
  | _, _, h, func f => func (by subst h; exact f)
  | _, _, h, app t₁ t₂ => app (change_arity' (by omega) t₁) t₂

@[simp] lemma change_arity'_rfl : ∀ {l} (t : preterm L l), change_arity' rfl t = t
  | _, var _ => rfl
  | _, func _ => rfl
  | _, app t₁ _ => by simp [change_arity'_rfl t₁]

end preterm

lemma apps_ne_var {l} {f : L.functions l} {ts : DVec (term L) l} {k : ℕ} :
    apps (preterm.func f) ts ≠ &k := by
  intro h
  cases ts with
  | nil =>
    simp only [apps] at h
    -- h : preterm.func f = preterm.var k — different constructors
    exact absurd h (fun h => by cases h)
  | cons ts_x ts_xs =>
    rcases apps_eq_app (preterm.func f) ts_x ts_xs with ⟨_, _, h'⟩
    rw [h'] at h
    -- h : preterm.app _ _ = preterm.var k — different constructors
    exact absurd h (fun h => by cases h)

lemma apps_inj' {l} {t t' : preterm L l} {ts ts' : DVec (term L) l}
    (h : apps t ts = apps t' ts') : t = t' ∧ ts = ts' := by
  induction ts with
  | nil =>
    cases ts'
    exact ⟨h, rfl⟩
  | cons x xs ih =>
    cases ts' with
    | cons x' xs' =>
      simp only [apps] at h
      obtain ⟨heq, hts⟩ := ih h
      obtain ⟨ht, hx⟩ := preterm.app.inj heq
      exact ⟨ht, by rw [hx, hts]⟩

lemma apps_inj {l} {f f' : L.functions l} {ts ts' : DVec (term L) l}
    (h : apps (preterm.func f) ts = apps (preterm.func f') ts') : f = f' ∧ ts = ts' := by
  rcases apps_inj' h with ⟨h', rfl⟩
  cases h'
  exact ⟨rfl, rfl⟩

def term_of_function {l} (f : L.functions l) : Arity' (term L) (term L) l :=
  Arity'.of_dvector_map (apps (preterm.func f))

-- term.rec: custom recursion principle via structural recursion
def term.rec {C : term L → Sort v}
    (hvar : ∀ (k : ℕ), C (&k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (term L) l)
      (ih_ts : ∀ t, DVec.pmem t ts → C t), C (apps (preterm.func f) ts)) :
    ∀ (t : term L), C t :=
  let rec go : ∀ {l} (t : preterm L l) (ts : DVec (term L) l)
      (ih_ts : ∀ s, DVec.pmem s ts → C s), C (apps t ts)
    | _, preterm.var k, ts, _ => by rw [DVec.zero_eq ts]; exact hvar k
    | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
    | _, preterm.app t₁ t₂, ts, ih_ts =>
        go t₁ (DVec.cons t₂ ts) fun t ht => by
          cases ht with
          | inl h => exact h ▸ go t₂ DVec.nil (fun s hs => hs.elim)
          | inr h => exact ih_ts t h
  fun t => go t DVec.nil (fun s hs => hs.elim)

def term.elim' {C : Type v}
    (hvar : ∀ (k : ℕ), C)
    (hfunc : ∀ {{l}} (f : L.functions l) (ts : DVec (term L) l) (ih_ts : DVec C l), C) :
    ∀ {l} (t : preterm L l) (ts : DVec (term L) l) (ih_ts : DVec C l), C
  | _, preterm.var k, _, _ => hvar k
  | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
  | _, preterm.app t s, ts, ih_ts =>
      term.elim' hvar hfunc t (DVec.cons s ts)
        (DVec.cons (term.elim' hvar hfunc s DVec.nil DVec.nil) ih_ts)

def term.elim {C : Type v}
    (hvar : ∀ (k : ℕ), C)
    (hfunc : ∀ {{l}} (f : L.functions l) (ts : DVec (term L) l) (ih_ts : DVec C l), C) :
    ∀ (t : term L), C :=
  fun t => term.elim' hvar hfunc t DVec.nil DVec.nil

lemma term.elim'_apps {C : Type v}
    (hvar : ∀ (k : ℕ), C)
    (hfunc : ∀ {{l}} (f : L.functions l) (ts : DVec (term L) l) (ih_ts : DVec C l), C)
    {l} (t : preterm L l) (ts : DVec (term L) l) :
    @term.elim' L C hvar hfunc 0 (apps t ts) DVec.nil DVec.nil =
    @term.elim' L C hvar hfunc l t ts (ts.map (term.elim hvar hfunc)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih =>
    simp only [DVec.map, apps]
    exact ih (preterm.app t x)

lemma term.elim_apps {C : Type v}
    (hvar : ∀ (k : ℕ), C)
    (hfunc : ∀ {{l}} (f : L.functions l) (ts : DVec (term L) l) (ih_ts : DVec C l), C)
    {l} (f : L.functions l) (ts : DVec (term L) l) :
    @term.elim L C hvar hfunc (apps (preterm.func f) ts) =
    hfunc f ts (ts.map (@term.elim L C hvar hfunc)) := by
  simp only [term.elim, term.elim'_apps]
  rfl

/-! ## lift_term_at — lifting variables -/

/-- `lift_term_at t n m` raises variables in `t` which are ≥ m by n. -/
@[simp] def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
  | _, preterm.var k, n, m => &(if m ≤ k then k + n else k)
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, n, m => preterm.app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

notation:90 t " ↑' " n " # " m => Fol.lift_term_at t n m

@[reducible] def lift_term {l} (t : preterm L l) (n : ℕ) : preterm L l := lift_term_at t n 0

infixl:100 " ↑ " => Fol.lift_term

@[reducible, simp] def lift_term1 {l} (t : preterm L l) : preterm L l := lift_term t 1

@[simp] lemma lift_term_def {l} (t : preterm L l) (n : ℕ) : lift_term_at t n 0 = lift_term t n :=
  rfl

lemma injective_lift_term_at : ∀ {l} {n m : ℕ},
    Function.Injective (fun (t : preterm L l) => lift_term_at t n m)
  | _, n, m, preterm.var k, preterm.var k', h => by
      simp only [lift_term_at] at h
      have hk := preterm.var.inj h
      split_ifs at hk with h₁ h₂
      all_goals (try exact congrArg preterm.var (by omega))
      all_goals (try exact congrArg preterm.var hk)
  | _, _, _, preterm.var _, preterm.func _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.var _, preterm.app _ _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.func _, preterm.var _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.func _, preterm.func _, h => h
  | _, _, _, preterm.func _, preterm.app _ _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.app _ _, preterm.var _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.app _ _, preterm.func _, h => by simp [lift_term_at] at h
  | _, n, m, preterm.app t₁ t₂, preterm.app t₁' t₂', h => by
      simp only [lift_term_at] at h
      obtain ⟨h1, h2⟩ := preterm.app.inj h
      exact congrArg₂ preterm.app (injective_lift_term_at h1) (injective_lift_term_at h2)

@[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm L l) (m : ℕ), lift_term_at t 0 m = t
  | _, preterm.var k, _ => by simp [lift_term_at]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, m => by
      simp only [lift_term_at, lift_term_at_zero t₁ m, lift_term_at_zero t₂ m]

@[simp] lemma lift_term_zero {l} (t : preterm L l) : lift_term t 0 = t := lift_term_at_zero t 0

/-- Iterated lifts: smaller new position -/
lemma lift_term_at2_small : ∀ {l} (t : preterm L l) (n n') {m m'}, m' ≤ m →
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at (lift_term_at t n' m') n (m + n')
  | _, preterm.var k, n, n', m, m', H => by
      simp only [lift_term_at]
      split_ifs <;> simp_all [lift_term_at] <;> omega
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H => by
      simp only [lift_term_at, lift_term_at2_small t₁ n n' H, lift_term_at2_small t₂ n n' H]

lemma lift_term_at2_medium : ∀ {l} (t : preterm L l) {n} (n') {m m'}, m ≤ m' → m' ≤ m + n →
    lift_term_at (lift_term_at t n m) n' m' = lift_term_at t (n + n') m
  | _, preterm.var k, n, n', m, m', H₁, H₂ => by
      simp only [lift_term_at]
      split_ifs <;> simp_all [lift_term_at] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H₁, H₂ => by
      simp only [lift_term_at, lift_term_at2_medium t₁ n' H₁ H₂, lift_term_at2_medium t₂ n' H₁ H₂]

lemma lift_term2_medium {l} (t : preterm L l) {n} (n') {m'} (h : m' ≤ n) :
    lift_term_at (lift_term t n) n' m' = lift_term t (n + n') :=
  lift_term_at2_medium t n' (Nat.zero_le _) (by omega)

lemma lift_term2 {l} (t : preterm L l) (n n') :
    lift_term (lift_term t n) n' = lift_term t (n + n') :=
  lift_term2_medium t n' (Nat.zero_le _)

lemma lift_term_at2_eq {l} (t : preterm L l) (n n' m : ℕ) :
    lift_term_at (lift_term_at t n m) n' (m + n) = lift_term_at t (n + n') m :=
  lift_term_at2_medium t n' (Nat.le_add_right _ _) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm L l) {n} (n') {m m'} (H : m + n ≤ m') :
    lift_term_at (lift_term_at t n m) n' m' =
    lift_term_at (lift_term_at t n' (m' - n)) n m := by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_term_at2_small t n' n H₂, Nat.sub_add_cancel H₁]

@[simp] lemma lift_term_var0 (n : ℕ) : lift_term (&0 : term L) n = &n := by
  simp [lift_term, lift_term_at]

@[simp] lemma lift_term_at_apps {l} (t : preterm L l) (ts : DVec (term L) l) (n m : ℕ) :
    lift_term_at (apps t ts) n m =
    apps (lift_term_at t n m) (ts.map (fun x => lift_term_at x n m)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps, DVec.map]; exact ih (preterm.app t x)

@[simp] lemma lift_term_apps {l} (t : preterm L l) (ts : DVec (term L) l) (n : ℕ) :
    lift_term (apps t ts) n = apps (lift_term t n) (ts.map (fun x => lift_term x n)) :=
  lift_term_at_apps t ts n 0

/-! ## subst_term — substitution -/

/-- `subst_term t s n` substitutes `s` for `(&n)` in `t` and reduces variable levels above n. -/
def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
  | _, preterm.var k, s, n => Fol.subst_realize preterm.var (lift_term s n) n k
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, s, n => preterm.app (subst_term t₁ s n) (subst_term t₂ s n)

@[simp] lemma subst_term_var_lt (s : term L) {k n : ℕ} (H : k < n) :
    subst_term (preterm.var k) s n = &k := by
  simp only [subst_term, subst_realize, H, if_true]

@[simp] lemma subst_term_var_gt (s : term L) {k n : ℕ} (H : n < k) :
    subst_term (preterm.var k) s n = &(k - 1) := by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [subst_term, subst_realize, h, if_false, H, if_true]

@[simp] lemma subst_term_var_eq (s : term L) (n : ℕ) :
    subst_term (preterm.var n) s n = lift_term_at s n 0 := by
  simp [subst_term, subst_realize]

lemma subst_term_var0 (s : term L) : subst_term (preterm.var 0) s 0 = s := by
  simp [subst_term, subst_realize, lift_term_at_zero]

@[simp] lemma subst_term_func {l} (f : L.functions l) (s : term L) (n : ℕ) :
    subst_term (preterm.func f : preterm L l) s n = preterm.func f := rfl

@[simp] lemma subst_term_app {l} (t₁ : preterm L (l + 1)) (t₂ s : term L) (n : ℕ) :
    subst_term (preterm.app t₁ t₂) s n =
    preterm.app (subst_term t₁ s n) (subst_term t₂ s n) := rfl

@[simp] lemma subst_term_apps {l} (t : preterm L l) (ts : DVec (term L) l) (s : term L)
    (n : ℕ) : subst_term (apps t ts) s n =
    apps (subst_term t s n) (ts.map (fun x => subst_term x s n)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps, DVec.map]; exact ih (preterm.app t x)

/-- Lift then substitute: large case (substituted var is above the lift range) -/
lemma lift_at_subst_term_large : ∀ {l} (t : preterm L l) (s : term L) {n₁} (n₂) {m}, m ≤ n₁ →
    subst_term (lift_term_at t n₂ m) s (n₁ + n₂) = lift_term_at (subst_term t s n₁) n₂ m
  | _, preterm.var k, s, n₁, n₂, m, h => by
      simp only [lift_term_at, subst_term, subst_realize]
      split_ifs with h1 h2 h3 h4 h5 <;>
        first | rfl | omega | (simp [lift_term_at]; omega) |
          (rw [← lift_term2_medium s n₂ (by omega)]) |
          (congr 1; omega) |
          -- Goal: &(k+n₂-1) = &(k-1) ↑' n₂ # m; know m ≤ n₁ < k so m ≤ k-1
          (simp only [lift_term_at]; split_ifs with hm <;> (first | (congr 1; omega) | omega))
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m, h => by
      simp [lift_at_subst_term_large t₁ s n₂ h, lift_at_subst_term_large t₂ s n₂ h]

lemma lift_subst_term_large {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_term (lift_term t n₂) s (n₁ + n₂) = lift_term (subst_term t s n₁) n₂ :=
  lift_at_subst_term_large t s n₂ (Nat.zero_le _)

lemma lift_subst_term_large' {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_term (lift_term t n₂) s (n₂ + n₁) = lift_term (subst_term t s n₁) n₂ := by
  rw [Nat.add_comm]; exact lift_subst_term_large t s n₁ n₂

/-- Lift then substitute: medium case (substituted var is within the lift range) -/
lemma lift_at_subst_term_medium : ∀ {l} (t : preterm L l) (s : term L) {n₁ n₂ m}, m ≤ n₂ →
    n₂ ≤ m + n₁ → subst_term (lift_term_at t (n₁ + 1) m) s n₂ = lift_term_at t n₁ m
  | _, preterm.var k, s, n₁, n₂, m, h₁, h₂ => by
      simp only [lift_term_at, subst_term, subst_realize]
      split_ifs <;> simp_all [subst_realize] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_at_subst_term_medium t₁ s h₁ h₂, lift_at_subst_term_medium t₂ s h₁ h₂]

lemma lift_subst_term_medium {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_term (lift_term t (n₁ + n₂ + 1)) s n₁ = lift_term t (n₁ + n₂) :=
  lift_at_subst_term_medium t s (Nat.zero_le _) (by omega)

lemma lift_at_subst_term_eq {l} (t : preterm L l) (s : term L) (n : ℕ) :
    subst_term (lift_term_at t 1 n) s n = t := by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, lift_at_subst_term_medium t s (le_refl n) (le_refl n), lift_term_at_zero]

@[simp] lemma lift_term1_subst_term {l} (t : preterm L l) (s : term L) :
    subst_term (lift_term t 1) s 0 = t :=
  lift_at_subst_term_eq t s 0

/-- Lift then substitute: small case -/
lemma lift_at_subst_term_small : ∀ {l} (t : preterm L l) (s : term L) (n₁ n₂ m : ℕ),
    subst_term (lift_term_at t n₁ (m + n₂ + 1)) (lift_term_at s n₁ m) n₂ =
    lift_term_at (subst_term t s n₂) n₁ (m + n₂)
  | _, preterm.var k, s, n₁, n₂, m => by
      rcases Nat.lt_trichotomy k n₂ with hk | hk | hk
      · -- k < n₂: subst gives &k, lift gives k (since ¬(m+n₂+1 ≤ k))
        have h1 : ¬(m + n₂ + 1 ≤ k) := by omega
        have h2 : ¬(m + n₂ ≤ k) := by omega
        simp only [lift_term_at, h1, if_false, subst_term, subst_realize, hk, if_true,
          h2, if_false]
      · -- k = n₂: use lift_term_at2_small
        -- After hk: k = n₂. Goal with n₂ replaced by k everywhere:
        -- subst_term (var k ↑' n₁ # m+k+1) (s ↑' n₁ # m) k = (subst_term (var k) s k) ↑' n₁ # m+k
        -- Since m+k+1 > k, lift of var k at (m+k+1) gives var k.
        -- subst_term (var k) (s ↑' n₁ # m) k = (s ↑' n₁ # m) ↑ k (since k = n₂ exactly)
        -- subst_term (var k) s k = s ↑ k
        -- Need: (s ↑' n₁ # m) ↑ k = (s ↑ k) ↑' n₁ # m+k = lift_term_at2_small
        -- rewrite n₂ as k throughout using hk
        rw [← hk]
        simp only [lift_term_at, show ¬(m + k + 1 ≤ k) from by omega, if_false,
          subst_term, subst_realize, lt_irrefl, if_false, lift_term]
        exact lift_term_at2_small s n₁ k (Nat.zero_le m)
      · -- k > n₂: subst gives &(k-1), lift depends on m+n₂+1 ≤ k
        by_cases h1 : m + n₂ + 1 ≤ k
        · -- k ≥ m+n₂+1: lift gives &(k+n₁), substitute gives &(k+n₁-1)
          have h2 : m + n₂ ≤ k - 1 := by omega
          have hk1 : 1 ≤ k := by omega
          -- lhs: lift var k at (m+n₂+1) gives var (k+n₁); subst at n₂: n₂ < k+n₁, gives &(k+n₁-1)
          -- rhs: subst var k at n₂: n₂ < k, gives &(k-1); lift &(k-1) at (m+n₂): m+n₂ ≤ k-1, gives &(k-1+n₁)
          -- need k+n₁-1 = k-1+n₁
          have hknlt : ¬(k < n₂) := Nat.lt_asymm hk
          have hkn1lt : ¬(k + n₁ < n₂) := by omega
          simp only [lift_term_at, h1, if_true, subst_term, subst_realize,
            hknlt, if_false, hkn1lt, show n₂ < k + n₁ from by omega, if_true, h2, if_true, hk,
            if_true]
          exact congrArg preterm.var (by omega)
        · -- k < m+n₂+1 but k > n₂: so n₂ < k < m+n₂+1
          -- lift gives &k (since ¬(m+n₂+1 ≤ k)), subst gives &(k-1) (since k > n₂)
          -- and ¬(m+n₂ ≤ k-1) because k ≤ m+n₂, so k-1 < m+n₂
          have h2 : ¬(m + n₂ ≤ k - 1) := by omega
          simp only [lift_term_at, h1, if_false, subst_term, subst_realize,
            Nat.lt_asymm hk, if_false, hk, if_true, h2, if_false]
  | _, preterm.func _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m => by
      simp [lift_at_subst_term_small t₁ s n₁ n₂ m, lift_at_subst_term_small t₂ s n₁ n₂ m]

/-- Double substitution lemma -/
lemma subst_term2 : ∀ {l} (t : preterm L l) (s₁ s₂ : term L) (n₁ n₂ : ℕ),
    subst_term (subst_term t s₁ n₁) s₂ (n₁ + n₂) =
    subst_term (subst_term t s₂ (n₁ + n₂ + 1)) (subst_term s₁ s₂ n₂) n₁
  | _, preterm.var k, s₁, s₂, n₁, n₂ => by
      -- TODO: port from src/fol.lean:456-476 (complex case analysis)
      sorry
  | _, preterm.func _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s₁, s₂, n₁, n₂ => by
      simp [subst_term2 t₁ s₁ s₂ n₁ n₂, subst_term2 t₂ s₁ s₂ n₁ n₂]

lemma subst_term2_0 {l} (t : preterm L l) (s₁ s₂ : term L) (n : ℕ) :
    subst_term (subst_term t s₁ 0) s₂ n =
    subst_term (subst_term t s₂ (n + 1)) (subst_term s₁ s₂ n) 0 := by
  have h := subst_term2 t s₁ s₂ 0 n
  simp only [Nat.zero_add] at h
  exact h

lemma lift_subst_term_cancel : ∀ {l} (t : preterm L l) (n : ℕ),
    subst_term (lift_term_at t 1 (n + 1)) (&0) n = t
  | _, preterm.var k, n => by
      simp only [lift_term_at, subst_term, subst_realize]
      split_ifs with h1 h2 h3 <;> simp_all [subst_realize, lift_term_at] <;> omega
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, n => by
      simp [lift_subst_term_cancel t₁ n, lift_subst_term_cancel t₂ n]

end Fol
