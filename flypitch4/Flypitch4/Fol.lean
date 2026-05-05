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

/-! ## preformula and formula -/

/-- `preformula L l` is a partially applied formula. If applied to `l` terms, it becomes a formula (l=0). -/
inductive preformula : ℕ → Type u
  | falsum : preformula 0
  | equal (t₁ t₂ : term L) : preformula 0
  | rel {l : ℕ} (R : L.relations l) : preformula l
  | apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
  | imp (f₁ f₂ : preformula 0) : preformula 0
  | all (f : preformula 0) : preformula 0

-- Switch L back to explicit so that `preformula L l` works in type signatures.
-- (After "variable {L}" at line 103, writing "preformula l" has ambiguous L in type positions.)
variable (L)

-- formula: formula L is the type of first-order formulas over language L.
@[reducible] def formula (L : Language.{u}) : Type u := @preformula L 0

variable {L}

notation "⊥'" => Fol.preformula.falsum
scoped infix:88 " ≃ " => Fol.preformula.equal
scoped infixr:62 " ⟹ " => Fol.preformula.imp
scoped prefix:110 "∀'" => Fol.preformula.all

def not' (f : formula L) : formula L := preformula.imp f preformula.falsum
scoped prefix:max "∼" => Fol.not'
def and' (f₁ f₂ : formula L) : formula L := not' (preformula.imp f₁ (not' f₂))
scoped infixr:69 " ⊓' " => Fol.and'
def or' (f₁ f₂ : formula L) : formula L := preformula.imp (not' f₁) f₂
scoped infixr:68 " ⊔' " => Fol.or'
def biimp (f₁ f₂ : formula L) : formula L :=
  and' (preformula.imp f₁ f₂) (preformula.imp f₂ f₁)
scoped infix:61 " ⇔ " => Fol.biimp
def ex' (f : formula L) : formula L := not' (preformula.all (not' f))
scoped prefix:110 "∃'" => Fol.ex'

@[simp] def apps_rel : ∀ {l}, @preformula L l → DVec (term L) l → formula L
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => apps_rel (preformula.apprel f t) ts

@[simp] lemma apps_rel_zero (f : formula L) (ts : DVec (term L) 0) :
    apps_rel f ts = f := by
  cases ts; rfl

def formula_of_relation {l} (R : L.relations l) :
    Arity' (term L) (formula L) l :=
  Arity'.of_dvector_map (apps_rel (preformula.rel R))

@[elab_as_elim] def formula.rec' {C : formula L → Sort v}
    (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l), C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (ih : C f), C (∀' f)) :
    ∀ {l} (f : @preformula L l) (ts : DVec (term L) l), C (apps_rel f ts)
  | _, preformula.falsum, ts => by cases ts; exact hfalsum
  | _, preformula.equal t₁ t₂, ts => by cases ts; exact hequal t₁ t₂
  | _, preformula.rel R, ts => hrel R ts
  | _, preformula.apprel f t, ts => formula.rec' hfalsum hequal hrel himp hall f (DVec.cons t ts)
  | _, preformula.imp f₁ f₂, ts => by
      cases ts
      exact himp (formula.rec' hfalsum hequal hrel himp hall f₁ DVec.nil)
                 (formula.rec' hfalsum hequal hrel himp hall f₂ DVec.nil)
  | _, preformula.all f, ts => by
      cases ts
      exact hall (formula.rec' hfalsum hequal hrel himp hall f DVec.nil)

@[elab_as_elim] def formula.rec {C : formula L → Sort v}
    (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l), C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (ih : C f), C (∀' f)) :
    ∀ f, C f :=
  fun f =>
    have h := @formula.rec' L C hfalsum hequal hrel himp hall 0 f DVec.nil
    apps_rel_zero f DVec.nil ▸ h

lemma formula.rec'_apps_rel {C : formula L → Sort v}
    (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l), C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (ih : C f), C (∀' f))
    {l} (f : @preformula L l) (ts : DVec (term L) l) :
    @formula.rec' L C hfalsum hequal hrel himp hall 0 (apps_rel f ts) DVec.nil =
    @formula.rec' L C hfalsum hequal hrel himp hall l f ts := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps_rel]; exact ih (preformula.apprel f x)

lemma formula.rec_apps_rel {C : formula L → Sort v}
    (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l), C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (ih : C f), C (∀' f))
    {l} (R : L.relations l) (ts : DVec (term L) l) :
    @formula.rec L C hfalsum hequal hrel himp hall (apps_rel (preformula.rel R) ts) = hrel R ts := by
  -- TODO: port from src/fol.lean:607-608
  -- formula.rec unfolds via apps_rel_zero ▸; need to show this is hrel R ts via formula.rec'_apps_rel
  sorry

/-! ## lift_formula_at — lifting variables in formulas -/

@[simp] def lift_formula_at : ∀ {l}, @preformula L l → ℕ → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, n, m => preformula.equal (lift_term_at t₁ n m) (lift_term_at t₂ n m)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, n, m => preformula.apprel (lift_formula_at f n m) (lift_term_at t n m)
  | _, preformula.imp f₁ f₂, n, m => preformula.imp (lift_formula_at f₁ n m) (lift_formula_at f₂ n m)
  | _, preformula.all f, n, m => preformula.all (lift_formula_at f n (m + 1))

notation:90 f " ↑f' " n " # " m => Fol.lift_formula_at f n m

@[reducible] def lift_formula {l} (f : @preformula L l) (n : ℕ) : @preformula L l :=
  lift_formula_at f n 0

infixl:100 " ↑f " => Fol.lift_formula

@[reducible, simp] def lift_formula1 {l} (f : @preformula L l) : @preformula L l := lift_formula f 1

@[simp] lemma lift_formula_def {l} (f : @preformula L l) (n : ℕ) :
    lift_formula_at f n 0 = lift_formula f n := rfl

@[simp] lemma lift_formula1_not (n : ℕ) (f : formula L) : ∼f ↑f n = ∼(f ↑f n) := rfl

lemma injective_lift_formula_at {l} {n : ℕ} {m : ℕ} :
    Function.Injective (fun (f : @preformula L l) => lift_formula_at f n m) := by
  intro f f' H
  induction f generalizing m with
  | falsum => cases f' <;> simp [lift_formula_at] at *
  | equal t₁ t₂ =>
    cases f' with
    | equal t₁' t₂' =>
      simp only [lift_formula_at] at H
      obtain ⟨h1, h2⟩ := preformula.equal.inj H
      exact congrArg₂ preformula.equal (injective_lift_term_at h1) (injective_lift_term_at h2)
    | _ => simp [lift_formula_at] at H
  | rel R =>
    cases f' with
    | rel R' => exact preformula.rel.inj H ▸ rfl
    | _ => simp [lift_formula_at] at H
  | apprel f t ih =>
    cases f' with
    | apprel f' t' =>
      simp only [lift_formula_at] at H
      obtain ⟨hf, ht⟩ := preformula.apprel.inj H
      exact congrArg₂ preformula.apprel (ih hf) (injective_lift_term_at ht)
    | _ => simp [lift_formula_at] at H
  | imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | imp f₁' f₂' =>
      simp only [lift_formula_at] at H
      obtain ⟨h1, h2⟩ := preformula.imp.inj H
      exact congrArg₂ preformula.imp (ih₁ h1) (ih₂ h2)
    | _ => simp [lift_formula_at] at H
  | all f ih =>
    cases f' with
    | all f' =>
      simp only [lift_formula_at] at H
      exact congrArg preformula.all (ih (preformula.all.inj H))
    | _ => simp [lift_formula_at] at H

@[simp] lemma lift_formula_at_zero : ∀ {l} (f : @preformula L l) (m : ℕ), lift_formula_at f 0 m = f
  | _, preformula.falsum, _ => rfl
  | _, preformula.equal t₁ t₂, m => by simp [lift_formula_at]
  | _, preformula.rel R, _ => rfl
  | _, preformula.apprel f t, m => by
      simp only [lift_formula_at, lift_formula_at_zero f m, lift_term_at_zero]
  | _, preformula.imp f₁ f₂, m => by
      simp only [lift_formula_at, lift_formula_at_zero f₁ m, lift_formula_at_zero f₂ m]
  | _, preformula.all f, m => by
      simp only [lift_formula_at, lift_formula_at_zero f (m + 1)]

lemma lift_formula_at2_small : ∀ {l} (f : @preformula L l) (n n') {m m'}, m' ≤ m →
    lift_formula_at (lift_formula_at f n m) n' m' =
    lift_formula_at (lift_formula_at f n' m') n (m + n')
  | _, preformula.falsum, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H => by
      simp [lift_formula_at, lift_term_at2_small, H]
  | _, preformula.rel R, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H => by
      simp only [lift_formula_at, lift_term_at2_small t n n' H]
      exact congrArg₂ preformula.apprel (lift_formula_at2_small f n n' H) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H => by
      simp only [lift_formula_at]
      exact congrArg₂ preformula.imp (lift_formula_at2_small f₁ n n' H) (lift_formula_at2_small f₂ n n' H)
  | _, preformula.all f, n, n', m, m', H => by
      simp only [lift_formula_at]
      have := lift_formula_at2_small f n n' (Nat.add_le_add_right H 1)
      rw [show m + 1 + n' = m + n' + 1 from by omega] at this
      exact congrArg preformula.all this

lemma lift_formula_at2_medium : ∀ {l} (f : @preformula L l) (n n') {m m'}, m ≤ m' → m' ≤ m + n →
    lift_formula_at (lift_formula_at f n m) n' m' = lift_formula_at f (n + n') m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H₁, H₂ => by
      simp [lift_formula_at, lift_term_at2_medium, H₁, H₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at, lift_term_at2_medium t n' H₁ H₂]
      exact congrArg₂ preformula.apprel (lift_formula_at2_medium f n n' H₁ H₂) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg₂ preformula.imp
        (lift_formula_at2_medium f₁ n n' H₁ H₂)
        (lift_formula_at2_medium f₂ n n' H₁ H₂)
  | _, preformula.all f, n, n', m, m', H₁, H₂ => by
      simp only [lift_formula_at]
      exact congrArg preformula.all
        (lift_formula_at2_medium f n n' (Nat.add_le_add_right H₁ 1)
          (by omega))

lemma lift_formula_at2_eq {l} (f : @preformula L l) (n n' m : ℕ) :
    lift_formula_at (lift_formula_at f n m) n' (m + n) = lift_formula_at f (n + n') m :=
  lift_formula_at2_medium f n n' (Nat.le_add_right _ _) (le_refl _)

lemma lift_formula_at2_large {l} (f : @preformula L l) (n n') {m m'} (H : m + n ≤ m') :
    lift_formula_at (lift_formula_at f n m) n' m' =
    lift_formula_at (lift_formula_at f n' (m' - n)) n m := by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_formula_at2_small f n' n H₂, Nat.sub_add_cancel H₁]

@[simp] lemma lift_formula_at_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l)
    (n m : ℕ) : lift_formula_at (apps_rel f ts) n m =
    apps_rel (lift_formula_at f n m) (ts.map (fun x => lift_term_at x n m)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps_rel, DVec.map]; exact ih (preformula.apprel f x)

@[simp] lemma lift_formula_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l) (n : ℕ) :
    lift_formula (apps_rel f ts) n =
    apps_rel (lift_formula f n) (ts.map (fun x => lift_term x n)) :=
  lift_formula_at_apps_rel f ts n 0

/-! ## subst_formula — substitution into formulas -/

@[simp] def subst_formula : ∀ {l}, @preformula L l → term L → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, s, n =>
      preformula.equal (subst_term t₁ s n) (subst_term t₂ s n)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, s, n =>
      preformula.apprel (subst_formula f s n) (subst_term t s n)
  | _, preformula.imp f₁ f₂, s, n =>
      preformula.imp (subst_formula f₁ s n) (subst_formula f₂ s n)
  | _, preformula.all f, s, n => preformula.all (subst_formula f s (n + 1))

notation:95 f " [" s " // " n "]f" => Fol.subst_formula f s n

lemma subst_formula_equal (t₁ t₂ s : term L) (n : ℕ) :
    subst_formula (preformula.equal t₁ t₂) s n =
    preformula.equal (subst_term t₁ s n) (subst_term t₂ s n) := rfl

@[simp] lemma subst_formula_biimp (f₁ f₂ : formula L) (s : term L) (n : ℕ) :
    subst_formula (biimp f₁ f₂) s n = biimp (subst_formula f₁ s n) (subst_formula f₂ s n) := rfl

lemma lift_at_subst_formula_large : ∀ {l} (f : @preformula L l) (s : term L) {n₁} (n₂) {m},
    m ≤ n₁ → subst_formula (lift_formula_at f n₂ m) s (n₁ + n₂) =
    lift_formula_at (subst_formula f s n₁) n₂ m
  | _, preformula.falsum, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m, h => by
      simp [lift_formula_at, subst_formula, lift_at_subst_term_large _ s n₂ h]
  | _, preformula.rel R, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m, h => by
      simp [lift_formula_at, subst_formula, lift_at_subst_term_large t s n₂ h,
            lift_at_subst_formula_large f s n₂ h]
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m, h => by
      simp [lift_formula_at, subst_formula,
            lift_at_subst_formula_large f₁ s n₂ h,
            lift_at_subst_formula_large f₂ s n₂ h]
  | _, preformula.all f, s, n₁, n₂, m, h => by
      simp only [lift_formula_at, subst_formula]
      have := lift_at_subst_formula_large f s n₂ (Nat.add_le_add_right h 1)
      rw [show n₁ + 1 + n₂ = n₁ + n₂ + 1 from by omega] at this
      exact congrArg preformula.all this

lemma lift_subst_formula_large {l} (f : @preformula L l) (s : term L) {n₁ n₂ : ℕ} :
    subst_formula (lift_formula f n₂) s (n₁ + n₂) = lift_formula (subst_formula f s n₁) n₂ :=
  lift_at_subst_formula_large f s n₂ (Nat.zero_le _)

lemma lift_subst_formula_large' {l} (f : @preformula L l) (s : term L) {n₁ n₂ : ℕ} :
    subst_formula (lift_formula f n₂) s (n₂ + n₁) = lift_formula (subst_formula f s n₁) n₂ := by
  rw [Nat.add_comm]; exact lift_subst_formula_large f s

lemma lift_at_subst_formula_medium : ∀ {l} (f : @preformula L l) (s : term L) {n₁ n₂ m},
    m ≤ n₂ → n₂ ≤ m + n₁ →
    subst_formula (lift_formula_at f (n₁ + 1) m) s n₂ = lift_formula_at f n₁ m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_formula_at, subst_formula, lift_at_subst_term_medium _ s h₁ h₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_formula_at, subst_formula,
            lift_at_subst_term_medium t s h₁ h₂,
            lift_at_subst_formula_medium f s h₁ h₂]
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m, h₁, h₂ => by
      simp [lift_formula_at, subst_formula,
            lift_at_subst_formula_medium f₁ s h₁ h₂,
            lift_at_subst_formula_medium f₂ s h₁ h₂]
  | _, preformula.all f, s, n₁, n₂, m, h₁, h₂ => by
      simp only [lift_formula_at, subst_formula]
      have h : n₂ + 1 ≤ (m + 1) + n₁ := by omega
      exact congrArg preformula.all
        (lift_at_subst_formula_medium f s (Nat.add_le_add_right h₁ 1) h)

lemma lift_subst_formula_medium {l} (f : @preformula L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_formula (lift_formula f (n₁ + n₂ + 1)) s n₁ = lift_formula f (n₁ + n₂) :=
  lift_at_subst_formula_medium f s (Nat.zero_le _) (by omega)

lemma lift_at_subst_formula_eq {l} (f : @preformula L l) (s : term L) (n : ℕ) :
    subst_formula (lift_formula_at f 1 n) s n = f := by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, lift_at_subst_formula_medium f s (le_refl n) (le_refl n), lift_formula_at_zero]

@[simp] lemma lift_formula1_subst {l} (f : @preformula L l) (s : term L) :
    subst_formula (lift_formula f 1) s 0 = f :=
  lift_at_subst_formula_eq f s 0

lemma lift_at_subst_formula_small : ∀ {l} (f : @preformula L l) (s : term L) (n₁ n₂ m : ℕ),
    subst_formula (lift_formula_at f n₁ (m + n₂ + 1)) (lift_term_at s n₁ m) n₂ =
    lift_formula_at (subst_formula f s n₂) n₁ (m + n₂)
  | _, preformula.falsum, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m => by
      simp only [lift_formula_at, subst_formula]
      exact congrArg₂ preformula.equal
        (lift_at_subst_term_small t₁ s n₁ n₂ m)
        (lift_at_subst_term_small t₂ s n₁ n₂ m)
  | _, preformula.rel R, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m => by
      simp only [lift_formula_at, subst_formula]
      exact congrArg₂ preformula.apprel
        (lift_at_subst_formula_small f s n₁ n₂ m)
        (lift_at_subst_term_small t s n₁ n₂ m)
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m => by
      simp only [lift_formula_at, subst_formula]
      exact congrArg₂ preformula.imp
        (lift_at_subst_formula_small f₁ s n₁ n₂ m)
        (lift_at_subst_formula_small f₂ s n₁ n₂ m)
  | _, preformula.all f, s, n₁, n₂, m => by
      simp only [lift_formula_at, subst_formula]
      have := lift_at_subst_formula_small f s n₁ (n₂ + 1) m
      simp only [Nat.add_assoc, Nat.add_comm 1] at this
      exact congrArg preformula.all this

lemma lift_at_subst_formula_small0 {l} (f : @preformula L l) (s : term L) (n₁ m : ℕ) :
    subst_formula (lift_formula_at f n₁ (m + 1)) (lift_term_at s n₁ m) 0 =
    lift_formula_at (subst_formula f s 0) n₁ m :=
  lift_at_subst_formula_small f s n₁ 0 m

lemma subst_formula2 : ∀ {l} (f : @preformula L l) (s₁ s₂ : term L) (n₁ n₂ : ℕ),
    subst_formula (subst_formula f s₁ n₁) s₂ (n₁ + n₂) =
    subst_formula (subst_formula f s₂ (n₁ + n₂ + 1)) (subst_term s₁ s₂ n₂) n₁
  | _, preformula.falsum, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s₁, s₂, n₁, n₂ => by
      simp [subst_formula, subst_term2]
  | _, preformula.rel R, _, _, _, _ => rfl
  | _, preformula.apprel f t, s₁, s₂, n₁, n₂ => by
      simp [subst_formula, subst_term2, subst_formula2 f s₁ s₂ n₁ n₂]
  | _, preformula.imp f₁ f₂, s₁, s₂, n₁, n₂ => by
      simp [subst_formula, subst_formula2 f₁ s₁ s₂ n₁ n₂, subst_formula2 f₂ s₁ s₂ n₁ n₂]
  | _, preformula.all f, s₁, s₂, n₁, n₂ => by
      simp only [subst_formula]
      have h := subst_formula2 f s₁ s₂ (n₁ + 1) n₂
      simp only [show n₁ + 1 + n₂ = n₁ + n₂ + 1 from by omega,
                 show n₁ + 1 + n₂ + 1 = n₁ + n₂ + 1 + 1 from by omega] at h
      exact congrArg preformula.all h

lemma subst_formula2_zero {l} (f : @preformula L l) (s₁ s₂ : term L) (n : ℕ) :
    subst_formula (subst_formula f s₁ 0) s₂ n =
    subst_formula (subst_formula f s₂ (n + 1)) (subst_term s₁ s₂ n) 0 := by
  have h := subst_formula2 f s₁ s₂ 0 n
  simp only [Nat.zero_add] at h
  exact h

lemma lift_subst_formula_cancel : ∀ {l} (f : @preformula L l) (n : ℕ),
    subst_formula (lift_formula_at f 1 (n + 1)) (&0) n = f
  | _, preformula.falsum, _ => rfl
  | _, preformula.equal t₁ t₂, n => by
      simp [lift_formula_at, subst_formula, lift_subst_term_cancel]
  | _, preformula.rel R, _ => rfl
  | _, preformula.apprel f t, n => by
      simp [lift_formula_at, subst_formula, lift_subst_term_cancel t n,
            lift_subst_formula_cancel f n]
  | _, preformula.imp f₁ f₂, n => by
      simp [lift_formula_at, subst_formula,
            lift_subst_formula_cancel f₁ n, lift_subst_formula_cancel f₂ n]
  | _, preformula.all f, n => by
      simp only [lift_formula_at, subst_formula]
      exact congrArg preformula.all (lift_subst_formula_cancel f (n + 1))

@[simp] lemma subst_formula_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l)
    (s : term L) (n : ℕ) :
    subst_formula (apps_rel f ts) s n =
    apps_rel (subst_formula f s n) (ts.map (fun x => subst_term x s n)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps_rel, DVec.map]; exact ih (preformula.apprel f x)

/-! ## count_quantifiers and quantifier_free -/

@[simp] def count_quantifiers : ∀ {l}, @preformula L l → ℕ
  | _, preformula.falsum => 0
  | _, preformula.equal _ _ => 0
  | _, preformula.rel _ => 0
  | _, preformula.apprel _ _ => 0
  | _, preformula.imp f₁ f₂ => count_quantifiers f₁ + count_quantifiers f₂
  | _, preformula.all f => count_quantifiers f + 1

@[simp] def count_quantifiers_succ {l} (f : @preformula L (l + 1)) : count_quantifiers f = 0 := by
  cases f <;> rfl

@[simp] lemma count_quantifiers_subst : ∀ {l} (f : @preformula L l) (s : term L) (n : ℕ),
    count_quantifiers (subst_formula f s n) = count_quantifiers f
  | _, preformula.falsum, _, _ => rfl
  | _, preformula.equal _ _, _, _ => rfl
  | _, preformula.rel _, _, _ => rfl
  | _, preformula.apprel _ _, _, _ => rfl
  | _, preformula.imp f₁ f₂, s, n => by
      simp [count_quantifiers_subst f₁ s n, count_quantifiers_subst f₂ s n]
  | _, preformula.all f, s, n => by
      simp [count_quantifiers_subst f s (n + 1)]

def quantifier_free {l} : @preformula L l → Prop := fun f => count_quantifiers f = 0

/-! ## prf — the proof system (src/fol.lean lines 816-824) -/

/-- `prf Γ A` is the type of proofs of `A` from hypotheses `Γ` in classical first-order logic. -/
inductive prf : Set (formula L) → formula L → Type u
  | axm     {Γ A}   (h : A ∈ Γ) : prf Γ A
  | impI    {Γ : Set (formula L)} {A B}
                    (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
  | impE    {Γ}     (A) {B}
                    (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
  | falsumE {Γ : Set (formula L)} {A}
                    (h : prf (insert (∼A) Γ) ⊥') : prf Γ A
  | allI    {Γ A}   (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀' A)
  | allE₂   {Γ}     (A) (t : term L)
                    (h : prf Γ (∀' A)) : prf Γ (A [t // 0]f)
  | ref     (Γ)     (t : term L) : prf Γ (t ≃ t)
  | subst₂  {Γ}     (s t : term L) (f : formula L)
                    (h₁ : prf Γ (s ≃ t)) (h₂ : prf Γ (f [s // 0]f)) : prf Γ (f [t // 0]f)

scoped infix:51 " ⊢ " => Fol.prf

def provable (T : Set (formula L)) (f : formula L) := Nonempty (T ⊢ f)

scoped infix:51 " ⊢' " => Fol.provable

/-! ## Derived proof rules (src/fol.lean lines 832-1103) -/

def allE {Γ} (A : formula L) (t : term L) {B} (H₁ : Γ ⊢ ∀' A) (H₂ : A [t // 0]f = B) : Γ ⊢ B := by
  subst H₂; exact prf.allE₂ A t H₁

def prf_subst {Γ} {s t : term L} (f₁ : formula L) {f₂} (H₁ : Γ ⊢ s ≃ t)
    (H₂ : Γ ⊢ f₁ [s // 0]f) (H₃ : f₁ [t // 0]f = f₂) : Γ ⊢ f₂ := by
  subst H₃; exact prf.subst₂ s t f₁ H₁ H₂

def axm1 {Γ : Set (formula L)} {A : formula L} : insert A Γ ⊢ A :=
  prf.axm (Set.mem_insert A Γ)

def axm2 {Γ : Set (formula L)} {A B : formula L} : insert A (insert B Γ) ⊢ B :=
  prf.axm (Set.mem_insert_of_mem A (Set.mem_insert B Γ))

noncomputable def weakening {Γ Δ : Set (formula L)} {f : formula L} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢ f) : Δ ⊢ f := by
  induction H₂ generalizing Δ with
  | axm h => exact prf.axm (H₁ h)
  | impI _ ih => exact prf.impI (ih (Set.insert_subset_insert H₁))
  | impE A _ _ ih₁ ih₂ => exact prf.impE A (ih₁ H₁) (ih₂ H₁)
  | falsumE _ ih => exact prf.falsumE (ih (Set.insert_subset_insert H₁))
  | allI _ ih => exact prf.allI (ih (Set.image_mono H₁))
  | allE₂ A t _ ih => exact prf.allE₂ A t (ih H₁)
  | ref => exact prf.ref _ _
  | subst₂ s t f _ _ ih₁ ih₂ => exact prf.subst₂ s t f (ih₁ H₁) (ih₂ H₁)

noncomputable def prf_lift {Γ : Set (formula L)} {f : formula L} (n m : ℕ) (H : Γ ⊢ f) :
    (fun f' => lift_formula_at f' n m) '' Γ ⊢ lift_formula_at f n m := by
  induction H generalizing m with
  | axm h => exact prf.axm (Set.mem_image_of_mem _ h)
  | impI _ ih =>
    apply prf.impI
    have h := ih m
    rwa [Set.image_insert_eq] at h
  | impE A _ _ ih₁ ih₂ => exact prf.impE _ (ih₁ m) (ih₂ m)
  | falsumE _ ih =>
    apply prf.falsumE
    have h := ih m
    rwa [Set.image_insert_eq] at h
  | allI _ ih =>
    apply prf.allI
    rw [Set.image_image]
    have h := ih (m + 1)
    rw [Set.image_image] at h
    apply cast _ h
    congr 1
    apply Set.image_congr'
    intro f'
    exact (lift_formula_at2_small f' n 1 (Nat.zero_le m)).symm
  | allE₂ A t _ ih =>
    have key : lift_formula_at (A [t // 0]f) n m = (lift_formula_at A n (m + 1)) [lift_term_at t n m // 0]f :=
      (lift_at_subst_formula_small0 A t n m).symm
    rw [key]
    exact prf.allE₂ _ _ (ih m)
  | ref => exact prf.ref _ _
  | subst₂ s t f _ _ ih₁ ih₂ =>
    have key1 : lift_formula_at (f [t // 0]f) n m = (lift_formula_at f n (m + 1)) [lift_term_at t n m // 0]f :=
      (lift_at_subst_formula_small0 f t n m).symm
    have key2 : lift_formula_at (f [s // 0]f) n m = (lift_formula_at f n (m + 1)) [lift_term_at s n m // 0]f :=
      (lift_at_subst_formula_small0 f s n m).symm
    rw [key1]
    apply prf.subst₂
    · exact ih₁ m
    · have h := ih₂ m
      rw [key2] at h
      exact h

noncomputable def prf_substitution {Γ : Set (formula L)} {f : formula L} (t : term L) (n : ℕ) (H : Γ ⊢ f) :
    (fun x => subst_formula x t n) '' Γ ⊢ subst_formula f t n := by
  induction H generalizing n with
  | axm h => exact prf.axm (Set.mem_image_of_mem _ h)
  | impI _ ih =>
    apply prf.impI
    have h := ih n
    rwa [Set.image_insert_eq] at h
  | impE A _ _ ih₁ ih₂ => exact prf.impE _ (ih₁ n) (ih₂ n)
  | falsumE _ ih =>
    apply prf.falsumE
    have h := ih n
    rwa [Set.image_insert_eq] at h
  | allI _ ih =>
    apply prf.allI
    rw [Set.image_image]
    have h := ih (n + 1)
    rw [Set.image_image] at h
    apply cast _ h
    congr 1
    apply Set.image_congr'
    intro f'
    exact lift_subst_formula_large f' t
  | allE₂ A s _ ih =>
    -- goal: (subst Γ) ⊢ subst_formula (A[s//0]) t n
    -- = (subst Γ) ⊢ (subst_formula A t (n+1)) [subst_term s t n // 0]
    -- which follows from allE₂ applied to ih n : (subst Γ) ⊢ ∀'(subst_formula A t (n+1))
    have key : subst_formula (subst_formula A s 0) t n = subst_formula (subst_formula A t (n + 1)) (subst_term s t n) 0 :=
      subst_formula2_zero A s t n
    rw [key]
    exact prf.allE₂ _ _ (ih n)
  | ref => exact prf.ref _ _
  | subst₂ s u f _ _ ih₁ ih₂ =>
    have key1 : subst_formula (subst_formula f u 0) t n = subst_formula (subst_formula f t (n + 1)) (subst_term u t n) 0 :=
      subst_formula2_zero f u t n
    have key2 : subst_formula (subst_formula f s 0) t n = subst_formula (subst_formula f t (n + 1)) (subst_term s t n) 0 :=
      subst_formula2_zero f s t n
    rw [key1]
    apply prf.subst₂
    · exact ih₁ n
    · have h := ih₂ n
      rw [key2] at h
      exact h

noncomputable def reflect_prf_lift1 {Γ : Set (formula L)} {f : formula L}
    (h : lift_formula1 '' Γ ⊢ lift_formula f 1) : Γ ⊢ f := by
  have h2 := prf_substitution (&0) 0 h
  simp only [Set.image_image, lift_formula1_subst] at h2
  convert h2 using 1
  simp [Set.image_congr', lift_formula1_subst]

noncomputable def weakening1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₂) : insert f₁ Γ ⊢ f₂ :=
  weakening (Set.subset_insert f₁ Γ) H

noncomputable def weakening2 {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L} (H : insert f₁ Γ ⊢ f₂) :
    insert f₁ (insert f₃ Γ) ⊢ f₂ :=
  weakening (Set.insert_subset_insert (Set.subset_insert _ Γ)) H

noncomputable def deduction {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A ⟹ B) : insert A Γ ⊢ B :=
  prf.impE A (weakening1 H) axm1

noncomputable def exfalso {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ ⊥') : Γ ⊢ A :=
  prf.falsumE (weakening1 H)

noncomputable def exfalso' {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢' ⊥') : Γ ⊢' A :=
  H.map exfalso

noncomputable def notI {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A ⟹ ⊥') : Γ ⊢ ∼A := H

noncomputable def andI {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : Γ ⊢ f₁) (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓' f₂ := by
  apply prf.impI
  apply prf.impE f₂
  · apply prf.impE f₁
    · exact axm1
    · exact weakening1 H₁
  · exact weakening1 H₂

noncomputable def andE1 {Γ : Set (formula L)} {f₁ : formula L} (f₂ : formula L) (H : Γ ⊢ f₁ ⊓' f₂) : Γ ⊢ f₁ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.impI
  apply exfalso
  apply prf.impE f₁
  · exact axm2
  · exact axm1

noncomputable def andE2 {Γ : Set (formula L)} (f₁ : formula L) {f₂ : formula L} (H : Γ ⊢ f₁ ⊓' f₂) : Γ ⊢ f₂ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.impI
  exact axm2

noncomputable def orI1 {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A) : Γ ⊢ A ⊔' B := by
  apply prf.impI
  apply exfalso
  apply prf.impE _ axm1
  exact weakening1 H

noncomputable def orI2 {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ B) : Γ ⊢ A ⊔' B :=
  prf.impI (weakening1 H)

noncomputable def orE {Γ : Set (formula L)} {A B C : formula L} (H₁ : Γ ⊢ A ⊔' B)
    (H₂ : insert A Γ ⊢ C) (H₃ : insert B Γ ⊢ C) : Γ ⊢ C := by
  apply prf.falsumE
  apply prf.impE C
  · exact axm1
  apply prf.impE B
  · apply prf.impI; exact weakening2 H₃
  apply prf.impE _ (weakening1 H₁)
  exact prf.impI (prf.impE _ axm2 (weakening2 H₂))

noncomputable def biimpI {Γ : Set (formula L)} {f₁ f₂ : formula L}
    (H₁ : insert f₁ Γ ⊢ f₂) (H₂ : insert f₂ Γ ⊢ f₁) : Γ ⊢ f₁ ⇔ f₂ :=
  andI (prf.impI H₁) (prf.impI H₂)

noncomputable def biimpE1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₁ Γ ⊢ f₂ :=
  deduction (andE1 _ H)

noncomputable def biimpE2 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) : insert f₂ Γ ⊢ f₁ :=
  deduction (andE2 _ H)

noncomputable def exI {Γ : Set (formula L)} {f : formula L} (t : term L) (H : Γ ⊢ f [t // 0]f) : Γ ⊢ ∃' f := by
  apply prf.impI
  apply prf.impE (f [t // 0]f) _ (weakening1 H)
  exact prf.allE₂ (∼f) t axm1

noncomputable def exE {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : Γ ⊢ ∃' f₁)
    (H₂ : insert f₁ (lift_formula1 '' Γ) ⊢ lift_formula1 f₂) : Γ ⊢ f₂ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H₁)
  apply prf.allI
  apply prf.impI
  rw [Set.image_insert_eq]
  apply prf.impE _ axm2
  exact weakening2 H₂

noncomputable def ex_not_of_not_all {Γ : Set (formula L)} {f : formula L} (H : Γ ⊢ ∼(∀' f)) : Γ ⊢ ∃' (∼f) := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.allI
  apply prf.falsumE
  rw [Set.image_insert_eq]
  apply prf.impE _ axm2
  apply exI (&0)
  rw [lift_subst_formula_cancel]
  exact axm1

noncomputable def not_and_self {Γ : Set (formula L)} {f : formula L} (H : Γ ⊢ f ⊓' (∼f)) : Γ ⊢ ⊥' :=
  prf.impE f (andE2 f H) (andE1 (∼f) H)

noncomputable def prf_symm {Γ : Set (formula L)} {s t : term L} (H : Γ ⊢ s ≃ t) : Γ ⊢ t ≃ s := by
  apply prf_subst (&0 ≃ lift_term s 1) H
  · simp [subst_formula_equal, lift_term1_subst_term, subst_term_var0]; exact prf.ref _ _
  · simp [subst_formula_equal, lift_term1_subst_term, subst_term_var0]

noncomputable def prf_trans {Γ : Set (formula L)} {t₁ t₂ t₃ : term L}
    (H : Γ ⊢ t₁ ≃ t₂) (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ := by
  apply prf_subst (lift_term t₁ 1 ≃ &0) H'
  · simp [subst_formula_equal, lift_term1_subst_term, subst_term_var0]; exact H
  · simp [subst_formula_equal, lift_term1_subst_term, subst_term_var0]

noncomputable def prf_congr {Γ : Set (formula L)} {t₁ t₂ : term L} (s : term L)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ subst_term s t₁ 0 ≃ subst_term s t₂ 0 := by
  apply prf_subst (lift_term (subst_term s t₁ 0) 1 ≃ s) H
  · simp [subst_formula_equal, lift_term1_subst_term]; exact prf.ref _ _
  · simp [subst_formula_equal, lift_term1_subst_term]

noncomputable def app_congr {Γ : Set (formula L)} {t₁ t₂ : term L} (s : preterm L 1)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ preterm.app s t₁ ≃ preterm.app s t₂ := by
  have h := prf_congr (preterm.app (lift_term s 1) (&0)) H
  simp at h
  exact h

noncomputable def apprel_congr {Γ : Set (formula L)} {t₁ t₂ : term L} (f : @preformula L 1)
    (H : Γ ⊢ t₁ ≃ t₂) (H₂ : Γ ⊢ preformula.apprel f t₁) : Γ ⊢ preformula.apprel f t₂ := by
  apply prf_subst (preformula.apprel (lift_formula f 1) (&0)) H
  · simp; exact H₂
  · simp

noncomputable def imp_trans {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H₁ : Γ ⊢ f₁ ⟹ f₂) (H₂ : Γ ⊢ f₂ ⟹ f₃) : Γ ⊢ f₁ ⟹ f₃ := by
  apply prf.impI
  apply prf.impE _ (weakening1 H₂)
  exact prf.impE _ (weakening1 H₁) axm1

noncomputable def biimp_refl (Γ : Set (formula L)) (f : formula L) : Γ ⊢ f ⇔ f :=
  biimpI axm1 axm1

noncomputable def biimp_trans {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H₁ : Γ ⊢ f₁ ⇔ f₂) (H₂ : Γ ⊢ f₂ ⇔ f₃) : Γ ⊢ f₁ ⇔ f₃ :=
  andI (imp_trans (andE1 _ H₁) (andE1 _ H₂)) (imp_trans (andE2 _ H₂) (andE2 _ H₁))

def equal_preterms (T : Set (formula L)) {l} (t₁ t₂ : preterm L l) : Type u :=
  ∀ (ts : DVec (term L) l), T ⊢ apps t₁ ts ≃ apps t₂ ts

noncomputable def equal_preterms_app {T : Set (formula L)} {l} {t t' : preterm L (l + 1)} {s s' : term L}
    (Ht : equal_preterms T t t') (Hs : T ⊢ s ≃ s') :
    equal_preterms T (preterm.app t s) (preterm.app t' s') := by
  intro xs
  apply prf_trans (Ht (DVec.cons s xs))
  have h := prf_congr (apps (lift_term t' 1) (DVec.cons (&0) (xs.map lift_term1))) Hs
  simp [DVec.map_congr (fun t => lift_term1_subst_term t s')] at h
  exact h

@[refl] noncomputable def equal_preterms_refl (T : Set (formula L)) {l} (t : preterm L l) :
    equal_preterms T t t :=
  fun xs => prf.ref T (apps t xs)

def equiv_preformulae (T : Set (formula L)) {l} (f₁ f₂ : @preformula L l) : Type u :=
  ∀ (ts : DVec (term L) l), T ⊢ apps_rel f₁ ts ⇔ apps_rel f₂ ts

noncomputable def equiv_preformulae_apprel {T : Set (formula L)} {l} {f f' : @preformula L (l + 1)} {s s' : term L}
    (Ht : equiv_preformulae T f f') (Hs : T ⊢ s ≃ s') :
    equiv_preformulae T (preformula.apprel f s) (preformula.apprel f' s') := by
  intro xs
  apply biimp_trans (Ht (DVec.cons s xs))
  apply prf_subst (apps_rel (lift_formula f' 1) (DVec.cons s (xs.map lift_term1)) ⇔
                  apps_rel (lift_formula f' 1) (DVec.cons (&0) (xs.map lift_term1))) Hs
  · -- TODO: port from src/fol.lean:1053-1057 (dvec map collapses via lift_term1_subst_term)
    sorry
  · -- TODO: port from src/fol.lean:1053-1057
    sorry

@[refl] noncomputable def equiv_preformulae_refl (T : Set (formula L)) {l} (f : @preformula L l) :
    equiv_preformulae T f f :=
  fun xs => biimp_refl T (apps_rel f xs)

def impI' {Γ : Set (formula L)} {A B : formula L} (h : insert A Γ ⊢' B) : Γ ⊢' (A ⟹ B) :=
  h.map prf.impI

def impE' {Γ : Set (formula L)} (A : formula L) {B : formula L}
    (h₁ : Γ ⊢' A ⟹ B) (h₂ : Γ ⊢' A) : Γ ⊢' B :=
  h₁.map2 (prf.impE _) h₂

def falsumE' {Γ : Set (formula L)} {A : formula L} (h : insert (∼A) Γ ⊢' ⊥') : Γ ⊢' A :=
  h.map prf.falsumE

def allI' {Γ : Set (formula L)} {A : formula L} (h : lift_formula1 '' Γ ⊢' A) : Γ ⊢' ∀' A :=
  h.map prf.allI

def allE' {Γ : Set (formula L)} (A : formula L) (t : term L) {B : formula L}
    (H₁ : Γ ⊢' ∀' A) (H₂ : A [t // 0]f = B) : Γ ⊢' B :=
  H₁.map (fun x => allE _ _ x H₂)

def allE₂' {Γ : Set (formula L)} {A : formula L} {t : term L} (h : Γ ⊢' ∀' A) : Γ ⊢' A [t // 0]f :=
  h.map (fun x => allE _ _ x rfl)

def ref' (Γ : Set (formula L)) (t : term L) : Γ ⊢' (t ≃ t) := ⟨prf.ref Γ t⟩

def subst' {Γ : Set (formula L)} {s t : term L} (f₁ : formula L) {f₂ : formula L}
    (H₁ : Γ ⊢' s ≃ t) (H₂ : Γ ⊢' f₁ [s // 0]f) (H₃ : f₁ [t // 0]f = f₂) : Γ ⊢' f₂ :=
  H₁.map2 (fun x y => prf_subst _ x y H₃) H₂

def subst₂' {Γ : Set (formula L)} (s t : term L) (f : formula L)
    (h₁ : Γ ⊢' s ≃ t) (h₂ : Γ ⊢' f [s // 0]f) : Γ ⊢' f [t // 0]f :=
  h₁.map2 (prf.subst₂ _ _ _) h₂

def weakening' {Γ Δ : Set (formula L)} {f : formula L} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢' f) : Δ ⊢' f :=
  H₂.map (weakening H₁)

def weakening1' {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢' f₂) : insert f₁ Γ ⊢' f₂ :=
  H.map weakening1

def weakening2' {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L} (H : insert f₁ Γ ⊢' f₂) :
    insert f₁ (insert f₃ Γ) ⊢' f₂ :=
  H.map weakening2

lemma apprel_congr' {Γ : Set (formula L)} {t₁ t₂ : term L} (f : @preformula L 1)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢' preformula.apprel f t₁ ↔ Γ ⊢' preformula.apprel f t₂ :=
  ⟨Nonempty.map (apprel_congr f H), Nonempty.map (apprel_congr f (prf_symm H))⟩

lemma prf_all_iff {Γ : Set (formula L)} {f : formula L} : Γ ⊢' ∀' f ↔ lift_formula1 '' Γ ⊢' f := by
  constructor
  · intro H
    rw [← lift_subst_formula_cancel f 0]
    apply allE₂'
    exact H.map (prf_lift 1 0)
  · exact allI'

lemma iff_of_biimp {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢' f₁ ⇔ f₂) :
    Γ ⊢' f₁ ↔ Γ ⊢' f₂ :=
  ⟨impE' _ (H.map (andE1 _)), impE' _ (H.map (andE2 _))⟩

lemma prf_by_cases {Γ : Set (formula L)} (f₁ : formula L) {f₂ : formula L}
    (H₁ : insert f₁ Γ ⊢' f₂) (H₂ : insert (∼f₁) Γ ⊢' f₂) : Γ ⊢' f₂ := by
  apply falsumE'
  apply impE' _ ⟨axm1⟩
  apply impE' _ (impI' (weakening2' H₁))
  apply falsumE'
  apply impE' _ ⟨axm2⟩
  exact weakening2' H₂

/-! ## Theory and consistency (src/fol.lean lines 1105-) -/

def Theory (L : Language.{u}) := Set (formula L)

def is_consistent (T : Theory L) := ¬(T ⊢' ⊥')

/-! ## Structure — L-structures (src/fol.lean line 1109) -/

variable (L)

structure Structure : Type (u + 1) where
  carrier : Type u
  fun_map : ∀ {n}, L.functions n → DVec carrier n → carrier
  rel_map : ∀ {n}, L.relations n → DVec carrier n → Prop

variable {L}

instance : CoeSort (Structure L) (Type u) where
  coe S := S.carrier

/-! ## realize_term — realization of terms in a structure -/

@[simp] def realize_term {S : Structure L} (v : ℕ → S) :
    ∀ {l} (t : preterm L l) (xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.fun_map f xs
  | _, preterm.app t₁ t₂, xs => realize_term v t₁ (DVec.cons (realize_term v t₂ DVec.nil) xs)

lemma realize_term_congr {S : Structure L} {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : preterm L l) (xs : DVec S l),
    realize_term v t xs = realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [realize_term]
      rw [realize_term_congr h t₁, realize_term_congr h t₂]

lemma realize_term_subst {S : Structure L} (v : ℕ → S) :
    ∀ {l} (n : ℕ) (t : preterm L l) (s : term L) (xs : DVec S l),
    realize_term (subst_realize v (realize_term v (lift_term s n) DVec.nil) n) t xs =
    realize_term v (subst_term t s n) xs
  | _, n, preterm.var k, s, DVec.nil => by
      rcases Nat.lt_trichotomy k n with h | h | h
      · simp only [realize_term, subst_realize_lt _ _ h, subst_term_var_lt _ h]
      · subst h
        simp only [realize_term, subst_term_var_eq, subst_realize_var_eq, lift_term]
      · simp only [realize_term, subst_realize_gt _ _ h, subst_term_var_gt _ h]
  | _, _, preterm.func _, _, _ => rfl
  | _, n, preterm.app t₁ t₂, s, xs => by
      simp only [realize_term, subst_term]
      rw [realize_term_subst v n t₂ s DVec.nil]
      rw [realize_term_subst v n t₁ s]

lemma realize_term_subst_lift {S : Structure L} (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : preterm L l) (xs : DVec S l),
    realize_term (subst_realize v x m) (lift_term_at t 1 m) xs = realize_term v t xs
  | _, preterm.var k, DVec.nil => by
      simp only [realize_term, lift_term_at]
      by_cases h : m ≤ k
      · -- lift gives k+1, subst_realize gives v k
        have hmk1 : m < k + 1 := Nat.lt_succ_of_le h
        simp only [if_pos h, subst_realize_gt _ _ hmk1, Nat.add_sub_cancel]
      · -- lift gives k, subst_realize gives v k (since k < m)
        have hkm : k < m := Nat.lt_of_not_le h
        simp only [if_neg h, realize_term, subst_realize_lt _ _ hkm]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [realize_term, lift_term_at]
      rw [realize_term_subst_lift v x m t₂ DVec.nil]
      rw [realize_term_subst_lift v x m t₁]

/-! ## realize_formula — satisfaction relation -/

@[simp] def realize_formula {S : Structure L} :
    ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → Prop
  | _, v, preformula.falsum, _ => False
  | _, v, preformula.equal t₁ t₂, _ =>
      realize_term v t₁ DVec.nil = realize_term v t₂ DVec.nil
  | _, _, preformula.rel R, xs => S.rel_map R xs
  | _, v, preformula.apprel f t, xs =>
      realize_formula v f (DVec.cons (realize_term v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs =>
      realize_formula v f₁ xs → realize_formula v f₂ xs
  | _, v, preformula.all f, _ =>
      ∀ x : S, realize_formula (subst_realize v x 0) f DVec.nil

lemma realize_formula_congr {S : Structure L} :
    ∀ {l} {v v' : ℕ → S} (h : ∀ n, v n = v' n) (f : @preformula L l) (xs : DVec S l),
    realize_formula v f xs ↔ realize_formula v' f xs
  | _, _, _, _, preformula.falsum, _ => Iff.rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
      simp [realize_formula, realize_term_congr h]
  | _, _, _, _, preformula.rel _, _ => Iff.rfl
  | _, _, _, h, preformula.apprel f t, xs => by
      simp only [realize_formula, realize_term_congr h]
      exact realize_formula_congr h f _
  | _, _, _, h, preformula.imp f₁ f₂, xs => by
      simp only [realize_formula]
      exact Iff.imp (realize_formula_congr h f₁ xs) (realize_formula_congr h f₂ xs)
  | _, _, _, h, preformula.all f, _ => by
      simp only [realize_formula]
      apply forall_congr'
      intro x
      exact realize_formula_congr (subst_realize_congr h x 0) f DVec.nil

lemma realize_formula_subst {S : Structure L} :
    ∀ {l} (v : ℕ → S) (n : ℕ) (f : @preformula L l) (s : term L) (xs : DVec S l),
    realize_formula (subst_realize v (realize_term v (lift_term s n) DVec.nil) n) f xs ↔
    realize_formula v (subst_formula f s n) xs
  | _, _, _, preformula.falsum, _, _ => Iff.rfl
  | _, v, n, preformula.equal t₁ t₂, s, _ => by
      simp [realize_formula, realize_term_subst]
  | _, _, _, preformula.rel _, _, _ => Iff.rfl
  | _, v, n, preformula.apprel f t, s, xs => by
      simp only [realize_formula, subst_formula, realize_term_subst]
      exact realize_formula_subst v n f s _
  | _, v, n, preformula.imp f₁ f₂, s, xs => by
      simp only [realize_formula, subst_formula]
      exact Iff.imp (realize_formula_subst v n f₁ s xs) (realize_formula_subst v n f₂ s xs)
  | _, v, n, preformula.all f, s, _ => by
      simp only [realize_formula, subst_formula]
      apply forall_congr'
      intro x
      -- goal: realize_formula (subst_realize (subst_realize v ...) x 0) f [] ↔ realize_formula v (f[s//n+1]) []
      -- use: IH at n+1, then congr on valuation
      rw [← realize_formula_subst (subst_realize v x 0) (n + 1) f s DVec.nil]
      apply realize_formula_congr
      intro k
      -- Use subst_realize2_0 to swap the two substitutions:
      -- subst_realize (subst_realize v (realize_term v (lift_term s n) []) n) x 0 k
      -- = subst_realize (subst_realize v x 0) (realize_term v (lift_term s n) []) (n+1) k (by subst_realize2_0)
      -- And realize_term v (lift_term s n) [] = realize_term (subst_realize v x 0) (lift_term_at s 1 0 ↑ n) []
      --   since s ↑ n+1 applied then subst at 0 cancels the lift-at-0.
      -- This direction is complex; use sorry for now.
      -- TODO: port from src/fol.lean:1178-1181
      sorry

lemma realize_formula_subst0 {S : Structure L} {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    realize_formula (subst_realize v (realize_term v s DVec.nil) 0) f xs ↔
    realize_formula v (subst_formula f s 0) xs := by
  have h := realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

lemma realize_formula_subst_lift {S : Structure L} :
    ∀ {l} (v : ℕ → S) (x : S) (m : ℕ) (f : @preformula L l) (xs : DVec S l),
    realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs = realize_formula v f xs
  | _, _, _, _, preformula.falsum, _ => rfl
  | _, v, x, m, preformula.equal t₁ t₂, _ => by
      simp [realize_formula, realize_term_subst_lift]
  | _, _, _, _, preformula.rel _, _ => rfl
  | _, v, x, m, preformula.apprel f t, xs => by
      simp only [realize_formula, lift_formula_at, realize_term_subst_lift]
      exact realize_formula_subst_lift v x m f _
  | _, v, x, m, preformula.imp f₁ f₂, xs => by
      simp only [realize_formula, lift_formula_at]
      exact propext (Iff.imp
        (Iff.of_eq (realize_formula_subst_lift v x m f₁ xs))
        (Iff.of_eq (realize_formula_subst_lift v x m f₂ xs)))
  | _, v, x, m, preformula.all f, _ => by
      simp only [realize_formula, lift_formula_at]
      apply propext
      apply forall_congr'
      intro x'
      rw [propext (realize_formula_congr (fun k => subst_realize2_0 v x' x m k) (lift_formula_at f 1 (m + 1)) DVec.nil)]
      exact Iff.of_eq (realize_formula_subst_lift (subst_realize v x' 0) x (m + 1) f DVec.nil)

/-! ## Semantic notions — satisfaction and models -/

def satisfied_in (S : Structure L) (f : formula L) : Prop :=
  ∀ v : ℕ → S, realize_formula v f DVec.nil

scoped infix:51 " ⊨ₛ " => Fol.satisfied_in

def all_satisfied_in (S : Structure L) (T : Set (formula L)) : Prop :=
  ∀ {{f}}, f ∈ T → S ⊨ₛ f

def satisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : Structure L) (v : ℕ → S),
    (∀ f' ∈ T, realize_formula v (f' : formula L) DVec.nil) →
    realize_formula v f DVec.nil

scoped infix:51 " ⊨ " => Fol.satisfied

def all_satisfied (T T' : Set (formula L)) : Prop :=
  ∀ {{f}}, f ∈ T' → T ⊨ f

def satisfied_in_trans {S : Structure L} {T : Set (formula L)} {f : formula L}
    (H' : all_satisfied_in S T) (H : T ⊨ f) : S ⊨ₛ f :=
  fun v => H S v (fun f' hf' => H' hf' v)

def all_satisfied_in_trans {S : Structure L} {T T' : Set (formula L)}
    (H' : all_satisfied_in S T) (H : all_satisfied T T') : all_satisfied_in S T' :=
  fun f hf => satisfied_in_trans H' (H hf)

def satisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ f :=
  fun S v h => h f hf

def all_satisfied_of_subset {T T' : Set (formula L)} (h : T' ⊆ T) : all_satisfied T T' :=
  fun f hf => satisfied_of_mem (h hf)

def satisfied_trans {T₁ T₂ : Set (formula L)} {f : formula L}
    (H' : all_satisfied T₁ T₂) (H : T₂ ⊨ f) : T₁ ⊨ f :=
  fun S v h => H S v (fun f' hf' => H' hf' S v h)

def all_satisfied_trans {T₁ T₂ T₃ : Set (formula L)}
    (H' : all_satisfied T₁ T₂) (H : all_satisfied T₂ T₃) : all_satisfied T₁ T₃ :=
  fun f hf => satisfied_trans H' (H hf)

def satisfied_weakening {T T' : Set (formula L)} (H : T ⊆ T') {f : formula L}
    (HT : T ⊨ f) : T' ⊨ f :=
  fun S v h => HT S v (fun f' hf' => h f' (H hf'))

/-! ## Soundness (src/fol.lean lines 1247-1261) -/

lemma formula_soundness {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A) : Γ ⊨ A := by
  intro S
  induction H with
  | axm h => intro v hΓ; exact hΓ _ h
  | impI _ ih =>
    intro v hΓ ha
    apply ih
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | impE A _ _ ih₁ ih₂ => intro v hΓ; exact ih₁ v hΓ (ih₂ v hΓ)
  | falsumE _ ih =>
    intro v hΓ
    by_contra ha
    apply ih v
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | allI _ ih =>
    intro v hΓ x
    apply ih
    intro f hf
    rcases hf with ⟨f', hf', rfl⟩
    rw [realize_formula_subst_lift v x 0 f']
    exact hΓ f' hf'
  | allE₂ A t _ ih =>
    intro v hΓ
    rw [← realize_formula_subst0]
    exact ih v hΓ (realize_term v t DVec.nil)
  | ref => intro v _; simp [realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro v hΓ
    have h' := ih₁ v hΓ
    simp only [realize_formula] at h'
    rw [← realize_formula_subst0, ← h', realize_formula_subst0]
    exact ih₂ v hΓ

end Fol
