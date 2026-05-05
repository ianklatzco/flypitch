/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/bfol.lean lines 1-450:
   Boolean-valued first-order logic — bStructure + early semantics. -/

import Flypitch4.Fol
import Mathlib.Order.CompleteBooleanAlgebra

open DVec

namespace Fol

section bfol

/-! ## bStructure — boolean-valued L-structure -/

/-- An L-Structure valued in a complete boolean algebra β.
    Analogous to `Structure L` from Fol.lean, but interpretations of relations
    return values in β rather than Prop. -/
structure bStructure (L : Language.{u}) (β : Type v) [CompleteBooleanAlgebra β] where
  carrier : Type u
  fun_map : ∀ {n}, L.functions n → DVec carrier n → carrier
  rel_map : ∀ {n}, L.relations n → DVec carrier n → β
  /-- Boolean equality on the carrier -/
  eq : carrier → carrier → β
  eq_refl : ∀ x, eq x x = ⊤
  eq_symm : ∀ x y, eq x y = eq y x
  eq_trans : ∀ {x} (y : carrier) {z}, eq x y ⊓ eq y z ≤ eq x z
  fun_congr : ∀ {n} (f : L.functions n) (x y : DVec carrier n),
    (DVec.map2 (eq) x y).fInf ≤ eq (fun_map f x) (fun_map f y)
  rel_congr : ∀ {n} (R : L.relations n) (x y : DVec carrier n),
    (DVec.map2 (eq) x y).fInf ⊓ rel_map R x ≤ rel_map R y

variable {L : Language.{u}} {β : Type v} [CompleteBooleanAlgebra β]

instance : CoeSort (bStructure L β) (Type u) := ⟨bStructure.carrier⟩

attribute [simp] bStructure.eq_refl

variable {S : bStructure L β}

@[simp] lemma eq_drefl : ∀ {n} (x : DVec S n),
    (DVec.map2 S.eq x x).fInf = ⊤
  | _, DVec.nil => rfl
  | _, DVec.cons x xs => by
      simp only [DVec.map2, DVec.fInf_cons, S.eq_refl, eq_drefl xs, inf_top_eq]

lemma eq_dsymm : ∀ {n} (x y : DVec S n),
    (DVec.map2 S.eq x y).fInf = (DVec.map2 S.eq y x).fInf
  | _, DVec.nil, DVec.nil => rfl
  | _, DVec.cons x xs, DVec.cons y ys => by
      simp [S.eq_symm x y, eq_dsymm xs ys]

lemma eq_dtrans : ∀ {n} {x : DVec S n} (y : DVec S n) {z : DVec S n},
    (DVec.map2 S.eq x y).fInf ⊓ (DVec.map2 S.eq y z).fInf ≤ (DVec.map2 S.eq x z).fInf
  | _, DVec.nil, DVec.nil, DVec.nil => by simp
  | _, DVec.cons x xs, DVec.cons y ys, DVec.cons z zs => by
      simp only [DVec.map2, DVec.fInf_cons]
      apply le_inf
      · exact le_trans (inf_le_inf inf_le_left inf_le_left) (S.eq_trans y)
      · exact le_trans (inf_le_inf inf_le_right inf_le_right) (eq_dtrans ys)

lemma subst_realize_congr1 (v v' : ℕ → S) (x : S) (m : ℕ) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v' x m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]; exact iInf_le _ k
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]; exact iInf_le _ (k - 1)

lemma subst_realize_congr2 (v : ℕ → S) (x y : S) (m : ℕ) :
    S.eq x y ≤ ⨅ k : ℕ, S.eq (subst_realize v x m k) (subst_realize v y m k) := by
  rw [le_iInf_iff]
  intro k
  rcases Nat.lt_trichotomy k m with h | h | h
  · simp [subst_realize, h]
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h]

/-! ## boolean_realize_term -/

@[simp] def boolean_realize_term (v : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.fun_map f xs
  | _, preterm.app t₁ t₂, xs =>
      boolean_realize_term v t₁ (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)

lemma boolean_realize_term_congr' {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l),
    boolean_realize_term v t xs = boolean_realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
      simp only [boolean_realize_term]
      rw [boolean_realize_term_congr' h t₂, boolean_realize_term_congr' h t₁]

lemma boolean_realize_term_subst (v : ℕ → S) :
    ∀ {l} (m : ℕ) (t : @preterm L l) (s : term L) (xs : DVec S l),
    boolean_realize_term
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) t xs =
    boolean_realize_term v (subst_term t s m) xs
  | _, m, preterm.var k, s, _ => by
      simp only [boolean_realize_term, subst_term, subst_realize_lt, subst_realize_gt,
                 subst_realize_var_eq]
      rcases Nat.lt_trichotomy k m with h | h | h
      · simp [h, Nat.lt_asymm h]
      · subst h; simp
      · simp [h, Nat.lt_asymm h]
  | _, _, preterm.func _, _, _ => rfl
  | _, m, preterm.app t₁ t₂, s, xs => by
      simp only [boolean_realize_term, subst_term]
      rw [boolean_realize_term_subst v m t₂ s DVec.nil,
          boolean_realize_term_subst v m t₁ s]

lemma boolean_realize_term_subst_lift (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : @preterm L l) (xs : DVec S l),
    boolean_realize_term (subst_realize v x 0) (lift_term_at t 1 m) xs =
    boolean_realize_term v t xs := by
  -- TODO: port from src/bfol.lean:95-104
  sorry

lemma boolean_realize_term_congr_gen (v v' : ℕ → S) :
    ∀ {l} (t : @preterm L l) (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ≤
      S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs')
  | _, preterm.var k, _, _ => le_trans inf_le_left (iInf_le _ k)
  | _, preterm.func f, xs, xs' => le_trans inf_le_right (S.fun_congr f xs xs')
  | _, preterm.app t₁ t₂, xs, xs' => by
      simp only [boolean_realize_term]
      refine le_trans ?_ (boolean_realize_term_congr_gen v v' t₁
        (DVec.cons (boolean_realize_term v t₂ DVec.nil) xs)
        (DVec.cons (boolean_realize_term v' t₂ DVec.nil) xs'))
      simp only [DVec.map2, DVec.fInf_cons]
      apply le_inf
      · exact inf_le_left
      · apply le_inf
        · have h2 := boolean_realize_term_congr_gen v v' t₂ DVec.nil DVec.nil
          simp only [DVec.map2, DVec.fInf_nil, inf_top_eq] at h2
          exact le_trans inf_le_left h2
        · exact inf_le_right

lemma boolean_realize_term_congr_iInf (v v' : ℕ → S) {l} (t : @preterm L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ≤
    S.eq (boolean_realize_term v t xs) (boolean_realize_term v' t xs) := by
  have h := boolean_realize_term_congr_gen v v' t xs xs
  simp only [eq_drefl, inf_top_eq] at h
  exact h

lemma boolean_realize_term_subst_congr (v : ℕ → S) {m} (s s' : term L)
    {l} (t : @preterm L l) (xs : DVec S l) :
    S.eq (boolean_realize_term v (lift_term s m) DVec.nil)
         (boolean_realize_term v (lift_term s' m) DVec.nil) ≤
    S.eq (boolean_realize_term v (subst_term t s m) xs)
         (boolean_realize_term v (subst_term t s' m) xs) := by
  rw [← boolean_realize_term_subst, ← boolean_realize_term_subst]
  exact le_trans (subst_realize_congr2 v _ _ m) (boolean_realize_term_congr_iInf _ _ t xs)

/-! ## boolean_realize_formula -/

@[simp] def boolean_realize_formula : ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → β
  | _, v, preformula.falsum, _ => ⊥
  | _, v, preformula.equal t₁ t₂, _ =>
      S.eq (boolean_realize_term v t₁ DVec.nil) (boolean_realize_term v t₂ DVec.nil)
  | _, v, preformula.rel R, xs => S.rel_map R xs
  | _, v, preformula.apprel f t, xs =>
      boolean_realize_formula v f (DVec.cons (boolean_realize_term v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs =>
      imp (boolean_realize_formula v f₁ xs) (boolean_realize_formula v f₂ xs)
  | _, v, preformula.all f, xs =>
      ⨅ x : S, boolean_realize_formula (subst_realize v x 0) f xs

lemma boolean_realize_formula_congr' : ∀ {l} {v v' : ℕ → S} (h : ∀ n, v n = v' n)
    (f : @preformula L l) (xs : DVec S l),
    boolean_realize_formula v f xs = boolean_realize_formula v' f xs
  | _, _, _, h, preformula.falsum, _ => rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
      simp only [boolean_realize_formula, boolean_realize_term_congr' h]
  | _, _, _, h, preformula.rel R, _ => rfl
  | _, v, v', h, preformula.apprel f t, xs => by
      simp only [boolean_realize_formula, boolean_realize_term_congr' h]
      exact boolean_realize_formula_congr' h f _
  | _, v, v', h, preformula.imp f₁ f₂, xs => by
      simp only [boolean_realize_formula]
      congr 1
      · exact boolean_realize_formula_congr' h f₁ xs
      · exact boolean_realize_formula_congr' h f₂ xs
  | _, v, v', h, preformula.all f, xs => by
      simp only [boolean_realize_formula]
      congr 1; funext x
      exact boolean_realize_formula_congr' (fun k => subst_realize_congr h x 0 k) f xs

lemma boolean_realize_formula_subst : ∀ {l} (v : ℕ → S) (m : ℕ) (f : @preformula L l)
    (s : term L) (xs : DVec S l),
    boolean_realize_formula
      (subst_realize v (boolean_realize_term v (lift_term s m) DVec.nil) m) f xs =
    boolean_realize_formula v (subst_formula f s m) xs := by
  -- TODO: port from src/bfol.lean:160-172 (boolean_realize_formula_subst)
  sorry

lemma boolean_realize_formula_subst0 {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    boolean_realize_formula (subst_realize v (boolean_realize_term v s DVec.nil) 0) f xs =
    boolean_realize_formula v (subst_formula f s 0) xs := by
  -- TODO: port from src/bfol.lean:174-176 (boolean_realize_formula_subst0)
  sorry

lemma boolean_realize_formula_subst_lift : ∀ {l} (v : ℕ → S) (x : S) (m : ℕ)
    (f : @preformula L l) (xs : DVec S l),
    boolean_realize_formula (subst_realize v x 0) (lift_formula_at f 1 m) xs =
    boolean_realize_formula v f xs := by
  -- TODO: port from src/bfol.lean:178-191 (boolean_realize_formula_subst_lift)
  sorry

lemma boolean_realize_formula_congr_gen : ∀ (v v' : ℕ → S) {l} (f : @preformula L l)
    (xs xs' : DVec S l),
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ (DVec.map2 S.eq xs xs').fInf ⊓
    boolean_realize_formula v f xs ≤ boolean_realize_formula v' f xs' := by
  -- TODO: port from src/bfol.lean:193-235 (boolean_realize_formula_congr_gen)
  sorry

lemma boolean_realize_formula_congr (v v' : ℕ → S) {l} (f : @preformula L l) (xs : DVec S l) :
    (⨅ k : ℕ, S.eq (v k) (v' k)) ⊓ boolean_realize_formula v f xs ≤
    boolean_realize_formula v' f xs := by
  have key := boolean_realize_formula_congr_gen v v' f xs xs
  have hd : (DVec.map2 S.eq xs xs).fInf = ⊤ := eq_drefl xs
  rw [hd, inf_top_eq] at key
  exact le_trans (le_inf le_rfl le_top) (by rw [inf_top_eq]; exact key)

lemma boolean_realize_formula_subst_congr (v : ℕ → S) (s s' : term L) :
    ∀ {m l} (f : @preformula L l) (xs : DVec S l),
    S.eq (boolean_realize_term v (lift_term s m) DVec.nil)
         (boolean_realize_term v (lift_term s' m) DVec.nil) ⊓
    boolean_realize_formula v (subst_formula f s m) xs ≤
    boolean_realize_formula v (subst_formula f s' m) xs := by
  -- TODO: port from src/bfol.lean:245-256 (boolean_realize_formula_subst_congr)
  sorry

lemma boolean_realize_formula_subst_congr0 (v : ℕ → S) (s s' : term L) {l} (f : @preformula L l)
    (xs : DVec S l) :
    S.eq (boolean_realize_term v s DVec.nil) (boolean_realize_term v s' DVec.nil) ⊓
    boolean_realize_formula v (subst_formula f s 0) xs ≤
    boolean_realize_formula v (subst_formula f s' 0) xs := by
  -- TODO: port from src/bfol.lean:258-264 (boolean_realize_formula_subst_congr0)
  sorry

@[simp] lemma boolean_realize_formula_not (v : ℕ → S) (f : formula L) :
    boolean_realize_formula v (not' f) DVec.nil = (boolean_realize_formula v f DVec.nil)ᶜ := by
  simp [not', boolean_realize_formula, imp]

/-! ## Satisfiability — boolean_realize_formula_glb, bstatisfied -/

def boolean_realize_formula_glb (S : bStructure L β) (f : formula L) : β :=
  ⨅ v : ℕ → S, boolean_realize_formula v f DVec.nil

notation "⟦" f "⟧[" S "]ᵤ" => Fol.boolean_realize_formula_glb S f

variable (β) in
def bstatisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : bStructure L β) (v : ℕ → S),
    (⨅ f' ∈ T, boolean_realize_formula v (f' : formula L) DVec.nil) ≤
    boolean_realize_formula v f DVec.nil

notation:51 T " ⊨ᵤ[" β "] " f => Fol.bstatisfied β T f

def bstatisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ᵤ[β] f :=
  fun S v => le_trans (iInf_le _ f) (iInf_le _ hf)

def bstatisfied_weakening {T T' : Set (formula L)} (H : T ⊆ T') {f : formula L}
    (HT : T ⊨ᵤ[β] f) : T' ⊨ᵤ[β] f := by
  intro S v
  refine le_trans ?_ (HT S v)
  apply iInf_mono
  intro f'
  apply le_iInf
  intro hf'
  exact iInf_le _ (H hf')

/-! ## boolean_formula_soundness -/

/-- Soundness for boolean-valued semantics: if Γ ⊢ A, then Γ ⊨ᵤ[β] A. -/
lemma boolean_formula_soundness {Γ : Set (formula L)} {A : formula L}
    (H : Γ ⊢ A) : Γ ⊨ᵤ[β] A := by
  induction H with
  | axm h => exact bstatisfied_of_mem h
  | impI _ ih =>
    intro S v
    simp only [boolean_realize_formula]
    rw [deduction_simp]
    refine le_trans ?_ (ih S v)
    rw [inf_comm, iInf_insert]
  | impE A _ _ ih₁ ih₂ =>
    intro S v
    have h1 := ih₁ S v
    have h2 := ih₂ S v
    simp only [boolean_realize_formula] at h1
    exact le_trans (le_inf h1 h2) (imp_inf_le _ _)
  | falsumE _ ih =>
    intro S v
    apply le_of_sub_eq_bot
    apply bot_unique
    refine le_trans ?_ (ih S v)
    rw [iInf_insert, boolean_realize_formula_not]
  | allI _ ih =>
    intro S v
    simp only [boolean_realize_formula]
    rw [le_iInf_iff]
    intro x
    refine le_trans ?_ (ih S _)
    apply le_iInf
    intro f
    apply le_iInf
    rintro ⟨f', hf', rfl⟩
    rw [boolean_realize_formula_subst_lift]
    exact le_trans (iInf_le _ f') (iInf_le _ hf')
  | allE₂ A t _ ih =>
    intro S v
    rw [← boolean_realize_formula_subst0]
    exact le_trans (ih S v) (iInf_le _ _)
  | ref Γ t =>
    intro S v
    simp [boolean_realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro S v
    refine le_trans ?_ (boolean_realize_formula_subst_congr0 v s t f DVec.nil)
    exact le_inf (ih₁ S v) (ih₂ S v)

/-! ## boolean_realize_bounded_term -/

@[simp] def boolean_realize_bounded_term {n} (v : DVec S n) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l), S.carrier
  | _, bd_var k, _ => v.nth k.1 k.2
  | _, bd_func f, xs => S.fun_map f xs
  | _, bd_app t₁ t₂, xs =>
      boolean_realize_bounded_term v t₁
        (DVec.cons (boolean_realize_bounded_term v t₂ DVec.nil) xs)

@[reducible] def boolean_realize_closed_term (S : bStructure L β) (t : closed_term L) : S :=
  boolean_realize_bounded_term DVec.nil t DVec.nil

lemma boolean_realize_bounded_term_eq {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₂ k = v₁.nth k hk) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    boolean_realize_term v₂ t.fst xs = boolean_realize_bounded_term v₁ t xs
  | _, bd_var k, _ => hv k.1 k.2
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [boolean_realize_term, boolean_realize_bounded_term, bounded_preterm.fst]
      rw [boolean_realize_bounded_term_eq hv t₂ DVec.nil,
          boolean_realize_bounded_term_eq hv t₁]

lemma boolean_realize_bounded_term_irrel' {n n'} {v₁ : DVec S n} {v₂ : DVec S n'}
    (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn')
    {l} (t : bounded_preterm L n l) (t' : bounded_preterm L n' l)
    (ht : t.fst = t'.fst) (xs : DVec S l) :
    boolean_realize_bounded_term v₁ t xs = boolean_realize_bounded_term v₂ t' xs := by
  induction t generalizing n' with
  | bd_var k =>
    cases t' with
    | bd_var k' =>
      simp only [bounded_preterm.fst, preterm.var.injEq] at ht
      simp only [boolean_realize_bounded_term]
      have hk : k.1 = k'.1 := ht
      calc v₁.nth k.1 k.2 = v₂.nth k.1 (hk ▸ k'.2) := h k.1 k.2 (hk ▸ k'.2)
        _ = v₂.nth k'.1 k'.2 := by congr 1
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_func f =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func f' =>
      simp only [bounded_preterm.fst, preterm.func.injEq] at ht
      simp [boolean_realize_bounded_term, ht]
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_app t₁ t₂ iht ihs =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app t₁' t₂' =>
      simp only [bounded_preterm.fst, preterm.app.injEq] at ht
      simp only [boolean_realize_bounded_term]
      rw [ihs h t₂' ht.2 DVec.nil, iht h t₁' ht.1]

lemma boolean_realize_bounded_term_irrel {n} {v₁ : DVec S n}
    (t : bounded_term L n) (t' : closed_term L) (ht : t.fst = t'.fst) (xs : DVec S 0) :
    boolean_realize_bounded_term v₁ t xs = boolean_realize_closed_term S t' := by
  cases xs
  exact boolean_realize_bounded_term_irrel'
    (fun m _ hm' => absurd hm' (Nat.not_lt_zero m)) t t' ht DVec.nil

@[simp] lemma boolean_realize_bounded_term_cast_eq_irrel {n m l} {h : n = m}
    {v : DVec S m} {t : bounded_preterm L n l} (xs : DVec S l) :
    boolean_realize_bounded_term v (t.cast_eq h) xs =
    boolean_realize_bounded_term (v.cast h.symm) t xs := by
  subst h
  simp only [bounded_preterm.cast_eq, bounded_preterm.cast_rfl, DVec.cast]

@[simp] lemma boolean_realize_bounded_term_dvector_cast_irrel {n m l} {h : n = m}
    {v : DVec S n} {t : bounded_preterm L n l} {xs : DVec S l} :
    boolean_realize_bounded_term (v.cast h) (t.cast (Nat.le_of_eq h)) xs =
    boolean_realize_bounded_term v t xs := by
  subst h
  simp only [DVec.cast, bounded_preterm.cast_rfl]

@[simp] lemma boolean_realize_bounded_term_bd_app {n l}
    (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) (xs : DVec S n)
    (xs' : DVec S l) :
    boolean_realize_bounded_term xs (bd_app t s) xs' =
    boolean_realize_bounded_term xs t
      (DVec.cons (boolean_realize_bounded_term xs s DVec.nil) xs') := rfl

@[simp] lemma boolean_realize_closed_term_bd_apps {l} (t : closed_preterm L l)
    (ts : DVec (closed_term L) l) :
    boolean_realize_closed_term S (bd_apps t ts) =
    boolean_realize_bounded_term (DVec.nil : DVec S 0) t
      (ts.map (fun t' => boolean_realize_bounded_term (DVec.nil : DVec S 0) t' DVec.nil)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => exact ih (bd_app t x)

lemma boolean_realize_bounded_term_bd_apps {n l} (xs : DVec S n)
    (t : bounded_preterm L n l) (ts : DVec (bounded_term L n) l) :
    boolean_realize_bounded_term xs (bd_apps t ts) DVec.nil =
    boolean_realize_bounded_term xs t
      (ts.map (fun t => boolean_realize_bounded_term xs t DVec.nil)) := by
  induction ts with
  | nil => rfl
  | cons x xs' ih => exact ih (bd_app t x)

@[simp] lemma boolean_realize_cast_bounded_term {n m} {h : n ≤ m} {t : bounded_term L n}
    {v : DVec S m} :
    boolean_realize_bounded_term v (t.cast h) DVec.nil =
    boolean_realize_bounded_term (v.trunc n h) t DVec.nil := by
  -- TODO: port from src/bfol.lean:405-412 (boolean_realize_cast_bounded_term)
  sorry

/-- When realizing a closed term, the realizing dvector is irrelevant. -/
@[simp] lemma boolean_realize_closed_term_v_irrel {n} {v : DVec S n} {t : bounded_term L 0} :
    boolean_realize_bounded_term v (t.cast (Nat.zero_le n)) DVec.nil =
    boolean_realize_closed_term S t := by
  simp [boolean_realize_cast_bounded_term]

lemma boolean_realize_bounded_term_subst_lift' {n} (v : DVec S n) (x : S) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
    boolean_realize_bounded_term (DVec.cons x v) (t ↑ᵇ 1) xs =
    boolean_realize_bounded_term v t xs
  | _, bd_var k, _ => by
      simp only [boolean_realize_bounded_term, lift_bounded_term, lift_bounded_term_at,
                 Nat.zero_le, if_true]
      simp [DVec.nth]
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs => by
      simp only [boolean_realize_bounded_term, lift_bounded_term, lift_bounded_term_at]
      rw [boolean_realize_bounded_term_subst_lift' v x t₂ DVec.nil,
          boolean_realize_bounded_term_subst_lift' v x t₁]

@[simp] lemma boolean_realize_bounded_term_subst_lift {n} (v : DVec S n) (x : S)
    {l} (t : bounded_preterm L n l) (xs : DVec S l) :
    boolean_realize_bounded_term (DVec.cons x v) (t ↑ᵇ 1) xs =
    boolean_realize_bounded_term v t xs :=
  boolean_realize_bounded_term_subst_lift' v x t xs

/-! ## boolean_realize_bounded_formula -/

@[simp] def boolean_realize_bounded_formula :
    ∀ {n l} (v : DVec S n) (f : bounded_preformula L n l) (xs : DVec S l), β
  | _, _, v, bd_falsum, _ => ⊥
  | _, _, v, bd_equal t₁ t₂, _ =>
      S.eq (boolean_realize_bounded_term v t₁ DVec.nil)
           (boolean_realize_bounded_term v t₂ DVec.nil)
  | _, _, _, bd_rel R, xs => S.rel_map R xs
  | _, _, v, bd_apprel f t, xs =>
      boolean_realize_bounded_formula v f
        (DVec.cons (boolean_realize_bounded_term v t DVec.nil) xs)
  | _, _, v, bd_imp f₁ f₂, xs =>
      imp (boolean_realize_bounded_formula v f₁ xs)
          (boolean_realize_bounded_formula v f₂ xs)
  | _, _, v, bd_all f, xs =>
      ⨅ x : S, boolean_realize_bounded_formula (DVec.cons x v) f xs

end bfol

end Fol
