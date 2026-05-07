/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
-/
/- Lean 4 port of src/henkin.lean — Part 1 (lines 1-450).
   Task 16a; Task 16b will continue from line 451. -/

import Flypitch4.Completion
import Flypitch4.LanguageExtension
import Flypitch4.Colimit

namespace Fol

open colimit omega_colimit

universe u

/-!
## Directed colimits of languages

These are fieldwise (and then indexwise) colimits of types.
For the Henkin construction, the directed type is always ℕ' (carrier = ℕ : Type 0),
so we can use a single universe u for the language symbols.
-/

/-- A directed diagram of Languages at universe u indexed by ℕ -/
structure directed_diagram_language : Type (u + 1) where
  obj : ℕ → Language.{u}
  mor : ∀ {x y : ℕ}, x ≤ y → (obj x →ᴸ obj y)
  h_mor : ∀ {x y z : ℕ} {f1 : x ≤ y} {f2 : y ≤ z} {f3 : x ≤ z},
    mor f3 = (mor f2).comp (mor f1)

/-- Restrict to n-ary function family -/
def diagram_functions (F : directed_diagram_language.{u}) (n : ℕ) : directed_diagram ℕ' where
  obj x := (F.obj x).functions n
  mor h := (F.mor h).on_function
  h_mor := by
    intro x y z f1 f2 f3
    have key := F.h_mor (f1 := f1) (f2 := f2) (f3 := f3)
    funext a
    exact congr_fun (show (F.mor f3).on_function = (F.mor f2).on_function ∘ (F.mor f1).on_function
      from by rw [key]) a

/-- Restrict to n-ary relation family -/
def diagram_relations (F : directed_diagram_language.{u}) (n : ℕ) : directed_diagram ℕ' where
  obj x := (F.obj x).relations n
  mor h := (F.mor h).on_relation
  h_mor := by
    intro x y z f1 f2 f3
    have key := F.h_mor (f1 := f1) (f2 := f2) (f3 := f3)
    funext a
    exact congr_fun (show (F.mor f3).on_relation = (F.mor f2).on_relation ∘ (F.mor f1).on_relation
      from by rw [key]) a

/-- The colimit language -/
def colimit_language (F : directed_diagram_language.{u}) : Language.{u} :=
  ⟨fun n => colimit (diagram_functions F n),
   fun n => colimit (diagram_relations F n)⟩

/-- Canonical map from stage i into the colimit language -/
def canonical_map_language {F : directed_diagram_language.{u}} (i : ℕ) :
    F.obj i →ᴸ colimit_language F :=
  ⟨fun {n} => @canonical_map _ (diagram_functions F n) i,
   fun {n} => @canonical_map _ (diagram_relations F n) i⟩

/-- A cocone over a directed diagram of languages -/
structure cocone_language (F : directed_diagram_language.{u}) where
  vertex : Language.{u}
  map : ∀ i : ℕ, F.obj i →ᴸ vertex
  h_compat : ∀ {i j : ℕ}, ∀ h : i ≤ j, map i = (map j).comp (F.mor h)

/-- The colimit is itself a cocone -/
def cocone_of_colimit_language (F : directed_diagram_language.{u}) :
    cocone_language F where
  vertex := colimit_language F
  map := canonical_map_language
  h_compat := by
    intro i j H
    apply Lhom.Lhom_funext
    · funext n; funext f
      simp only [canonical_map_language, Lhom.comp, Function.comp]
      exact congr_fun ((cocone_of_colimit (diagram_functions F n)).h_compat H) f
    · funext n; funext R
      simp only [canonical_map_language, Lhom.comp, Function.comp]
      exact congr_fun ((cocone_of_colimit (diagram_relations F n)).h_compat H) R

/-!
## The Henkin construction
-/

/-- Inductive type of function symbols for one Henkin step.
    `inc` embeds L-symbols; `wit` introduces witness constants. -/
inductive henkin_language_functions (L : Language.{u}) : ℕ → Type u
  | inc : ∀ {n}, L.functions n → henkin_language_functions L n
  | wit : bounded_formula L 1 → henkin_language_functions L 0

open henkin_language_functions

/-- One Henkin step on languages -/
@[reducible] def henkin_language_step (L : Language.{u}) : Language.{u} :=
  ⟨henkin_language_functions L, L.relations⟩

def wit' {L : Language.{u}} : bounded_formula L 1 → (henkin_language_step L).constants :=
  wit

def henkin_language_inclusion {L : Language.{u}} : L →ᴸ henkin_language_step L :=
  ⟨fun {_} f => inc f, fun {_} => id⟩

lemma henkin_language_inclusion_inj {L : Language.{u}} :
    Lhom.is_injective (@henkin_language_inclusion L) :=
  ⟨fun {_} _ _ H => henkin_language_functions.inc.inj H, fun {_} _ _ H => H⟩

/-! ## wit_property and henkin_theory_step -/

/-- The witnessing sentence: (∃ᵇf) → f[c/0] -/
@[reducible] def wit_property {L : Language.{u}} (f : bounded_formula L 1) (c : L.constants) :
    sentence L :=
  bd_imp (bd_ex f) (subst0_bounded_formula f (bd_const c))

/-- One Henkin step on theories -/
def henkin_theory_step {L : Language.{u}} (T : SentTheory L) :
    SentTheory (henkin_language_step L) :=
  henkin_language_inclusion.Theory_induced T ∪
  (fun f : bounded_formula L 1 =>
    wit_property (henkin_language_inclusion.on_bounded_formula f) (wit' f)) '' Set.univ

/-- The Henkin extension of a consistent theory is consistent -/
lemma is_consistent_henkin_theory_step {L : Language.{u}} {T : SentTheory L}
    (hT : T.is_consistent) : (henkin_theory_step T).is_consistent :=
  sorry -- TODO: requires is_consistent_extend (currently sorry in LanguageExtension)

/-! ## Henkin language chain -/

/-- Objects of the Henkin language chain -/
@[reducible] def henkin_language_chain_objects {L : Language.{u}} : ℕ → Language.{u}
  | 0 => L
  | (n + 1) => henkin_language_step (@henkin_language_chain_objects L n)

lemma obvious {L : Language.{u}} (i : ℕ) :
    henkin_language_functions (@henkin_language_chain_objects L i) 0 =
    (@henkin_language_chain_objects L (i + 1)).constants := by
  simp only [Language.constants, henkin_language_chain_objects, henkin_language_step]

/-- Transition maps of the Henkin language chain -/
def henkin_language_chain_maps (L : Language.{u}) :
    ∀ (x y : ℕ), x ≤ y →
      Lhom (@henkin_language_chain_objects L x) (@henkin_language_chain_objects L y)
  | _, 0, H => Nat.eq_zero_of_le_zero H ▸ Lhom.id _
  | x, y + 1, H =>
      if hx : x = y + 1 then hx ▸ Lhom.id _
      else henkin_language_inclusion.comp
             (henkin_language_chain_maps L x y
               (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H hx)))

-- Private helper: the zero-zero case gives identity
private lemma hcm_zero_zero (L : Language.{u}) (H : 0 ≤ 0) :
    henkin_language_chain_maps L 0 0 H = Lhom.id L := rfl

-- Private helper: the self case gives identity
private lemma hcm_self (L : Language.{u}) (k : ℕ) (H : k ≤ k) :
    henkin_language_chain_maps L k k H = Lhom.id (@henkin_language_chain_objects L k) := by
  cases k with
  | zero => exact hcm_zero_zero L H
  | succ n =>
      simp only [henkin_language_chain_maps, dif_pos rfl]
      rfl

-- Private helper: the non-equal successor case gives a composition
private lemma hcm_succ_ne (L : Language.{u}) (x y : ℕ) (H : x ≤ y + 1) (hne : x ≠ y + 1) :
    henkin_language_chain_maps L x (y + 1) H =
    henkin_language_inclusion.comp
      (henkin_language_chain_maps L x y (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H hne))) := by
  simp only [henkin_language_chain_maps, dif_neg hne]

lemma henkin_language_chain_maps_inj (L : Language.{u}) (i j : ℕ) (h : i ≤ j) :
    Lhom.is_injective (henkin_language_chain_maps L i j h) := by
  induction j with
  | zero =>
    have h0 : i = 0 := Nat.eq_zero_of_le_zero h; subst h0
    rw [hcm_zero_zero]; exact ⟨fun {_} _ _ H => H, fun {_} _ _ H => H⟩
  | succ n ih =>
    by_cases hx : i = n + 1
    · subst hx
      rw [hcm_self]; exact ⟨fun {_} _ _ H => H, fun {_} _ _ H => H⟩
    · have hle : i ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hx)
      rw [hcm_succ_ne L i n h hx]
      have ih' := ih hle
      exact ⟨fun {m} x y H => ih'.on_function (henkin_language_inclusion_inj.on_function H),
             fun {m} x y H => ih'.on_relation (henkin_language_inclusion_inj.on_relation H)⟩

/-- Functoriality of the Henkin language chain maps -/
lemma henkin_language_chain_maps_functorial (L : Language.{u}) :
    ∀ (x y z : ℕ) (f1 : x ≤ y) (f2 : y ≤ z) (f3 : x ≤ z),
      henkin_language_chain_maps L x z f3 =
      (henkin_language_chain_maps L y z f2).comp (henkin_language_chain_maps L x y f1) := by
  intro x y z f1 f2 f3
  induction z with
  | zero =>
    have hy0 : y = 0 := Nat.eq_zero_of_le_zero f2
    have hx0 : x = 0 := Nat.le_antisymm (hy0 ▸ f1) (Nat.zero_le _)
    subst hx0; subst hy0
    simp [hcm_zero_zero, Lhom.id_is_left_identity]
  | succ n ih =>
    by_cases hy : y = n + 1
    · subst hy
      by_cases hx : x = n + 1
      · subst hx; simp [hcm_self, Lhom.id_is_left_identity]
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f3 hx)
        rw [hcm_succ_ne L x n f3 hx, hcm_self, Lhom.id_is_left_identity]
    · have hyn : y ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f2 hy)
      by_cases hx : x = n + 1
      · exfalso; exact absurd (Nat.le_trans f1 hyn) (hx ▸ Nat.not_succ_le_self n)
      · have hxn : x ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne f3 hx)
        rw [hcm_succ_ne L x n f3 hx, hcm_succ_ne L y n f2 hy,
            ih hyn hxn]
        apply Lhom.Lhom_funext <;> (funext n; simp [Lhom.comp, Function.comp_assoc])

/-- The Henkin language chain as a directed diagram of languages -/
def henkin_language_chain {L : Language.{u}} : directed_diagram_language.{u} where
  obj := @henkin_language_chain_objects L
  mor := fun {x y} H => henkin_language_chain_maps L x y H
  h_mor := fun {x y z f1 f2 f3} =>
    henkin_language_chain_maps_functorial L x y z f1 f2 f3

lemma id_of_self_map (L : Language.{u}) (k : ℕ) :
    henkin_language_chain_maps L k k (Nat.le_refl k) =
    Lhom.id (@henkin_language_chain_objects L k) :=
  hcm_self L k (Nat.le_refl k)

lemma henkin_language_inclusion_chain_map {i : ℕ} {L : Language.{u}} :
    @henkin_language_inclusion (@henkin_language_chain_objects L i) =
    henkin_language_chain_maps L i (i + 1) (Nat.le_succ i) := by
  rw [hcm_succ_ne L i i (Nat.le_succ i) (Nat.ne_of_lt (Nat.lt_succ_self i))]
  rw [hcm_self L i (Nat.le_refl i)]
  rw [Lhom.id_is_right_identity]

/-! ## The limit language L_∞ -/

/-- The colimit of the Henkin language chain -/
def L_infty (L : Language.{u}) : Language.{u} :=
  colimit_language (@henkin_language_chain L)

/-- Canonical inclusion L_m → L_∞ -/
def henkin_language_canonical_map {L : Language.{u}} (m : ℕ) :
    (@henkin_language_chain L).obj m →ᴸ L_infty L :=
  canonical_map_language m

@[simp] lemma henkin_language_canonical_map_inj {L : Language.{u}} (m : ℕ) :
    Lhom.is_injective (@henkin_language_canonical_map L m) := by
  constructor
  · intro n
    simp only [henkin_language_canonical_map, canonical_map_language]
    apply canonical_map_inj_of_transition_maps_inj
    intro i j H
    exact (henkin_language_chain_maps_inj L i j H).on_function
  · intro n
    simp only [henkin_language_canonical_map, canonical_map_language]
    apply canonical_map_inj_of_transition_maps_inj
    intro i j H
    exact (henkin_language_chain_maps_inj L i j H).on_relation

/-! ## Directed diagrams of terms and formulas -/

/-- Chain of preterms at level l -/
def henkin_term_chain {L : Language.{u}} (l : ℕ) : directed_diagram ℕ' where
  obj k := preterm (@henkin_language_chain_objects L k) l
  mor H := Lhom.on_term (henkin_language_chain_maps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    simp only [Lhom.comp_on_term, hcomp]

/-- Chain of preformulas at level l -/
def henkin_formula_chain {L : Language.{u}} (l : ℕ) : directed_diagram ℕ' where
  obj k := @preformula (@henkin_language_chain_objects L k) l
  mor H := Lhom.on_formula (henkin_language_chain_maps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    funext f
    simp [Lhom.comp_on_formula, hcomp]

/-- Chain of bounded preterms at bound n, level l -/
def henkin_bounded_term_chain {L : Language.{u}} (n l : ℕ) : directed_diagram ℕ' where
  obj k := bounded_preterm (@henkin_language_chain_objects L k) n l
  mor H := Lhom.on_bounded_term (henkin_language_chain_maps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    rw [hcomp, Lhom.comp_on_bounded_term]

@[reducible] def henkin_bounded_term_chain' {L : Language.{u}} : directed_diagram ℕ' :=
  @henkin_bounded_term_chain L 1 0

/-- Chain of bounded preformulas at bound n, level l -/
def henkin_bounded_formula_chain {L : Language.{u}} (n l : ℕ) : directed_diagram ℕ' where
  obj k := bounded_preformula (@henkin_language_chain_objects L k) n l
  mor H := Lhom.on_bounded_formula (henkin_language_chain_maps L _ _ H)
  h_mor := by
    intro x y z f1 f2 f3
    have hcomp := henkin_language_chain_maps_functorial L x y z f1 f2 f3
    rw [hcomp, Lhom.comp_on_bounded_formula]

@[reducible] def henkin_bounded_formula_chain' {L : Language.{u}} : directed_diagram ℕ' :=
  @henkin_bounded_formula_chain L 1 0

/-! ## Cocones with vertex L_∞ -/

/-- L_∞ is a cocone over the diagram of languages -/
def cocone_of_L_infty {L : Language.{u}} : cocone_language (@henkin_language_chain L) :=
  cocone_of_colimit_language _

/-- Cocone over the preterm chain with vertex preterm (L_∞ L) l -/
def cocone_of_term_L_infty {L : Language.{u}} (l : ℕ) :
    cocone (@henkin_term_chain L l) where
  vertex := preterm (L_infty L) l
  map i := Lhom.on_term (henkin_language_canonical_map i)
  h_compat := by
    intro i j H
    have hc : henkin_language_canonical_map i =
        (henkin_language_canonical_map j).comp (henkin_language_chain_maps L i j H) :=
      (@cocone_of_L_infty L).h_compat H
    funext t
    simp only [Function.comp, henkin_term_chain]
    have := congr_arg (fun ϕ : @henkin_language_chain_objects L i →ᴸ L_infty L =>
        ϕ.on_term t) hc
    simpa [Lhom.comp] using this

/-- Cocone over the preformula chain with vertex @preformula (L_∞ L) l -/
def cocone_of_formula_L_infty {L : Language.{u}} (l : ℕ) :
    cocone (@henkin_formula_chain L l) where
  vertex := @preformula (L_infty L) l
  map i := Lhom.on_formula (henkin_language_canonical_map i)
  h_compat := by
    intro i j H
    have hc : henkin_language_canonical_map i =
        (henkin_language_canonical_map j).comp (henkin_language_chain_maps L i j H) :=
      (@cocone_of_L_infty L).h_compat H
    funext f
    simp only [Function.comp, henkin_formula_chain]
    have := congr_arg (fun ϕ : @henkin_language_chain_objects L i →ᴸ L_infty L =>
        ϕ.on_formula f) hc
    simpa [Lhom.comp] using this

/-- Cocone over the bounded term chain with vertex bounded_preterm (L_∞ L) n l -/
def cocone_of_bounded_term_L_infty {L : Language.{u}} (n l : ℕ) :
    cocone (@henkin_bounded_term_chain L n l) where
  vertex := bounded_preterm (L_infty L) n l
  map i := Lhom.on_bounded_term (henkin_language_canonical_map i)
  h_compat := by
    intro i j H
    have hc : henkin_language_canonical_map i =
        (henkin_language_canonical_map j).comp (henkin_language_chain_maps L i j H) :=
      (@cocone_of_L_infty L).h_compat H
    funext t
    simp only [Function.comp, henkin_bounded_term_chain]
    have := congr_arg (fun ϕ : @henkin_language_chain_objects L i →ᴸ L_infty L =>
        ϕ.on_bounded_term t) hc
    simpa [Lhom.comp] using this

end Fol
