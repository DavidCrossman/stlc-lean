import Mathlib.Logic.Relation
import Stlc.Subst
import Stlc.Value

namespace Stlc

section
set_option hygiene false

local infixr:10 " ⟶ " => Step

open Term Syntax in
inductive Step : Term → Term → Prop
| app_cont {τ t₁ t₂ x} : Value t₂ → (t[(λ x : τ, t₁) t₂] ⟶ t[[x := t₂] t₁])
| app_cong_l {t₁ t₁' t₂} : (t₁ ⟶ t₁') → (t[t₁ t₂] ⟶ t[t₁' t₂])
| app_cong_r {t₁ t₂ t₂'} : Value t₁ → (t₂ ⟶ t₂') → (t[t₁ t₂] ⟶ t[t₁ t₂'])
| ite_cont_true {t₁ t₂} : t[if true then t₁ else t₂] ⟶ t₁
| ite_cont_false {t₁ t₂} : t[if false then t₁ else t₂] ⟶ t₂
| ite_cong {t₁ t₁' t₂ t₃} :
    (t₁ ⟶ t₁') → (t[if t₁ then t₂ else t₃] ⟶ t[if t₁' then t₂ else t₃])

end

infixr:10 " ⟶ " => Step

section
open Syntax

@[simp]
theorem Step.var_not {t : Term} {x : String} : ¬(t[xⱽ] ⟶ t) := by
  rintro ⟨⟩

@[simp]
theorem Step.abs_not {τ : Ty} {t₁ t₂ : Term} {x : String} : ¬(t[λ x : τ, t₁] ⟶ t₂) := by
  rintro ⟨⟩

@[simp]
theorem Step.true_not {t : Term} : ¬(t[true] ⟶ t) := by
  rintro ⟨⟩

@[simp]
theorem Step.false_not {t : Term} : ¬(t[false] ⟶ t) := by
  rintro ⟨⟩

@[simp]
theorem Step.ite_cont_true_iff {t₁ t₂ t₃ : Term} :
    (t[if true then t₁ else t₂] ⟶ t₃) ↔ (t₁ = t₃) := by
  constructor
  · intro h
    cases h with
    | ite_cont_true => rfl
    | ite_cong h => cases h
  · intro rfl
    exact ite_cont_true

@[simp]
theorem Step.ite_cont_false_iff {t₁ t₂ t₃ : Term} :
    (t[if false then t₁ else t₂] ⟶ t₃) ↔ (t₂ = t₃) := by
  constructor
  · intro h
    cases h with
    | ite_cont_false => rfl
    | ite_cong h => cases h
  · intro rfl
    exact ite_cont_false

@[simp]
theorem Step.ite_cong_iff {t₁ t₁' t₂ t₃} :
    (t[if t₁ then t₂ else t₃] ⟶ t[if t₁' then t₂ else t₃]) ↔ (t₁ ⟶ t₁') := by
  constructor
  · rintro ⟨⟩
    assumption
  · exact ite_cong

end

def Multistep := Relation.ReflTransGen Step

infixr:10 " ⟶* " => Multistep

@[refl]
theorem Multistep.refl {t : Term} : t ⟶* t :=
  Relation.ReflTransGen.refl

@[trans]
theorem Multistep.trans {t₁ t₂ t₃ : Term} : (t₁ ⟶* t₂) → (t₂ ⟶* t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.trans

theorem Multistep.head {t₁ t₂ t₃ : Term} : (t₁ ⟶ t₂) → (t₂ ⟶* t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.head

theorem Multistep.tail {t₁ t₂ t₃ : Term} : (t₁ ⟶* t₂) → (t₂ ⟶ t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.tail

theorem Multistep.single {t₁ t₂ : Term} : (t₁ ⟶ t₂) → (t₁ ⟶* t₂) :=
  Relation.ReflTransGen.single

@[elab_as_elim]
theorem Multistep.head_induction_on {b : Term} {motive : ∀ a, (a ⟶* b) → Prop} {a : Term}
    (h : a ⟶* b) (refl : motive b refl)
    (head : ∀ {a c} (h' : a ⟶ c) (h : c ⟶* b), motive c h → motive a (h.head h')) : motive a h :=
  Relation.ReflTransGen.head_induction_on h refl head

theorem Term.Value.no_step {t t' : Term} : Value t → ¬(t ⟶ t') := by
  rintro ⟨⟩ <;> rintro ⟨⟩

theorem Step.not_value {t t' : Term} : (t ⟶ t') → ¬t.Value := by
  rintro ⟨⟩ <;> rintro ⟨⟩

open Syntax in
@[simp]
def Term.step : Term → Option Term
| t[(λ x : τ, t₁) t₂] =>
    if Value t₂ then subst x t₂ t₁ else t₂.step.map <| app (abs x τ t₁)
| t[t₁ t₂] => if Value t₁ then t₂.step.map (app t₁) else t₁.step.map (app · t₂)
| t[if true then t else _] | t[if false then _ else t] => t
| t[if t₁ then t₂ else t₃] => t₁.step.map (ite · t₂ t₃)
| _ => none

theorem Term.step_iff_step (t t' : Term) : t.step = some t' ↔ (t ⟶ t') := by
  induction t generalizing t' with
  | var | abs | «true» | «false» =>
    simp only [step, reduceCtorEq, false_iff]
    rintro ⟨⟩
  | app t₁ t₂ ht₁ ht₂ =>
    constructor <;> intro h
    · cases t₁ with simp [step, value_iff] at h
      | abs => cases t₂ with simp [step, value_iff] at h
        | abs | «true» | «false» => simp [←h, Step.app_cont]
        | app | ite =>
          rcases h with ⟨t₃, h1, h₂⟩
          simp [←h₂, Step.app_cong_r _ ((ht₂ t₃).mp h1)]
      | app | ite =>
        rcases h with ⟨t₃, h₁, h₂⟩
        simp only [←h₂, Step.app_cong_l ((ht₁ t₃).mp h₁)]
      | «true» | «false» =>
        rcases h with ⟨t₃, h₁, h₂⟩
        simp [←h₂, Step.app_cong_r _ ((ht₂ t₃).mp h₁)]
    · cases h with
      | app_cont hb => simp [step, hb]
      | app_cong_l h => cases t₁ with
        | var | abs | «true» | «false» => cases h
        | app | ite => simp [step, value_iff, ht₁, h]
      | @app_cong_r _ _ t₃ v h => cases t₁ with
        | var | app | ite => cases v
        | abs =>
          have h' := h.not_value
          simp [step, h', (ht₂ t₃).mpr h]
        | «true» | «false» => simp [step, (ht₂ t₃).mpr h]
  | ite t₁ _ _ ht₁ =>
    constructor <;> intro h
    · cases t₁ with simp [step] at h
      | app | ite =>
        rcases h with ⟨t₂, h₁, h₂⟩
        rw [←h₂]
        exact Step.ite_cong ((ht₁ t₂).mp h₁)
      | «true» => simp only [h, Step.ite_cont_true]
      | «false» => simp only [h, Step.ite_cont_false]
    · cases h with
      | ite_cont_true | ite_cont_false => rw [step]
      | @ite_cong _ t₂ _ _ h => cases t₁ with
        | var | abs | «true» | «false» => cases h
        | app | ite => simp only [step, (ht₁ t₂).mpr h, Option.map_some]

instance : DecidableRel Step := fun t₁ t₂ =>
  decidable_of_decidable_of_iff <| Term.step_iff_step t₁ t₂

theorem Term.not_step_iff_not_step (t : Term) : t.step = none ↔ ∀ t', ¬(t ⟶ t') := by
  simp_rw [←step_iff_step]
  constructor <;> intro h
  · simp [h]
  · ext
    simp [h]

def Term.step_n : Term → Nat → Term
| x, 0 => x
| t, n + 1 =>
  let t' := t.step_n n
  match t'.step with
  | some t'' => t''
  | none => t'

theorem Term.step_n_spec (t : Term) (n : Nat) : t ⟶* t.step_n n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [step_n]
    by_cases h : ∃ t', t.step_n n ⟶ t'
    · rcases h with ⟨_, h'⟩
      simp only [(step_iff_step ..).mpr h']
      rcases (ih t).cases_head with ht | _
      · rw [ht]
        exact Multistep.single h'
      · exact Multistep.tail (ih t) h'
    · push_neg at h
      rw [←not_step_iff_not_step] at h
      rw [h]
      exact ih t

theorem Term.reduce_n {t t' : Term} (n : Nat) (h : t.step_n n = t' := by rfl) : t ⟶* t' := by
  rw [←h]
  exact t.step_n_spec n

theorem Step.unique {t t₁ t₂} : (t ⟶ t₁) → (t ⟶ t₂) → t₁ = t₂ := by
  intro h₁ h₂
  induction h₁ generalizing t₂ with
  | app_cont v => cases h₂ with
    | app_cont => rfl
    | app_cong_l h₃ => cases h₃
    | app_cong_r _ h₃ => cases v.no_step h₃
  | app_cong_l h₃ ih => cases h₂ with
    | app_cont => cases h₃
    | app_cong_l h₄ => rw [ih h₄]
    | app_cong_r v => cases v.no_step h₃
  | app_cong_r v h₃ ih => cases h₂ with
    | app_cont v₂ => cases v₂.no_step h₃
    | app_cong_l h₄ => cases v.no_step h₄
    | app_cong_r _ h₄ => rw [ih h₄]
  | ite_cont_true => cases h₂ with
    | ite_cont_true => rfl
    | ite_cong h₃ => cases Term.Value.true.no_step h₃
  | ite_cont_false => cases h₂ with
    | ite_cont_false => rfl
    | ite_cong h₃ => cases Term.Value.false.no_step h₃
  | ite_cong h₃ ih => cases h₂ with
    | ite_cont_true | ite_cont_false => cases h₃
    | ite_cong h₄ => rw [ih h₄]

theorem Multistep.cont_iff {t t₁ t₂ : Term} (ht : t.Value) (h : t₁ ⟶ t₂) :
    (t₁ ⟶* t) ↔ (t₂ ⟶* t) := by
  constructor
  · intro h₂
    obtain rfl | ⟨_, h₃, _⟩ := h₂.cases_head
    · cases ht.no_step h
    · rwa [h.unique h₃]
  · exact head h

end Stlc
