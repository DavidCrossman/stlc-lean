import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace Stlc

inductive Ty : Type
| bool
| arrow : Ty → Ty → Ty
deriving DecidableEq

inductive Term : Type
| var : String → Term
| abs : String → Ty → Term → Term
| app : Term → Term → Term
| true
| false
| if : Term → Term → Term → Term
deriving DecidableEq

declare_syntax_cat stlc_ty
syntax ident : stlc_ty
syntax hole : stlc_ty
syntax "Bool" : stlc_ty
syntax:10 stlc_ty:11 " → " stlc_ty:10 : stlc_ty
syntax "(" stlc_ty ")" : stlc_ty
syntax "$(" term ")" : stlc_ty

declare_syntax_cat stlc_term
syntax:max ident : stlc_term
syntax:max hole : stlc_term
syntax:max str : stlc_term
syntax:lead "λ " str " : " stlc_ty ", " stlc_term : stlc_term
syntax:lead "λ " ident " : " stlc_ty ", " stlc_term : stlc_term
syntax:lead "λ " "$(" term ")" " : " stlc_ty ", " stlc_term : stlc_term
syntax:arg stlc_term:arg stlc_term:max : stlc_term
syntax:max "true" : stlc_term
syntax:max "false" : stlc_term
syntax:lead "if " stlc_term " then " stlc_term " else " stlc_term : stlc_term
syntax "(" stlc_term ")" : stlc_term
syntax "$(" term ")" : stlc_term

syntax "τ[ " stlc_ty " ]" : term
syntax "t[ " stlc_term " ]" : term

macro_rules
| `(τ[ $a:ident ]) => return a
| `(τ[ $a:hole ]) => return a
| `(τ[ Bool ]) => `(Ty.bool)
| `(τ[ $τ₁:stlc_ty → $τ₂:stlc_ty ]) => `(Ty.arrow τ[$τ₁] τ[$τ₂])
| `(τ[ ($τ:stlc_ty) ]) => `(τ[$τ])
| `(τ[ $($t:term) ]) => return t

macro_rules
| `(t[ $a:ident ]) => return a
| `(t[ $a:hole ]) => return a
| `(t[ $x:str ]) => `(Term.var $x)
| `(t[ λ $x:ident : $τ:stlc_ty, $t:stlc_term ]) => `(Term.abs $x τ[$τ] t[$t])
| `(t[ λ $x:str : $τ:stlc_ty, $t:stlc_term ]) => `(Term.abs $x τ[$τ] t[$t])
| `(t[ λ $($x:term) : $τ:stlc_ty, $t:stlc_term ]) => `(Term.abs $x τ[$τ] t[$t])
| `(t[ $t₁:stlc_term $t₂:stlc_term ]) => `(Term.app t[$t₁] t[$t₂])
| `(t[ true ]) => `(Term.true)
| `(t[ false ]) => `(Term.false)
| `(t[ if $t₁:stlc_term then $t₂:stlc_term else $t₃:stlc_term ]) =>
    `(Term.if t[$t₁] t[$t₂] t[$t₃])
| `(t[ ($t:stlc_term) ]) => `(t[$t])
| `(t[ $($t:term) ]) => return t

@[mk_iff]
inductive Value : Term → Prop
| abs {x τ t} : Value t[λ x : τ, t]
| true : Value t[true]
| false : Value t[false]

attribute [simp] Value.abs Value.true Value.false

instance : DecidablePred Value := fun t =>
  decidable_of_bool (t matches .true | .false | .abs ..) (by cases t <;> simp [value_iff])

@[simp]
def subst (x : String) (s t : Term) : Term := match t with
| .var y => if x = y then s else t
| t[λ y : τ, t'] => if x = y then t else t[λ y : τ, $(subst x s t')]
| t[t₁ t₂] => t[$(subst x s t₁) $(subst x s t₂)]
| t[true] | t[false] => t
| t[if t₁ then t₂ else t₃] => t[if $(subst x s t₁) then $(subst x s t₂) else $(subst x s t₃)]

syntax:lead "[" ident " := " stlc_term "]" stlc_term:max : stlc_term
syntax:lead "[" str " := " stlc_term "]" stlc_term:max : stlc_term
macro_rules
| `(t[ [$x:ident := $s:stlc_term] $t:stlc_term ]) => `(subst $x t[$s] t[$t])
| `(t[ [$x:str := $s:stlc_term] $t:stlc_term ]) => `(subst $x t[$s] t[$t])

section
set_option hygiene false

local infixr:10 " ⟶ " => Step

inductive Step : Term → Term → Prop
| app_cont {x τ t v} : Value v → (t[(λ x : τ, t) v] ⟶ t[[x := v] t])
| app_cong_l {t₁ t₁' t₂} : (t₁ ⟶ t₁') → (t[t₁ t₂] ⟶ t[t₁' t₂])
| app_cong_r {v t t'} : Value v → (t ⟶ t') → (t[v t] ⟶ t[v t'])
| if_cont_true {t₁ t₂} : t[if true then t₁ else t₂] ⟶ t₁
| if_cont_false {t₁ t₂} : t[if false then t₁ else t₂] ⟶ t₂
| if_cong {t₁ t₁' t₂ t₃} :
    (t₁ ⟶ t₁') → (t[if t₁ then t₂ else t₃] ⟶ t[if t₁' then t₂ else t₃])

end

infixr:10 " ⟶ " => Step

def Steps := Relation.ReflTransGen Step

infixr:10 " ⟶* " => Steps

@[refl]
theorem Steps.refl {t : Term} : t ⟶* t := Relation.ReflTransGen.refl

@[trans]
theorem Steps.trans {t₁ t₂ t₃ : Term} : (t₁ ⟶* t₂) → (t₂ ⟶* t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.trans

theorem Steps.head {t₁ t₂ t₃ : Term} : (t₁ ⟶ t₂) → (t₂ ⟶* t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.head

theorem Steps.tail {t₁ t₂ t₃ : Term} : (t₁ ⟶* t₂) → (t₂ ⟶ t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.tail

theorem Steps.single {t₁ t₂ : Term} : (t₁ ⟶ t₂) → (t₁ ⟶* t₂) := Relation.ReflTransGen.single

theorem Value.no_step {v t : Term} : Value v → ¬(v ⟶ t) := by
  rintro ⟨⟩ <;> rintro ⟨⟩

theorem Step.not_value {t t' : Term} : (t ⟶ t') → ¬Value t := by
  rintro ⟨⟩ <;> rintro ⟨⟩

def Term.step : Term → Option Term
| t[(λ x : τ, t₁) t₂] =>
    if Value t₂ then subst x t₂ t₁ else t₂.step.map <| .app (.abs x τ t₁)
| t[t₁ t₂] => if Value t₁ then t₂.step.map (.app t₁) else t₁.step.map (.app · t₂)
| t[if true then t else _] | t[if false then _ else t] => t
| t[if t₁ then t₂ else t₃] => t₁.step.map (.if · t₂ t₃)
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
        | app | «if» =>
          rcases h with ⟨t₃, h1, h₂⟩
          simp [←h₂, Step.app_cong_r _ ((ht₂ t₃).mp h1)]
      | app | «if» =>
        rcases h with ⟨t₃, h₁, h₂⟩
        simp only [←h₂, Step.app_cong_l ((ht₁ t₃).mp h₁)]
      | «true» | «false» =>
        rcases h with ⟨t₃, h₁, h₂⟩
        simp [←h₂, Step.app_cong_r _ ((ht₂ t₃).mp h₁)]
    · cases h with
      | app_cont hb => simp [step, hb]
      | app_cong_l h => cases t₁ with
        | var | abs | «true» | «false» => cases h
        | app | «if» => simp [step, value_iff, ht₁, h]
      | @app_cong_r _ _ t₃ v h => cases t₁ with
        | var | app | «if» => cases v
        | abs =>
          have h' := h.not_value
          simp [step, h', (ht₂ t₃).mpr h]
        | «true» | «false» => simp [step, (ht₂ t₃).mpr h]
  | «if» t₁ _ _ ht₁ =>
    constructor <;> intro h
    · cases t₁ with simp [step] at h
      | app | «if» =>
        rcases h with ⟨t₂, h₁, h₂⟩
        rw [←h₂]
        exact Step.if_cong ((ht₁ t₂).mp h₁)
      | «true» => simp only [h, Step.if_cont_true]
      | «false» => simp only [h, Step.if_cont_false]
    · cases h with
      | if_cont_true | if_cont_false => rw [step]
      | @if_cong _ t₂ _ _ h => cases t₁ with
        | var | abs | «true» | «false» => cases h
        | app | «if» => simp only [step, (ht₁ t₂).mpr h, Option.map_some]

instance : DecidableRel Step := fun t₁ t₂ =>
  decidable_of_decidable_of_iff <| Term.step_iff_step t₁ t₂

theorem Term.not_step_iff_not_step (t : Term) : t.step = none ↔ ∀ t', ¬(t ⟶ t') := by
  simp [←Term.step_iff_step]
  constructor <;> intro h
  · simp only [h, reduceCtorEq, not_false_eq_true, implies_true]
  · ext
    simp only [h, reduceCtorEq]

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
      simp only [(Term.step_iff_step ..).mpr h']
      rcases (ih t).cases_head with ht | _
      · rw [ht]
        exact Steps.single h'
      · exact Steps.tail (ih t) h'
    · push_neg at h
      rw [←Term.not_step_iff_not_step] at h
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
    | app_cont => cases (Value.abs ..).no_step h₃
    | app_cong_l h₄ => rw [ih h₄]
    | app_cong_r v => cases v.no_step h₃
  | app_cong_r v h₃ ih => cases h₂ with
    | app_cont v₂ => cases v₂.no_step h₃
    | app_cong_l h₄ => cases v.no_step h₄
    | app_cong_r _ h₄ => rw [ih h₄]
  | if_cont_true => cases h₂ with
    | if_cont_true => rfl
    | if_cong h₃ => cases Value.true.no_step h₃
  | if_cont_false => cases h₂ with
    | if_cont_false => rfl
    | if_cong h₃ => cases Value.false.no_step h₃
  | if_cong h₃ ih => cases h₂ with
    | if_cont_true => cases Value.true.no_step h₃
    | if_cont_false => cases Value.false.no_step h₃
    | if_cong h₄ => rw [ih h₄]

theorem Steps.cont_iff {t₁ t₂ v : Term} (hv : Value v) (h : t₁ ⟶ t₂) :
    (t₁ ⟶* v) ↔ (t₂ ⟶* v) := by
  constructor
  · intro h₂
    obtain rfl | ⟨_, h₃, _⟩ := h₂.cases_head
    · cases hv.no_step h
    · rwa [h.unique h₃]
  · exact Steps.head h

def Context : Type := String → Option Ty

instance : EmptyCollection Context :=
  ⟨fun _ => none⟩

def Context.update (Γ : Context) (x : String) (τ : Ty) : Context :=
  Function.update Γ x (some τ)

notation:arg x " ↦ " τ "; " Γ:arg => Context.update Γ x τ

def Context.IncludedIn (Γ Γ' : Context) : Prop :=
  ∀ {x τ}, Γ x = some τ → Γ' x = some τ

instance : HasSubset Context :=
  ⟨Context.IncludedIn⟩

theorem Context.includedIn_empty (Γ : Context) : ∅ ⊆ Γ := by
  rintro _ _ ⟨⟩

theorem Context.includedIn_update {Γ Γ' : Context} {x : String} {τ : Ty} :
    Γ ⊆ Γ' → x ↦ τ; Γ ⊆ x ↦ τ; Γ' := by
  simp only [Subset, IncludedIn, update, Function.update_apply]
  intro h₁ y τ' h₂
  rw [←h₂]
  split_ifs with hyx
  · rfl
  · simp only [hyx, ↓reduceIte] at h₂
    rw [h₁ h₂, h₂]

section
set_option hygiene false

local syntax term " ⊢ " stlc_term " : " stlc_ty : term

local macro_rules
| `($Γ:term ⊢ $t:stlc_term : $τ:stlc_ty) => `(Judgement $Γ t[$t] τ[$τ])

inductive Judgement : Context → Term → Ty → Prop
| var {Γ x τ} : Γ x = some τ → Γ ⊢ $(Term.var x) : τ
| abs {Γ x τ₁ τ₂ t} : (x ↦ τ₂; Γ ⊢ t : τ₁) → Γ ⊢ λ x : τ₂, t : τ₂ → τ₁
| app {Γ τ τ' t₁ t₂} : (Γ ⊢ t₁ : τ → τ') → (Γ ⊢ t₂ : τ) → Γ ⊢ t₁ t₂ : τ'
| true {Γ} : Γ ⊢ true : Bool
| false {Γ} : Γ ⊢ false : Bool
| if {Γ τ t₁ t₂ t₃} : (Γ ⊢ t₁ : Bool) → (Γ ⊢ t₂ : τ) → (Γ ⊢ t₃ : τ) → Γ ⊢ if t₁ then t₂ else t₃ : τ

end

syntax term " ⊢ " stlc_term " : " stlc_ty : term
syntax "⊢ " stlc_term " : " stlc_ty : term

macro_rules
| `($Γ:term ⊢ $t:stlc_term : $τ:stlc_ty) => `(Judgement $Γ t[$t] τ[$τ])
| `(⊢ $t:stlc_term : $τ:stlc_ty) => `(Judgement ∅ t[$t] τ[$τ])

theorem progress {t : Term} {τ : Ty} : (⊢ t : τ) → Value t ∨ ∃ t', t ⟶ t' := by
  set Γ : Context := ∅ with hΓ
  clear_value Γ
  intro h
  induction h with subst hΓ
  | var h => cases h
  | abs | «true» | «false» =>
    left
    constructor
  | @app _ _ _ t₁ t₂ ht₁ _ iht₁ iht₂ =>
    simp_rw [forall_const] at iht₁ iht₂
    right
    rcases iht₁ with iht₁ | ⟨t₁', iht₁⟩
    · rcases iht₂ with iht₂ | ⟨t₂', iht₂⟩
      · cases ht₁ with
        | var | app | «if» => cases iht₁
        | @abs _ x _ _ t₁ =>
          use subst x t₂ t₁
          exact Step.app_cont iht₂
      · use t₁.app t₂'
        exact Step.app_cong_r iht₁ iht₂
    · use t₁'.app t₂
      exact Step.app_cong_l iht₁
  | @«if» _ _ t₁ t₂ t₃ ht₁ _ _ iht₁ =>
    simp_rw [forall_const] at iht₁
    right
    rcases iht₁ with iht₁ | ⟨t₁', iht₁⟩
    · cases ht₁ with
      | var | app | «if» => cases iht₁
      | «true» =>
        use t₂
        exact Step.if_cont_true
      | «false» =>
        use t₃
        exact Step.if_cont_false
    · use t₁'.if t₂ t₃
      exact Step.if_cong iht₁

theorem weakening {Γ Γ' : Context} {t : Term} {τ : Ty} : Γ ⊆ Γ' → (Γ ⊢ t : τ) → Γ' ⊢ t : τ := by
  intro hΓ h
  induction h generalizing Γ' with
  | var h => exact Judgement.var (hΓ h)
  | abs _ ih => exact Judgement.abs (ih (Context.includedIn_update hΓ))
  | app _ _ ih₁ ih₂ => exact Judgement.app (ih₁ hΓ) (ih₂ hΓ)
  | «true» | «false» => constructor
  | «if» _ _ _ ih₁ ih₂ ih₃ => exact Judgement.if (ih₁ hΓ) (ih₂ hΓ) (ih₃ hΓ)

theorem subst_preserves_typing {Γ x τ₁ t₁ t₂ τ₂} :
    (x ↦ τ₂; Γ ⊢ t₁ : τ₁) → (⊢ t₂ : τ₂) → Γ ⊢ [x := t₂] t₁ : τ₁ := by
  simp_rw [Context.update]
  intro h₁ h₂
  induction t₁ generalizing Γ τ₁ τ₂ with
  | var y => cases h₁ with | var h₁ =>
    by_cases hxy : x = y
    · subst hxy
      rw [Function.update_self, Option.some.injEq] at h₁
      rw [←h₁, subst, if_pos rfl]
      exact weakening Γ.includedIn_empty h₂
    · rw [Function.update_of_ne (Ne.symm hxy)] at h₁
      simp only [subst, hxy]
      exact Judgement.var h₁
  | abs y _ _ ih => cases h₁ with | abs h₁ =>
    by_cases hxy : x = y
    · subst hxy
      rw [Context.update, Function.update_idem] at h₁
      rw [subst, if_pos rfl]
      exact Judgement.abs h₁
    · simp only [subst, hxy]
      apply Judgement.abs
      rw [Context.update]
      apply ih _ h₂
      rwa [Function.update_comm (Ne.symm hxy)]
  | app _ _ ih₁ ih₂ => cases h₁ with | app h₃ h₄ =>
    exact Judgement.app (ih₁ h₃ h₂) (ih₂ h₄ h₂)
  | «true» | «false» =>
    cases h₁
    constructor
  | «if» _ _ _ ih₁ ih₂ ih₃ => cases h₁ with | «if» h₃ h₄ h₅ =>
    exact Judgement.if (ih₁ h₃ h₂) (ih₂ h₄ h₂) (ih₃ h₅ h₂)

theorem preservation {t t' : Term} {τ : Ty} : (⊢ t : τ) → (t ⟶ t') → ⊢ t' : τ := by
  set Γ : Context := ∅ with hΓ
  clear_value Γ
  intro h₁ h₂
  induction h₁ generalizing t' with subst hΓ
  | var | abs | «true» | «false» => cases h₂
  | app h₃ h₄ ih₁ ih₂ =>
    simp_rw [forall_const] at ih₁ ih₂
    cases h₂ with
    | app_cont => cases h₃ with | abs h₃ =>
      exact subst_preserves_typing h₃ h₄
    | app_cong_l h₅ => exact Judgement.app (ih₁ h₅) h₄
    | app_cong_r _ h₅ => exact Judgement.app h₃ (ih₂ h₅)
  | «if» _ h₃ h₄ ih₁ =>
    simp_rw [forall_const] at ih₁
    cases h₂ with
    | if_cont_true => exact h₃
    | if_cont_false => exact h₄
    | if_cong h₂ => exact Judgement.if (ih₁ h₂) h₃ h₄

def Term.Stuck (t : Term) : Prop := ¬Value t ∧ ¬∃ t', t ⟶ t'

theorem soundness {t t' : Term} {τ : Ty} : (⊢ t : τ) → (t ⟶* t') → ¬t'.Stuck := by
  intro h₁ h₂ ⟨_, _⟩
  induction h₂ using Relation.ReflTransGen.head_induction_on with
  | refl => cases progress h₁ <;> contradiction
  | head h₃ _ ih => exact ih (preservation h₁ h₃)

end Stlc
