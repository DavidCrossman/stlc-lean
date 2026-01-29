import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
import Stlc.Basic
import Stlc.Syntax

namespace Stlc

variable {c : Config}

def Context (c : Config) : Type := TermVar → Option (Ty c)

@[ext]
def Context.ext {Γ₁ Γ₂ : Context c} (h : ∀ x, Γ₁ x = Γ₂ x) : Γ₁ = Γ₂ :=
  funext h

instance : EmptyCollection (Context c) :=
  ⟨fun _ ↦ none⟩

def Context.update (Γ : Context c) (x : TermVar) (τ : Ty c) : Context c :=
  Function.update Γ x (some τ)

def Context.IncludedIn (Γ Γ' : Context c) : Prop :=
  ∀ ⦃x τ⦄, Γ x = some τ → Γ' x = some τ

instance : HasSubset (Context c) :=
  ⟨Context.IncludedIn⟩

theorem Context.includedIn_empty (Γ : Context c) : ∅ ⊆ Γ := by
  rintro _ _ ⟨⟩

theorem Context.includedIn_update {Γ Γ' : Context c} {x : TermVar} {τ : Ty c} :
    Γ ⊆ Γ' → Γ.update x τ ⊆ Γ'.update x τ := by
  simp only [Subset, IncludedIn, update, Function.update_apply]
  intro h₁ y τ' h₂
  rw [←h₂]
  split_ifs with hyx
  · rfl
  · rw [if_neg hyx] at h₂
    rw [h₁ h₂, h₂]

@[simp]
theorem Context.update_self (x : TermVar) (τ : Ty c) (Γ : Context c) :
    Γ.update x τ x = τ := by
  exact Function.update_self x τ Γ

theorem Context.update_of_ne {x x' : TermVar} (h : x ≠ x') (τ : Ty c) (Γ : Context c) :
    Γ.update x' τ x = Γ x := by
  exact Function.update_of_ne h τ Γ

@[simp]
theorem Context.update_idem {x : TermVar} (τ₁ τ₂ : Ty c) (Γ : Context c) :
    (Γ.update x τ₁).update x τ₂ = Γ.update x τ₂ := by
  exact Function.update_idem _ _ Γ

theorem Context.update_comm {x₁ x₂ : TermVar} (h : x₁ ≠ x₂) (τ₁ τ₂ : Ty c) (Γ : Context c) :
    (Γ.update x₁ τ₁).update x₂ τ₂ = (Γ.update x₂ τ₂).update x₁ τ₁ := by
  exact Function.update_comm h τ₁ τ₂ Γ

namespace Syntax

declare_syntax_cat stlc_ctx
scoped syntax stlc_ident : stlc_ctx
scoped syntax "∅" : stlc_ctx
scoped syntax stlc_ctx "; " term:arg " ↦ " term:arg : stlc_ctx
scoped syntax "Γ[ " stlc_ctx " ]" : term

scoped macro_rules
| `(Γ[ $x:stlc_ident ]) => `(x[$x])
| `(Γ[ ∅ ]) => `((∅ : Context))
| `(Γ[ $Γ:stlc_ctx; $x:term ↦ $τ:term ]) => `(Context.update Γ[$Γ] $x $τ)

end Syntax

section
set_option hygiene false

open Syntax

local syntax stlc_ctx " ⊢ " stlc_term " : " stlc_ty : term

local macro_rules
| `($Γ:stlc_ctx ⊢ $t:stlc_term : $τ:stlc_ty) => `(Judgement _ Γ[$Γ] t[$t] τ[$τ])

inductive Judgement (c : Config) : Context c → Term c → Ty c → Prop
| var {Γ x τ} : Γ x = some τ → Γ ⊢ xⱽ : τ
| abs {Γ x τ₁ τ₂ t} : (Γ; x ↦ τ₂ ⊢ t : τ₁) → Γ ⊢ λ x : τ₂, t : τ₂ → τ₁
| app {Γ τ τ' t₁ t₂} : (Γ ⊢ t₁ : τ → τ') → (Γ ⊢ t₂ : τ) → Γ ⊢ t₁ t₂ : τ'
| bool {Γ} b [c.HasBool] : Γ ⊢ #.bool b# : Bool
| ite {Γ τ t₁ t₂ t₃} [c.HasBool] :
  (Γ ⊢ t₁ : Bool) → (Γ ⊢ t₂ : τ) → (Γ ⊢ t₃ : τ) → Γ ⊢ if t₁ then t₂ else t₃ : τ

end

@[match_pattern]
notation Γ " ⊢ " t " : " τ => Judgement _ Γ t τ

namespace Syntax

scoped syntax stlc_ctx " ⊢' " stlc_term " : " stlc_ty : term
scoped syntax "⊢' " stlc_term " : " stlc_ty : term

scoped macro_rules
| `($Γ:stlc_ctx ⊢' $t:stlc_term : $τ:stlc_ty) => `(Γ[$Γ] ⊢ t[$t] : τ[$τ])
| `(⊢' $t:stlc_term : $τ:stlc_ty) => `(∅ ⊢ t[$t] : τ[$τ])

end Syntax

open Syntax in
@[simp]
def Term.typeCheck (Γ : Context c) : Term c → Option (Ty c)
| t[xⱽ] => Γ x
| t[λ x : τ, t] => do
  let τ' ← t.typeCheck (Γ.update x τ)
  τ[τ → τ']
| t[t₁ t₂] => do
  let τ[τ₁ → τ₂] ← t₁.typeCheck Γ | failure
  unless (← t₂.typeCheck Γ) = τ₁ do failure
  τ₂
| bool _ => some .bool
| t[if t₁ then t₂ else t₃] => do
  let .bool ← t₁.typeCheck Γ | failure
  let τ₂ ← t₂.typeCheck Γ
  unless (← t₃.typeCheck Γ) = τ₂ do failure
  τ₂

theorem Term.typeCheck_sound {Γ : Context c} {t : Term c} {τ : Ty c} :
    t.typeCheck Γ = some τ → Γ ⊢ t : τ := by
  intro h
  induction t generalizing Γ τ with rw [Term.typeCheck] at h
  | var => exact Judgement.var h
  | abs _ _ _ ih =>
    rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h, ⟨⟩⟩ := h
    exact Judgement.abs (ih h)
  | app _ _ ih₁ ih₂ =>
    rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟩, h₁, h₂⟩ := h
    · contradiction
    · rw [Option.bind_eq_some_iff] at h₂
      obtain ⟨_, h₂, h₃⟩ := h₂
      split_ifs at h₃ with h₄
      · cases h₃
        subst h₄
        exact Judgement.app (ih₁ h₁) (ih₂ h₂)
      · contradiction
  | bool b =>
    cases h
    exact Judgement.bool b
  | ite _ _ _ ih₁ ih₂ ih₃ =>
    rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟩, h₁, h₂⟩ := h
    · rw [Option.bind_eq_some_iff] at h₂
      obtain ⟨_, h₂, h₃⟩ := h₂
      rw [Option.bind_eq_some_iff] at h₃
      obtain ⟨_, h₃, h₄⟩ := h₃
      split_ifs at h₄ with h₅
      · cases h₄
        subst h₅
        exact Judgement.ite (ih₁ h₁) (ih₂ h₂) (ih₃ h₃)
      · contradiction
    · contradiction

theorem Term.typeCheck_complete {Γ : Context c} {t : Term c} {τ : Ty c} :
    (Γ ⊢ t : τ) → t.typeCheck Γ = some τ := by
  intro J
  induction J with
  | var h => exact h
  | abs _ ih => simp [ih]
  | app _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | bool => rfl
  | ite _ _ _ ih₁ ih₂ ih₃ => simp [ih₁, ih₂, ih₃]

theorem Term.typeCheck_iff_judgement {Γ : Context c} {t : Term c} {τ : Ty c} :
    t.typeCheck Γ = some τ ↔ (Γ ⊢ t : τ) :=
  ⟨Term.typeCheck_sound, Term.typeCheck_complete⟩

instance {Γ : Context c} {t : Term c} {τ : Ty c} : Decidable (Γ ⊢ t : τ) :=
  decidable_of_decidable_of_iff Term.typeCheck_iff_judgement

end Stlc
