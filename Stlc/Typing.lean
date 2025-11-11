import Mathlib.Logic.Function.Basic
import Stlc.Basic
import Stlc.Syntax

namespace Stlc

def Context : Type := TermVar → Option Ty

instance : EmptyCollection Context :=
  ⟨fun _ ↦ none⟩

def Context.update (Γ : Context) (x : TermVar) (τ : Ty) : Context :=
  Function.update Γ x (some τ)


def Context.IncludedIn (Γ Γ' : Context) : Prop :=
  ∀ ⦃x τ⦄, Γ x = some τ → Γ' x = some τ

instance : HasSubset Context :=
  ⟨Context.IncludedIn⟩

theorem Context.includedIn_empty (Γ : Context) : ∅ ⊆ Γ := by
  rintro _ _ ⟨⟩

theorem Context.includedIn_update {Γ Γ' : Context} {x : TermVar} {τ : Ty} :
    Γ ⊆ Γ' → Γ.update x τ ⊆ Γ'.update x τ := by
  simp only [Subset, IncludedIn, update, Function.update_apply]
  intro h₁ y τ' h₂
  rw [←h₂]
  split_ifs with hyx
  · rfl
  · rw [if_neg hyx] at h₂
    rw [h₁ h₂, h₂]

@[simp]
theorem Context.update_self (x : TermVar) (τ : Ty) (Γ : Context) :
    Γ.update x τ x = τ := by
  exact Function.update_self x τ Γ

theorem Context.update_of_ne {x x' : TermVar} (h : x ≠ x') (τ : Ty) (Γ : Context) :
    Γ.update x' τ x = Γ x := by
  exact Function.update_of_ne h τ Γ

@[simp]
theorem Context.update_idem {x : TermVar} (τ₁ τ₂ : Ty) (Γ : Context) :
    (Γ.update x τ₁).update x τ₂ = Γ.update x τ₂ := by
  exact Function.update_idem τ₁ τ₂ Γ

theorem Context.update_comm {x₁ x₂ : TermVar} (h : x₁ ≠ x₂) (τ₁ τ₂ : Ty) (Γ : Context) :
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
| `($Γ:stlc_ctx ⊢ $t:stlc_term : $τ:stlc_ty) => `(Judgement Γ[$Γ] t[$t] τ[$τ])

inductive Judgement : Context → Term → Ty → Prop
| var {Γ x τ} : Γ x = some τ → Γ ⊢ xⱽ : τ
| abs {Γ x τ₁ τ₂ t} : (Γ; x ↦ τ₂ ⊢ t : τ₁) → Γ ⊢ λ x : τ₂, t : τ₂ → τ₁
| app {Γ τ τ' t₁ t₂} : (Γ ⊢ t₁ : τ → τ') → (Γ ⊢ t₂ : τ) → Γ ⊢ t₁ t₂ : τ'
| bool {Γ} b : Γ ⊢ $(.bool b) : Bool
| ite {Γ τ t₁ t₂ t₃} : (Γ ⊢ t₁ : Bool) → (Γ ⊢ t₂ : τ) → (Γ ⊢ t₃ : τ) → Γ ⊢ if t₁ then t₂ else t₃ : τ

end

@[match_pattern]
notation Γ " ⊢ " t " : " τ => Judgement Γ t τ

namespace Syntax

scoped syntax stlc_ctx " ⊢' " stlc_term " : " stlc_ty : term
scoped syntax "⊢' " stlc_term " : " stlc_ty : term

scoped macro_rules
| `($Γ:stlc_ctx ⊢' $t:stlc_term : $τ:stlc_ty) => `(Γ[$Γ] ⊢ t[$t] : τ[$τ])
| `(⊢' $t:stlc_term : $τ:stlc_ty) => `(∅ ⊢ t[$t] : τ[$τ])

end Syntax

end Stlc
