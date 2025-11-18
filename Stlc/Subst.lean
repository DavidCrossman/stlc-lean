import Mathlib.Data.Finset.Basic
import Stlc.FreeVars

namespace Stlc

class Subst (α β γ : Type*) where
  subst : α → β → γ → γ

attribute [simp] Subst.subst

class LawfulSubst (α β γ : Type*) [DecidableEq α] [FreeVars γ α] [FreeVars β α]
    extends Subst α β γ where
  subst_eq_of_notMem {a : α} {b : β} {c : γ} : a ∉ FreeVars.freeVars c → subst a b c = c
  subst_comm {a₁ a₂ : α} {b₁ b₂ : β} {c : γ} :
    a₁ ≠ a₂ → a₁ ∉ FreeVars.freeVars b₂ → a₂ ∉ FreeVars.freeVars b₁ →
    subst a₂ b₂ (subst a₁ b₁ c) = subst a₁ b₁ (subst a₂ b₂ c)
  freeVars_subst_eq_of_closed {a : α} {b : β} {c : γ} :
    FreeVars.Closed b α → FreeVars.freeVars (subst a b c) = FreeVars.freeVars c \ {a}

attribute [simp] LawfulSubst.subst_eq_of_notMem LawfulSubst.freeVars_subst_eq_of_closed

section
set_option hygiene false

open Syntax

local syntax:lead "[" ident " := " stlc_term "]" stlc_term:max : stlc_term
local macro_rules
| `(t[ [$x:ident := $s:stlc_term] $t:stlc_term ]) => `(Term.subst $x t[$s] t[$t])

@[simp]
def Term.subst (x : TermVar) (s t : Term) : Term := match t with
| t[yⱽ] => if x = y then s else t
| t[λ y : τ, t'] => if x = y then t else t[λ y : τ, [x := s] t']
| t[t₁ t₂] => t[([x := s] t₁) ([x := s] t₂)]
| .bool _ => t
| t[if t₁ then t₂ else t₃] => t[if [x := s] t₁ then [x := s] t₂ else [x := s] t₃]

end

instance : Subst TermVar Term Term :=
  ⟨Term.subst⟩

namespace Syntax

scoped syntax:lead "[" ident " := " stlc_term "]" stlc_term:max : stlc_term
scoped syntax:lead "[" str " := " stlc_term "]" stlc_term:max : stlc_term
scoped macro_rules
| `(t[ [$x:ident := $s:stlc_term] $t:stlc_term ]) => `(Subst.subst $x t[$s] t[$t])
| `(t[ [$x:str := $s:stlc_term] $t:stlc_term ]) => `(Subst.subst $x t[$s] t[$t])

end Syntax

end Stlc
