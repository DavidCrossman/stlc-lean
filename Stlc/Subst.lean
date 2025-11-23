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

@[simp]
theorem Subst.subst_eq_of_closed {α β γ : Type*} {a : α} {b : β} {c : γ} [DecidableEq α]
  [FreeVars γ α] [FreeVars β α] [LawfulSubst α β γ] (hc : FreeVars.Closed c α) :
    subst a b c = c := by
  rw [LawfulSubst.subst_eq_of_notMem (hc.notMem_freeVars a)]

@[simp]
theorem Subst.idem_of_closed {α β γ : Type*} {a : α} {b₁ b₂ : β} {c : γ} [DecidableEq α]
  [FreeVars γ α] [FreeVars β α] [LawfulSubst α β γ] (hb₁ : FreeVars.Closed b₁ α) :
    subst a b₂ (subst a b₁ c) = subst a b₁ c := by
  rw [LawfulSubst.subst_eq_of_notMem]
  rw [LawfulSubst.freeVars_subst_eq_of_closed hb₁]
  exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton.mpr rfl)

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

@[simp]
theorem Term.subst_eq_of_notMem {x : TermVar} {t₁ t₂ : Term} :
    x ∉ t₂.freeVars → subst x t₁ t₂ = t₂ := by
  intro h
  induction t₂ with rw [subst]
  | var =>
    rw [freeVars, Finset.notMem_singleton] at h
    rw [if_neg h]
  | abs _ _ t ih =>
    rw [freeVars, Finset.mem_sdiff, Finset.mem_singleton, not_and_not_right] at h
    by_cases hx : x ∈ t.freeVars
    · rw [if_pos (h hx)]
    · rw [ih hx, ite_id]
  | app _ _ ih₁ ih₂ =>
    rw [freeVars, Finset.notMem_union] at h
    rw [ih₁ h.left, ih₂ h.right]
  | ite _ _ _ ih₁ ih₂ ih₃ =>
    rw [freeVars, Finset.notMem_union, Finset.notMem_union] at h
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
    rw [ih₁ h₁, ih₂ h₂, ih₃ h₃]

theorem Term.subst_comm {t₁ t₂ t : Term} {x₁ x₂ : TermVar} :
    x₁ ≠ x₂ → x₁ ∉ freeVars t₂ → x₂ ∉ freeVars t₁ →
    subst x₂ t₂ (subst x₁ t₁ t) = subst x₁ t₁ (subst x₂ t₂ t) := by
  intro _ h₁ h₂
  induction t with simp_rw [subst]
  | var =>
    split_ifs with hy₁ hy₂ hy₂
    · rw [←hy₂] at hy₁
      contradiction
    · rw [subst, if_pos hy₁, subst_eq_of_notMem h₂]
    · rw [subst, if_pos hy₂, subst_eq_of_notMem h₁]
    · rw [subst, subst, if_neg hy₂, if_neg hy₁]
  | abs _ _ _ ih =>
    split_ifs with hy₁ hy₂ hy₂
    · rw [←hy₂] at hy₁
      contradiction
    · rw [subst, subst, if_pos hy₁, if_neg hy₂]
    · rw [subst, subst, if_neg hy₁, if_pos hy₂]
    · rw [subst, subst, if_neg hy₁, if_neg hy₂, ih]
  | app _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | ite _ _ _ ih₁ ih₂ ih₃ => rw [ih₁, ih₂, ih₃]

@[simp]
theorem Term.freeVars_subst_eq_of_closed {x : TermVar} {t₁ t₂ : Term} :
    FreeVars.Closed t₁ TermVar → (subst x t₁ t₂).freeVars = t₂.freeVars \ {x} := fun _ ↦ by
  induction t₂ with rw [subst, freeVars]
  | var =>
    split_ifs with h
    · rwa [h, Finset.sdiff_self]
    · rw [freeVars, Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem]
      exact Finset.notMem_singleton.mpr h
  | abs _ _ _ ih =>
    split_ifs with h
    · rw [h, freeVars, Finset.sdiff_idem]
    · rw [freeVars, ih, sdiff_right_comm]
  | app t₃ t₄ ih₁ ih₂ => rw [freeVars, Finset.union_sdiff_distrib, ih₁, ih₂]
  | bool => rfl
  | ite _ _ _ ih₁ ih₂ ih₃ =>
    rw [freeVars, ih₁, ih₂, ih₃, Finset.union_sdiff_distrib, Finset.union_sdiff_distrib]

namespace Syntax

scoped syntax:lead "[" ident " := " stlc_term "]" stlc_term:max : stlc_term
scoped syntax:lead "[" str " := " stlc_term "]" stlc_term:max : stlc_term
scoped macro_rules
| `(t[ [$x:ident := $s:stlc_term] $t:stlc_term ]) => `(Subst.subst $x t[$s] t[$t])
| `(t[ [$x:str := $s:stlc_term] $t:stlc_term ]) => `(Subst.subst $x t[$s] t[$t])

end Syntax

end Stlc
