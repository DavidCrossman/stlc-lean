import Mathlib.Tactic.Common
import Stlc.Syntax

namespace Stlc.Term

variable {c : Config}

open Syntax

@[mk_iff]
inductive Value : Term c → Prop
| abs {x τ t} : Value t[λ x : τ, t]
| bool {b} [c.HasBool] : Value (bool b)

attribute [simp] Value.abs Value.bool

@[simp]
lemma Value.var_not {x : TermVar} : ¬@Value c t[xⱽ] := by
  rintro ⟨⟩

@[simp]
lemma Value.app_not {t₁ t₂ : Term c} : ¬Value t[t₁ t₂] := by
  rintro ⟨⟩

@[simp]
lemma Value.ite_not {t₁ t₂ t₃ : Term c} [c.HasBool] : ¬Value t[if t₁ then t₂ else t₃] := by
  rintro ⟨⟩

instance : DecidablePred (@Value c) := fun t ↦
  decidable_of_bool (t matches bool _ | abs ..) (by cases t <;> simp)

end Stlc.Term
