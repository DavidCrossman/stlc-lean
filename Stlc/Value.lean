import Mathlib.Tactic.Common
import Stlc.Syntax

namespace Stlc.Term

open Syntax

@[mk_iff]
inductive Value : Term → Prop
| abs {x τ t} : Value t[λ x : τ, t]
| bool {b} : Value (.bool b)

attribute [simp] Value.abs Value.bool

@[simp]
lemma Value.var_not {x : String} : ¬Value t[xⱽ] := by
  rintro ⟨⟩

@[simp]
lemma Value.app_not {t₁ t₂ : Term} : ¬Value t[t₁ t₂] := by
  rintro ⟨⟩

@[simp]
lemma Value.ite_not {t₁ t₂ t₃ : Term} : ¬Value t[if t₁ then t₂ else t₃] := by
  rintro ⟨⟩

instance : DecidablePred Value := fun t ↦
  decidable_of_bool (t matches .bool _ | .abs ..) (by cases t <;> simp)

end Stlc.Term
