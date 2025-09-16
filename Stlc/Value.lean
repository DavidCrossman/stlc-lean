import Mathlib.Tactic.Common
import Stlc.Syntax

namespace Stlc.Term

open Syntax

@[mk_iff]
inductive Value : Term → Prop
| abs {x τ t} : Value t[λ x : τ, t]
| true : Value t[true]
| false : Value t[false]

attribute [simp] Value.abs Value.true Value.false

@[simp]
lemma Value.var_not {x : String} : ¬Value (var x) := by
  rintro ⟨⟩

@[simp]
lemma Value.app_not {t₁ t₂ : Term} : ¬Value t[t₁ t₂] := by
  rintro ⟨⟩

@[simp]
lemma Value.ite_not {t₁ t₂ t₃ : Term} : ¬Value t[if t₁ then t₂ else t₃] := by
  rintro ⟨⟩

instance : DecidablePred Value := fun t ↦
  decidable_of_bool (t matches .true | .false | .abs ..) (by cases t <;> simp)

end Stlc.Term
