import Mathlib.Data.Finset.SDiff
import Stlc.Basic
import Stlc.Syntax

namespace Stlc

open Syntax

class FreeVars (α β : Type*) [DecidableEq β] where
  freeVars : α → Finset β

attribute [simp] FreeVars.freeVars

@[simp]
def FreeVars.Closed {α : Type*} (a : α) (β : Type*) [DecidableEq β] [FreeVars α β] : Prop :=
  (freeVars a : Finset β) = ∅

def FreeVars.Closed.notMem_freeVars {α β : Type*} {a : α} [DecidableEq β] [FreeVars α β]
    (hc : Closed a β) (b : β) : b ∉ freeVars a := by
  rw [hc]
  exact Finset.notMem_empty b

@[simp]
def Term.freeVars : Term → Finset TermVar
| t[xⱽ] => {x}
| t[λ x : _, t] => t.freeVars \ {x}
| t[t₁ t₂]  => t₁.freeVars ∪ t₂.freeVars
| .bool _ => ∅
| t[if t₁ then t₂ else t₃] => t₁.freeVars ∪ t₂.freeVars ∪ t₃.freeVars

instance : FreeVars Term TermVar :=
  ⟨Term.freeVars⟩

end Stlc
