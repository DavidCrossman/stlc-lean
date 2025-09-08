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
| ite : Term → Term → Term → Term
deriving DecidableEq

end Stlc
