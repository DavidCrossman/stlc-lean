namespace Stlc

def TermVar : Type := String
deriving DecidableEq

inductive Ty : Type
| bool
| arrow : Ty → Ty → Ty
deriving DecidableEq

inductive Term : Type
| var : TermVar → Term
| abs : TermVar → Ty → Term → Term
| app : Term → Term → Term
| bool : Bool → Term
| ite : Term → Term → Term → Term
deriving DecidableEq

end Stlc
