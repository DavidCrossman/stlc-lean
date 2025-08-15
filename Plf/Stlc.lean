namespace Stlc

inductive Ty : Type
| Bool
| Arrow : Ty → Ty → Ty

inductive Term : Type
| Var : String → Term
| Abs : String → Ty → Term → Term
| App : Term → Term → Term
| True
| False
| If : Term → Term → Term → Term
