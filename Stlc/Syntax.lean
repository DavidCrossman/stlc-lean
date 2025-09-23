import Stlc.Basic

namespace Stlc.Syntax

declare_syntax_cat stlc_ident
scoped syntax ident : stlc_ident
scoped syntax hole : stlc_ident

declare_syntax_cat stlc_ty
scoped syntax:max stlc_ident : stlc_ty
scoped syntax "Bool" : stlc_ty
scoped syntax:10 stlc_ty:11 " → " stlc_ty:10 : stlc_ty
scoped syntax "(" stlc_ty ")" : stlc_ty
scoped syntax "$(" term ")" : stlc_ty

declare_syntax_cat stlc_term
scoped syntax:max stlc_ident : stlc_term
scoped syntax:max stlc_ident "ⱽ" : stlc_term
scoped syntax:max str : stlc_term
scoped syntax:lead "λ " str " : " stlc_ty ", " stlc_term : stlc_term
scoped syntax:lead "λ " stlc_ident " : " stlc_ty ", " stlc_term : stlc_term
scoped syntax:arg stlc_term:arg stlc_term:max : stlc_term
scoped syntax:max "true" : stlc_term
scoped syntax:max "false" : stlc_term
scoped syntax:lead "if " stlc_term " then " stlc_term " else " stlc_term : stlc_term
scoped syntax "(" stlc_term ")" : stlc_term
scoped syntax "$(" term ")" : stlc_term

scoped syntax "x[ " stlc_ident " ]" : term
scoped syntax "τ[ " stlc_ty " ]" : term
scoped syntax "t[ " stlc_term " ]" : term

scoped macro_rules
| `(x[ $x:ident ]) => return x
| `(x[ $x:hole ]) => return x

scoped macro_rules
| `(τ[ $x:stlc_ident ]) => `(x[$x])
| `(τ[ Bool ]) => `(Ty.bool)
| `(τ[ $τ₁:stlc_ty → $τ₂:stlc_ty ]) => `(Ty.arrow τ[$τ₁] τ[$τ₂])
| `(τ[ ($τ:stlc_ty) ]) => `(τ[$τ])
| `(τ[ $($t:term) ]) => return t

scoped macro_rules
| `(t[ $x:stlc_ident ]) => `(x[$x])
| `(t[ $x:stlc_identⱽ ]) => `(Term.var x[$x])
| `(t[ $x:str ]) => `(Term.var $x)
| `(t[ λ $x:stlc_ident : $τ:stlc_ty, $t:stlc_term ]) => `(Term.abs x[$x] τ[$τ] t[$t])
| `(t[ λ $x:str : $τ:stlc_ty, $t:stlc_term ]) => `(Term.abs $x τ[$τ] t[$t])
| `(t[ $t₁:stlc_term $t₂:stlc_term ]) => `(Term.app t[$t₁] t[$t₂])
| `(t[ true ]) => `(Term.true)
| `(t[ false ]) => `(Term.false)
| `(t[ if $t₁:stlc_term then $t₂:stlc_term else $t₃:stlc_term ]) => `(Term.ite t[$t₁] t[$t₂] t[$t₃])
| `(t[ ($t:stlc_term) ]) => `(t[$t])
| `(t[ $($t:term) ]) => return t

end Stlc.Syntax
