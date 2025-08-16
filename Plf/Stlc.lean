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

declare_syntax_cat stlc_ty
syntax "Bool" : stlc_ty
syntax:10 stlc_ty:11 " → " stlc_ty:10 : stlc_ty
syntax "(" stlc_ty ")" : stlc_ty
syntax "!" ident : stlc_ty
syntax "!(" term ")" : stlc_ty
syntax "λ→[" stlc_ty "]" : term

declare_syntax_cat stlc_term
syntax ident : stlc_term
syntax "λ" "!"? ident " : " stlc_ty " , " stlc_term : stlc_term
syntax "λ" "!(" term ")" " : " stlc_ty " , " stlc_term : stlc_term
syntax:80 stlc_term:80 stlc_term:81 : stlc_term
syntax "true" : stlc_term
syntax "false" : stlc_term
syntax "if " stlc_term " then " stlc_term " else " stlc_term : stlc_term
syntax "(" stlc_term ")" : stlc_term
syntax "!" ident : stlc_term
syntax "!(" term ")" : stlc_term
syntax "λ→(" stlc_term ")" : term

macro_rules
| `(λ→[Bool]) => `(Ty.Bool)
| `(λ→[$l:stlc_ty → $r:stlc_ty]) => `(Ty.Arrow λ→[$l] λ→[$r])
| `(λ→[($ty:stlc_ty)]) => `(λ→[$ty])
| `(λ→[!$x:ident]) => pure x
| `(λ→[!($t:term)]) => pure t

macro_rules
| `(λ→($x:ident)) => `(Term.Var $(Lean.quote (toString x.getId)))
| `(λ→(λ $x:ident : $ty:stlc_ty, $term:stlc_term)) =>
    `(Term.Abs $(Lean.quote (toString x.getId)) λ→[$ty] λ→($term))
| `(λ→(λ !$x:ident : $ty:stlc_ty, $term:stlc_term)) =>
    `(Term.Abs $x λ→[$ty] λ→($term))
| `(λ→(λ !($x:term) : $ty:stlc_ty, $term:stlc_term)) =>
    `(Term.Abs $x λ→[$ty] λ→($term))
| `(λ→($l:stlc_term $r:stlc_term)) => `(Term.App λ→($l) λ→($r))
| `(λ→(true)) => `(Term.True)
| `(λ→(false)) => `(Term.False)
| `(λ→(if $t₁:stlc_term then $t₂:stlc_term else $t₃:stlc_term)) =>
    `(Term.If λ→($t₁) λ→($t₂) λ→($t₃))
| `(λ→(($term:stlc_term))) => `(λ→($term))
| `(λ→(!$x:ident)) => pure x
| `(λ→(!($t:term))) => pure t

end Stlc
