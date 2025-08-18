import Mathlib.Tactic

namespace Stlc

inductive Ty : Type
| bool
| arrow : Ty → Ty → Ty

inductive Term : Type
| var : String → Term
| abs : String → Ty → Term → Term
| app : Term → Term → Term
| true
| false
| if : Term → Term → Term → Term

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
| `(λ→[Bool]) => `(Ty.bool)
| `(λ→[$l:stlc_ty → $r:stlc_ty]) => `(Ty.arrow λ→[$l] λ→[$r])
| `(λ→[($ty:stlc_ty)]) => `(λ→[$ty])
| `(λ→[!$x:ident]) => pure x
| `(λ→[!($t:term)]) => pure t

macro_rules
| `(λ→($x:ident)) => `(Term.var $(Lean.quote (toString x.getId)))
| `(λ→(λ $x:ident : $ty:stlc_ty, $term:stlc_term)) =>
    `(Term.abs $(Lean.quote (toString x.getId)) λ→[$ty] λ→($term))
| `(λ→(λ !$x:ident : $ty:stlc_ty, $term:stlc_term)) =>
    `(Term.abs $x λ→[$ty] λ→($term))
| `(λ→(λ !($x:term) : $ty:stlc_ty, $term:stlc_term)) =>
    `(Term.abs $x λ→[$ty] λ→($term))
| `(λ→($l:stlc_term $r:stlc_term)) => `(Term.app λ→($l) λ→($r))
| `(λ→(true)) => `(Term.true)
| `(λ→(false)) => `(Term.false)
| `(λ→(if $t₁:stlc_term then $t₂:stlc_term else $t₃:stlc_term)) =>
    `(Term.if λ→($t₁) λ→($t₂) λ→($t₃))
| `(λ→(($term:stlc_term))) => `(λ→($term))
| `(λ→(!$x:ident)) => pure x
| `(λ→(!($t:term))) => pure t

inductive Value : Term → Prop
| abs x T t : Value λ→(λ !x : !T, !t)
| true : Value λ→(true)
| false : Value λ→(false)

attribute [simp] Value.abs Value.true Value.false

@[simp]
def subst (x : String) (s t : Term) : Term := match t with
| Term.var y => if x == y then s else t
| λ→(λ !y : !T, !t₁) => if x == y then t else λ→(λ !y : !T, !(subst x s t₁))
| λ→(!t₁ !t₂) => λ→(!(subst x s t₁) !(subst x s t₂))
| λ→(true) | λ→(false) => t
| λ→(if !t₁ then !t₂ else !t₃) =>
    λ→(if !(subst x s t₁) then !(subst x s t₂) else !(subst x s t₃))

notation "[" x " := " s "] " t => subst x s t

end Stlc
