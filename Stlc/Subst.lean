import Stlc.Basic
import Stlc.Syntax

namespace Stlc

section
set_option hygiene false

open Syntax

local syntax:lead "[" ident " := " stlc_term "]" stlc_term:max : stlc_term
local macro_rules
| `(t[ [$x:ident := $s:stlc_term] $t:stlc_term ]) => `(subst $x t[$s] t[$t])

@[simp]
def subst (x : String) (s t : Term) : Term := match t with
| .var y => if x = y then s else t
| t[λ y : τ, t'] => if x = y then t else t[λ y : τ, [x := s] t']
| t[t₁ t₂] => t[([x := s] t₁) ([x := s] t₂)]
| t[true] | t[false] => t
| t[if t₁ then t₂ else t₃] => t[if [x := s] t₁ then [x := s] t₂ else [x := s] t₃]

end

namespace Syntax

scoped syntax:lead "[" ident " := " stlc_term "]" stlc_term:max : stlc_term
scoped syntax:lead "[" str " := " stlc_term "]" stlc_term:max : stlc_term
scoped macro_rules
| `(t[ [$x:ident := $s:stlc_term] $t:stlc_term ]) => `(subst $x t[$s] t[$t])
| `(t[ [$x:str := $s:stlc_term] $t:stlc_term ]) => `(subst $x t[$s] t[$t])

end Syntax

end Stlc
