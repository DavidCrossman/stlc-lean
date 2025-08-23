import Mathlib.Logic.Relation
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

@[mk_iff]
inductive Value : Term → Prop
| abs x T t : Value λ→(λ !x : !T, !t)
| true : Value λ→(true)
| false : Value λ→(false)

attribute [simp] Value.abs Value.true Value.false

def Term.value : Term → «Bool»
| .true | .false | .abs .. => Bool.true
| _ => Bool.false

theorem Term.value_iff (t : Term) : t.value ↔ Value t := by
  rw [Stlc.value_iff]
  cases t <;> simp [value]

@[simp]
def subst (x : String) (s t : Term) : Term := match t with
| .var y => if x == y then s else t
| λ→(λ !y : !T, !t₁) => if x == y then t else λ→(λ !y : !T, !(subst x s t₁))
| λ→(!t₁ !t₂) => λ→(!(subst x s t₁) !(subst x s t₂))
| λ→(true) | λ→(false) => t
| λ→(if !t₁ then !t₂ else !t₃) =>
    λ→(if !(subst x s t₁) then !(subst x s t₂) else !(subst x s t₃))

notation "[" x " := " s "] " t:max => subst x s t

inductive Step : Term → Term → Prop
| app_cont {x T t v} :
    Value v → Step λ→((λ !x: !T, !t) !v) λ→(!([x := v] t))
| app_cong_l {t₁ t₁' t₂} : Step t₁ t₁' → Step λ→(!t₁ !t₂) λ→(!t₁' !t₂)
| app_cong_r {v t t'} : Value v → Step t t' → Step λ→(!v !t) λ→(!v !t')
| if_cont_true {t₁ t₂} : Step λ→(if true then !t₁ else !t₂) t₁
| if_cont_false {t₁ t₂} : Step λ→(if false then !t₁ else !t₂) t₂
| if_cong {t₁ t₁' t₂ t₃} :
    Step t₁ t₁' → Step λ→(if !t₁ then !t₂ else !t₃) λ→(if !t₁' then !t₂ else !t₃)

def Steps := Relation.ReflTransGen Step

infixr:10 " ⟶ " => Step

infixr:10 " ⟶* " => Steps

theorem Value.no_step {t t' : Term} : Value t → ¬(t ⟶ t') := by
  rintro ⟨⟩ <;> rintro ⟨⟩

theorem Step.not_value {t t' : Term} : (t ⟶ t') → ¬Value t := by
  contrapose
  push_neg
  exact Value.no_step

def Term.step : Term → Option Term
| λ→((λ !x : !T, !t₁) !t₂) =>
    if t₂.value then [x := t₂] t₁ else t₂.step.map <| .app (.abs x T t₁)
| λ→(!t₁ !t₂) => if t₁.value then t₂.step.map (.app t₁) else t₁.step.map (.app · t₂)
| λ→(if true then !t else !(_)) | λ→(if false then !(_) else !t) => t
| λ→(if !t₁ then !t₂ else !t₃) => t₁.step.map (.if · t₂ t₃)
| _ => none

theorem Value.no_step {v t : Term} : Value v → ¬(v ⟶ t) := by
  intro hv hvt
  induction hvt <;> cases hv

theorem Step.unique {t t₁ t₂} : (t ⟶ t₁) → (t ⟶ t₂) → t₁ = t₂ := by
  intro h1 h2
  induction h1 generalizing t₂ with
  | app_cont v => cases h2 with
    | app_cont => rfl
    | app_cong_l h3 => cases h3
    | app_cong_r _ h3 => cases v.no_step h3
  | app_cong_l h3 ih => cases h2 with
    | app_cont => cases (Value.abs ..).no_step h3
    | app_cong_l h4 => rw [ih h4]
    | app_cong_r v => cases v.no_step h3
  | app_cong_r v h3 ih => cases h2 with
    | app_cont v2 => cases v2.no_step h3
    | app_cong_l h4 => cases v.no_step h4
    | app_cong_r _ h4 => rw [ih h4]
  | if_cont_true => cases h2 with
    | if_cont_true => rfl
    | if_cong h3 => cases Value.true.no_step h3
  | if_cont_false => cases h2 with
    | if_cont_false => rfl
    | if_cong h3 => cases Value.false.no_step h3
  | if_cong h3 ih => cases h2 with
    | if_cont_true => cases Value.true.no_step h3
    | if_cont_false => cases Value.false.no_step h3
    | if_cong h4 => rw [ih h4]

@[refl, simp]
theorem Steps.refl {t : Term} : t ⟶* t := Relation.ReflTransGen.refl

theorem Steps.head {t₁ t₂ t₃ : Term} : (t₁ ⟶ t₂) → (t₂ ⟶* t₃) → (t₁ ⟶* t₃) :=
  Relation.ReflTransGen.head

theorem Steps.cont_iff {t₁ t₂ v : Term} (hv : Value v) (h : t₁ ⟶ t₂) :
    (t₁ ⟶* v) ↔ (t₂ ⟶* v) := by
  constructor
  · intro h2
    obtain (rfl | ⟨t₃, h3, h4⟩) := h2.cases_head
    · cases hv.no_step h
    · rw [h.unique h3]
      exact h4
  · intro h2
    apply Steps.head h
    exact h2

end Stlc
