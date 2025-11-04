import Stlc.Step
import Stlc.Typing

namespace Stlc

theorem progress {t : Term} {τ : Ty} : (∅ ⊢ t : τ) → t.Value ∨ ∃ t', t ⟶ t' := by
  generalize hΓ : (∅ : Context) = Γ
  intro J
  induction J with subst hΓ
  | var h => cases h
  | abs | «true» | «false» =>
    left
    constructor
  | @app _ _ _ t₁ t₂ J' _ iht₁ iht₂ =>
    right
    obtain ht₁ | ⟨t₁', ht₁⟩ := iht₁ rfl
    · obtain ht₂ | ⟨t₂', ht₂⟩ := iht₂ rfl
      · cases J' with
        | var | app | ite => cases ht₁
        | @abs _ x _ _ t₁ =>
          use subst x t₂ t₁
          exact Step.app_cont ht₂
      · use t₁.app t₂'
        exact Step.app_cong_r ht₁ ht₂
    · use t₁'.app t₂
      exact Step.app_cong_l ht₁
  | @ite _ _ t₁ t₂ t₃ J' _ _ iht₁ =>
    right
    obtain ht₁ | ⟨t₁', ht₁⟩ := iht₁ rfl
    · cases J' with
      | var | app | ite => cases ht₁
      | «true» =>
        use t₂
        exact Step.ite_cont_true
      | «false» =>
        use t₃
        exact Step.ite_cont_false
    · use t₁'.ite t₂ t₃
      exact Step.ite_cong ht₁

theorem weakening {Γ Γ' : Context} {t : Term} {τ : Ty} : Γ ⊆ Γ' → (Γ ⊢ t : τ) → Γ' ⊢ t : τ := by
  intro hΓ h
  induction h generalizing Γ' with
  | var h => exact Judgement.var (hΓ h)
  | abs _ ih => exact Judgement.abs (ih (Context.includedIn_update hΓ))
  | app _ _ ih₁ ih₂ => exact Judgement.app (ih₁ hΓ) (ih₂ hΓ)
  | «true» | «false» => constructor
  | ite _ _ _ ih₁ ih₂ ih₃ => exact Judgement.ite (ih₁ hΓ) (ih₂ hΓ) (ih₃ hΓ)

open Syntax in
theorem subst_preserves_typing {Γ : Context} {τ₁ τ₂ : Ty} {t₁ t₂ : Term} {x : String} :
    (x ↦ τ₂; Γ ⊢ t₁ : τ₁) → (∅ ⊢ t₂ : τ₂) → Γ ⊢' [x := t₂] t₁ : τ₁ := by
  intro J₁ J₂
  induction t₁ generalizing Γ τ₁ τ₂ with rw [subst]
  | var y => cases J₁ with | var h =>
    split_ifs with hxy
    · rw [hxy, Context.update_self, Option.some.injEq] at h
      subst h
      exact weakening Γ.includedIn_empty J₂
    · rw [Context.update_of_ne (Ne.symm hxy)] at h
      exact Judgement.var h
  | abs _ _ _ ih => cases J₁ with | abs J₁ =>
    split_ifs with hxy
    · subst hxy
      rw [Context.update_idem] at J₁
      exact Judgement.abs J₁
    · rw [Context.update_comm hxy] at J₁
      exact Judgement.abs (ih J₁ J₂)
  | app _ _ ih₁ ih₂ => cases J₁ with | app J₃ J₄ => exact Judgement.app (ih₁ J₃ J₂) (ih₂ J₄ J₂)
  | «true» | «false» =>
    cases J₁
    constructor
  | ite _ _ _ ih₁ ih₂ ih₃ => cases J₁ with | ite J₃ J₄ J₅ =>
    exact Judgement.ite (ih₁ J₃ J₂) (ih₂ J₄ J₂) (ih₃ J₅ J₂)

theorem preservation {t t' : Term} {τ : Ty} : (∅ ⊢ t : τ) → (t ⟶ t') → ∅ ⊢ t' : τ := by
  generalize hΓ : (∅ : Context) = Γ
  intro J h
  induction J generalizing t' with subst hΓ
  | var | abs | «true» | «false» => cases h
  | app J₁ J₂ ih₁ ih₂ => cases h with
    | app_cont => cases J₁ with | abs J₁ => exact subst_preserves_typing J₁ J₂
    | app_cong_l h => exact Judgement.app (ih₁ rfl h) J₂
    | app_cong_r _ h => exact Judgement.app J₁ (ih₂ rfl h)
  | ite _ J₁ J₂ ih => cases h with
    | ite_cont_true => exact J₁
    | ite_cont_false => exact J₂
    | ite_cong h => exact Judgement.ite (ih rfl h) J₁ J₂

def Term.Stuck (t : Term) : Prop := ¬Value t ∧ ¬∃ t', t ⟶ t'

theorem soundness {t t' : Term} {τ : Ty} : (∅ ⊢ t : τ) → (t ⟶* t') → ¬t'.Stuck := by
  intro J h ⟨_, _⟩
  induction h using Multistep.head_induction_on with
  | refl => cases progress J <;> contradiction
  | head h' _ ih => exact ih (preservation J h')

theorem type_uniqueness {Γ : Context} {t : Term} {τ τ' : Ty} :
    (Γ ⊢ t : τ) → (Γ ⊢ t : τ') → τ = τ' := by
  intro J₁ J₂
  induction J₁ generalizing τ' with
  | var h₁ => cases J₂ with | var h₂ => rwa [h₁, Option.some_inj] at h₂
  | abs _ ih => cases J₂ with | abs J₂ =>
    congr
    exact ih J₂
  | app _ _ ih => cases J₂ with | app J₂ _ => injection ih J₂
  | «true» | «false» =>
    cases J₂
    rfl
  | ite _ _ _ _ _ ih => cases J₂ with | ite _ _ J₂ => exact ih J₂

end Stlc
