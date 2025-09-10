import Stlc.Step
import Stlc.Typing

namespace Stlc

open Syntax

theorem progress {t : Term} {τ : Ty} : (⊢ t : τ) → Value t ∨ ∃ t', t ⟶ t' := by
  set Γ : Context := ∅ with hΓ
  clear_value Γ
  intro h
  induction h with subst hΓ
  | var h => cases h
  | abs | «true» | «false» =>
    left
    constructor
  | @app _ _ _ t₁ t₂ ht₁ _ iht₁ iht₂ =>
    simp_rw [forall_const] at iht₁ iht₂
    right
    rcases iht₁ with iht₁ | ⟨t₁', iht₁⟩
    · rcases iht₂ with iht₂ | ⟨t₂', iht₂⟩
      · cases ht₁ with
        | var | app | ite => cases iht₁
        | @abs _ x _ _ t₁ =>
          use subst x t₂ t₁
          exact Step.app_cont iht₂
      · use t₁.app t₂'
        exact Step.app_cong_r iht₁ iht₂
    · use t₁'.app t₂
      exact Step.app_cong_l iht₁
  | @ite _ _ t₁ t₂ t₃ ht₁ _ _ iht₁ =>
    simp_rw [forall_const] at iht₁
    right
    rcases iht₁ with iht₁ | ⟨t₁', iht₁⟩
    · cases ht₁ with
      | var | app | ite => cases iht₁
      | «true» =>
        use t₂
        exact Step.ite_cont_true
      | «false» =>
        use t₃
        exact Step.ite_cont_false
    · use t₁'.ite t₂ t₃
      exact Step.ite_cong iht₁

theorem weakening {Γ Γ' : Context} {t : Term} {τ : Ty} : Γ ⊆ Γ' → (Γ ⊢ t : τ) → Γ' ⊢ t : τ := by
  intro hΓ h
  induction h generalizing Γ' with
  | var h => exact Judgement.var (hΓ h)
  | abs _ ih => exact Judgement.abs (ih (Context.includedIn_update hΓ))
  | app _ _ ih₁ ih₂ => exact Judgement.app (ih₁ hΓ) (ih₂ hΓ)
  | «true» | «false» => constructor
  | ite _ _ _ ih₁ ih₂ ih₃ => exact Judgement.ite (ih₁ hΓ) (ih₂ hΓ) (ih₃ hΓ)

theorem subst_preserves_typing {Γ x τ₁ t₁ t₂ τ₂} :
    (x ↦ τ₂; Γ ⊢ t₁ : τ₁) → (⊢ t₂ : τ₂) → Γ ⊢ [x := t₂] t₁ : τ₁ := by
  simp_rw [Context.update]
  intro h₁ h₂
  induction t₁ generalizing Γ τ₁ τ₂ with
  | var y => cases h₁ with | var h₁ =>
    by_cases hxy : x = y
    · subst hxy
      rw [Function.update_self, Option.some.injEq] at h₁
      rw [←h₁, subst, if_pos rfl]
      exact weakening Γ.includedIn_empty h₂
    · rw [Function.update_of_ne (Ne.symm hxy)] at h₁
      simp only [subst, hxy]
      exact Judgement.var h₁
  | abs y _ _ ih => cases h₁ with | abs h₁ =>
    by_cases hxy : x = y
    · subst hxy
      rw [Context.update, Function.update_idem] at h₁
      rw [subst, if_pos rfl]
      exact Judgement.abs h₁
    · simp only [subst, hxy]
      apply Judgement.abs
      rw [Context.update]
      apply ih _ h₂
      rwa [Function.update_comm (Ne.symm hxy)]
  | app _ _ ih₁ ih₂ => cases h₁ with | app h₃ h₄ =>
    exact Judgement.app (ih₁ h₃ h₂) (ih₂ h₄ h₂)
  | «true» | «false» =>
    cases h₁
    constructor
  | ite _ _ _ ih₁ ih₂ ih₃ => cases h₁ with | ite h₃ h₄ h₅ =>
    exact Judgement.ite (ih₁ h₃ h₂) (ih₂ h₄ h₂) (ih₃ h₅ h₂)

theorem preservation {t t' : Term} {τ : Ty} : (⊢ t : τ) → (t ⟶ t') → ⊢ t' : τ := by
  set Γ : Context := ∅ with hΓ
  clear_value Γ
  intro h₁ h₂
  induction h₁ generalizing t' with subst hΓ
  | var | abs | «true» | «false» => cases h₂
  | app h₃ h₄ ih₁ ih₂ =>
    simp_rw [forall_const] at ih₁ ih₂
    cases h₂ with
    | app_cont => cases h₃ with | abs h₃ =>
      exact subst_preserves_typing h₃ h₄
    | app_cong_l h₅ => exact Judgement.app (ih₁ h₅) h₄
    | app_cong_r _ h₅ => exact Judgement.app h₃ (ih₂ h₅)
  | ite _ h₃ h₄ ih₁ =>
    simp_rw [forall_const] at ih₁
    cases h₂ with
    | ite_cont_true => exact h₃
    | ite_cont_false => exact h₄
    | ite_cong h₂ => exact Judgement.ite (ih₁ h₂) h₃ h₄

def Term.Stuck (t : Term) : Prop := ¬Value t ∧ ¬∃ t', t ⟶ t'

theorem soundness {t t' : Term} {τ : Ty} : (⊢ t : τ) → (t ⟶* t') → ¬t'.Stuck := by
  intro h₁ h₂ ⟨_, _⟩
  induction h₂ using Relation.ReflTransGen.head_induction_on with
  | refl => cases progress h₁ <;> contradiction
  | head h₃ _ ih => exact ih (preservation h₁ h₃)

theorem type_uniqueness {Γ : Context} {t : Term} {τ τ' : Ty} :
    (Γ ⊢ t : τ) → (Γ ⊢ t : τ') → τ = τ' := by
  intro h₁ h₂
  induction h₁ generalizing τ' with
  | var h₃ => cases h₂ with | var h₄ => rwa [h₃, Option.some_inj] at h₄
  | abs _ ih => cases h₂ with | abs h₃ =>
    rw [Ty.arrow.injEq, propext (and_iff_left (ih h₃))]
  | app _ _ ih => cases h₂ with | app h₃ _ => injection ih h₃
  | «true» | «false» =>
    cases h₂
    rfl
  | ite _ _ _ _ _ ih => cases h₂ with | ite _ _ h₃ => exact ih h₃

end Stlc
