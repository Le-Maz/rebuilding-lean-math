import ReMath.Function.Basic

/-- Two types are equinumerous when there is a bijection between them. -/
structure Equinum (α β : Sort _) : Prop where
  exists_bij : ∃ f : α → β, Function.Bijective f

namespace Equinum

/-- Every type is equinumerous to itself, via the identity. -/
@[refl]
theorem refl (α : Sort _) : Equinum α α := by
  refine ⟨fun x => x, ?_, ?_⟩
  · intro x y hxy
    exact hxy
  · intro y
    exact ⟨y, rfl⟩

/-- Equinumerosity is symmetric: invert the bijection. -/
@[symm]
theorem symm {α β : Sort _}
    (h : Equinum α β) : Equinum β α := by
  have ⟨f, hf⟩ := h.exists_bij
  have ⟨g, hg⟩ := hf.inverse
  exact ⟨g, hg.bijective⟩

/-- Equinumerosity is transitive: compose the bijections. -/
theorem trans {α β γ : Sort _}
    (h₁ : Equinum α β) (h₂ : Equinum β γ) : Equinum α γ := by
  have ⟨f, hf⟩ := h₁.exists_bij
  have ⟨g, hg⟩ := h₂.exists_bij
  exact ⟨g ∘ f, hg.left.comp hf.left, hg.right.comp hf.right⟩

/-- Enables `calc` chains over `Equinum`. -/
instance instTrans : Trans Equinum Equinum Equinum := ⟨trans⟩

/-- Equinumerosity is an equivalence relation on each universe. -/
theorem iseqv.{u} : Equivalence Equinum.{u, u} where
  refl := refl
  symm := symm
  trans := trans

/-- The setoid on types whose relation is equinumerosity. -/
instance setoid.{u} : Setoid (Sort u) := ⟨Equinum, iseqv⟩

/-- Elements of `α` reachable from those outside the range of `g` by iterating `g ∘ f`. -/
inductive Bad {α β : Sort _} (f : α → β) (g : β → α) : α → Prop
  | base (a : α) : (∀ b, g b ≠ a) → Bad f g a
  | step (a' a : α) : Bad f g a' → g (f a') = a → Bad f g a

/-- Schröder-Bernstein: mutually injectable types are equinumerous. -/
theorem of_injective {α β : Sort _} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) : Equinum α β := by
  classical
  have range_of : ∀ a, ¬ Bad f g a → ∃ b, g b = a := fun a hB =>
    Classical.byContradiction fun hne =>
      hB (.base a fun b hb => hne ⟨b, hb⟩)
  refine ⟨fun a => if hB : Bad f g a then f a else Classical.choose (range_of a hB), ?_, ?_⟩
  · intro a₁ a₂ h
    by_cases h₁ : Bad f g a₁ <;> by_cases h₂ : Bad f g a₂
    · simp only [dif_pos h₁, dif_pos h₂] at h
      exact hf h
    · simp only [dif_pos h₁, dif_neg h₂] at h
      have e := Classical.choose_spec (range_of a₂ h₂)
      rw [← h] at e
      exact absurd (Bad.step a₁ a₂ h₁ e) h₂
    · simp only [dif_neg h₁, dif_pos h₂] at h
      have e := Classical.choose_spec (range_of a₁ h₁)
      rw [h] at e
      exact absurd (Bad.step a₂ a₁ h₂ e) h₁
    · simp only [dif_neg h₁, dif_neg h₂] at h
      calc a₁ = g (Classical.choose (range_of a₁ h₁)) :=
            (Classical.choose_spec (range_of a₁ h₁)).symm
        _ = g (Classical.choose (range_of a₂ h₂)) := congrArg g h
        _ = a₂ := Classical.choose_spec (range_of a₂ h₂)
  · intro b
    by_cases hex : ∃ a, Bad f g a ∧ f a = b
    · obtain ⟨a, ha, rfl⟩ := hex
      exact ⟨a, dif_pos ha⟩
    · have hn : ¬ Bad f g (g b) := fun hB => by
        cases hB with
        | base _ h => exact h b rfl
        | step a' _ ha' heq => exact hex ⟨a', ha', hg heq⟩
      exact ⟨g b, (dif_neg hn).trans (hg (Classical.choose_spec (range_of (g b) hn)))⟩

/-- Two maps that are mutual two-sided inverses witness an equinumerosity. -/
theorem of_lr_inverses {α β : Sort _} (f : α → β) (g : β → α)
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) : Equinum α β :=
  ⟨f,
    fun a₁ a₂ h => (hgf a₁).symm.trans ((congrArg g h).trans (hgf a₂)),
    fun b => ⟨g b, hfg b⟩⟩

/-- Any two empty types are equinumerous. -/
theorem of_isEmpty {α β : Sort _} (hα : α → False) (hβ : β → False) : Equinum α β :=
  ⟨fun a => (hα a).elim, fun a => (hα a).elim, fun b => (hβ b).elim⟩

/-- `PEmpty` is equinumerous to `Fin 0`, as both are empty. -/
theorem pempty_to_fin : Equinum PEmpty (Fin 0) :=
  of_isEmpty (fun e => e.elim) (fun y => Nat.not_lt_zero _ y.isLt)

/-- `PUnit` is equinumerous to `Fin 1`, as both have exactly one element. -/
theorem punit_to_fin : Equinum PUnit (Fin 1) :=
  of_lr_inverses (fun _ => 0) (fun _ => PUnit.unit)
    (fun _ => rfl) (fun _ => Subsingleton.elim _ _)

/-- `Prop` is equinumerous to `Bool`, via `propext` and classical decidability. -/
theorem prop_to_bool : Equinum Prop Bool := by
  classical
  refine ⟨fun p => decide p, ?_, ?_⟩
  · intro p q h
    exact propext (decide_eq_decide.mp h)
  · intro b
    cases b
    · exact ⟨False, decide_false _⟩
    · exact ⟨True, decide_true _⟩

/-- `Bool` is equinumerous to `Fin 2`, sending `false` to `0` and `true` to `1`. -/
theorem bool_to_fin : Equinum Bool (Fin 2) :=
  of_lr_inverses (fun b => cond b 1 0) (fun y => decide (y = 1))
    (fun b => by cases b <;> decide)
    (fun y => by
      match y with
      | 0 => decide
      | 1 => decide)

/-- `Prop` is equinumerous to `Fin 2`, by composing `Prop ≃ Bool` and `Bool ≃ Fin 2`. -/
theorem prop_to_fin : Equinum Prop (Fin 2) := trans prop_to_bool bool_to_fin

end Equinum
