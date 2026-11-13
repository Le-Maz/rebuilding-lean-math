import ReMath.Order.Zorn

namespace Function

def Inverse {α β : Sort _} (g : β → α) (f : α → β) : Prop :=
  LeftInverse g f ∧ RightInverse g f

def Bijective {α β : Sort _} (f : α → β) : Prop :=
  Injective f ∧ Surjective f

theorem Bijective.inverse {α β} {f : α → β} (hf : Bijective f) : ∃ g, Function.Inverse g f := by
  classical
  if hα : Nonempty α then
    have ⟨g, hg⟩ := hf.left.leftInverse
    refine ⟨g, hg, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := hf.right y
    exact congrArg f (hg x)
  else
    let g (y : β) : α := hf.right y |>.choose
    have {P : Prop} : α → P := False.elim ∘ hα ∘ Nonempty.intro
    refine ⟨g, ?_, ?_⟩
    · exact fun x => this x
    · exact fun y => this (g y)

/-- A two-sided inverse of a function is itself bijective. -/
theorem Inverse.bijective {α β : Sort _} {f : α → β} {g : β → α}
    (h : Inverse g f) : Bijective g := by
  obtain ⟨hl, hr⟩ := h
  refine ⟨?_, ?_⟩
  · intro y₁ y₂ hy
    calc y₁
      _ = f (g y₁) := (hr y₁).symm
      _ = f (g y₂) := congrArg f hy
      _ = y₂ := hr y₂
  · intro x
    exact ⟨f x, hl x⟩

/-- Of any two types, one injects into the other. -/
theorem exists_injective_or {α β : Sort _} :
    (∃ f : α → β, Function.Injective f) ∨ (∃ g : β → α, Function.Injective g) := by
  classical
  let σ := {R : α → β → Prop //
    (∀ a b b', R a b → R a b' → b = b') ∧ (∀ a a' b, R a b → R a' b → a = a')}
  have bound : ∀ c : σ → Prop, (∀ x y, c x → c y → (∀ a b, x.1 a b → y.1 a b) ∨
      (∀ a b, y.1 a b → x.1 a b)) →
      ∃ ub : σ, ∀ x, c x → ∀ a b, x.1 a b → ub.1 a b := by
    intro c hc
    refine ⟨⟨fun a b => ∃ R : σ, c R ∧ R.1 a b, ?_, ?_⟩, fun R hR a b h => ⟨R, hR, h⟩⟩
    · rintro a b b' ⟨R, hR, h⟩ ⟨S, hS, h'⟩
      rcases hc R S hR hS with hRS | hSR
      · exact S.2.1 a b b' (hRS a b h) h'
      · exact R.2.1 a b b' h (hSR a b' h')
    · rintro a a' b ⟨R, hR, h⟩ ⟨S, hS, h'⟩
      rcases hc R S hR hS with hRS | hSR
      · exact S.2.2 a a' b (hRS a b h) h'
      · exact R.2.2 a a' b h (hSR a' b h')
  obtain ⟨m, hm⟩ := Zorn.exists_maximal (σ := σ)
    (fun R S => ∀ a b, R.1 a b → S.1 a b)
    (fun _ _ _ h => h)
    (fun _ _ _ h₁ h₂ a b h => h₂ a b (h₁ a b h))
    bound
  by_cases hA : ∀ a, ∃ b, m.1 a b
  · left
    refine ⟨fun a => (hA a).choose, fun a a' h => ?_⟩
    have h' : (hA a).choose = (hA a').choose := h
    have h2 : m.1 a' (hA a).choose := by
      rw [h']
      exact (hA a').choose_spec
    exact m.2.2 a a' _ (hA a).choose_spec h2
  · by_cases hB : ∀ b, ∃ a, m.1 a b
    · right
      refine ⟨fun b => (hB b).choose, fun b b' h => ?_⟩
      have h' : (hB b).choose = (hB b').choose := h
      have h2 : m.1 (hB b).choose b' := by
        rw [h']
        exact (hB b').choose_spec
      exact m.2.1 _ b b' (hB b).choose_spec h2
    · exfalso
      have hA' : ∃ a0, ∀ b, ¬ m.1 a0 b :=
        Classical.byContradiction fun hne =>
          hA fun a => Classical.byContradiction fun hnb =>
            hne ⟨a, fun b hb => hnb ⟨b, hb⟩⟩
      have hB' : ∃ b0, ∀ a, ¬ m.1 a b0 :=
        Classical.byContradiction fun hne =>
          hB fun b => Classical.byContradiction fun hna =>
            hne ⟨b, fun a ha => hna ⟨a, ha⟩⟩
      obtain ⟨a0, ha0⟩ := hA'
      obtain ⟨b0, hb0⟩ := hB'
      have hfun : ∀ a b b', (m.1 a b ∨ (a = a0 ∧ b = b0)) →
          (m.1 a b' ∨ (a = a0 ∧ b' = b0)) → b = b' := by
        rintro a b b' (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
        · exact m.2.1 a b b' h h'
        · subst h1'
          exact absurd h (ha0 b)
        · subst h1
          exact absurd h' (ha0 b')
        · rw [h2, h2']
      have hinj : ∀ a a' b, (m.1 a b ∨ (a = a0 ∧ b = b0)) →
          (m.1 a' b ∨ (a' = a0 ∧ b = b0)) → a = a' := by
        rintro a a' b (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
        · exact m.2.2 a a' b h h'
        · subst h2'
          exact absurd h (hb0 a)
        · subst h2
          exact absurd h' (hb0 a')
        · rw [h1, h1']
      have key := hm ⟨fun a b => m.1 a b ∨ (a = a0 ∧ b = b0), hfun, hinj⟩
        (fun a b h => Or.inl h)
      exact ha0 b0 (key a0 b0 (Or.inr ⟨rfl, rfl⟩))

end Function
