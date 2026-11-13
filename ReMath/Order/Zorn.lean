namespace ZornAux

variable {σ : Sort _}

/-- `c` is a chain for `le`: any two members are comparable. -/
def IsCh (le : σ → σ → Prop) (c : σ → Prop) : Prop :=
  ∀ x y, c x → c y → le x y ∨ le y x

/-- Inclusion of predicates. -/
def Sub (s t : σ → Prop) : Prop := ∀ x, s x → t x

theorem Sub.refl (s : σ → Prop) : Sub s s := fun _ h => h

theorem Sub.trans {s t u : σ → Prop} (h₁ : Sub s t) (h₂ : Sub t u) : Sub s u :=
  fun x hx => h₂ x (h₁ x hx)

theorem Sub.antisymm {s t : σ → Prop} (h₁ : Sub s t) (h₂ : Sub t s) : s = t :=
  funext fun x => propext ⟨h₁ x, h₂ x⟩

open Classical in
/-- Extends the chain `c` by a strictly larger chain when one exists, else returns `c`. -/
noncomputable def succCh (le : σ → σ → Prop) (c : σ → Prop) : σ → Prop :=
  if h : ∃ d, IsCh le d ∧ Sub c d ∧ ∃ x, d x ∧ ¬ c x then Classical.choose h else c

theorem succCh_of_pos {le : σ → σ → Prop} {c : σ → Prop}
    (h : ∃ d, IsCh le d ∧ Sub c d ∧ ∃ x, d x ∧ ¬ c x) :
    succCh le c = Classical.choose h := by
  simp only [succCh, h, ↓reduceDIte]

theorem succCh_of_neg {le : σ → σ → Prop} {c : σ → Prop}
    (h : ¬ ∃ d, IsCh le d ∧ Sub c d ∧ ∃ x, d x ∧ ¬ c x) :
    succCh le c = c := by
  simp only [succCh, h, ↓reduceDIte]

theorem sub_succCh (le : σ → σ → Prop) (c : σ → Prop) : Sub c (succCh le c) := by
  by_cases h : ∃ d, IsCh le d ∧ Sub c d ∧ ∃ x, d x ∧ ¬ c x
  · rw [succCh_of_pos h]
    exact (Classical.choose_spec h).2.1
  · rw [succCh_of_neg h]
    exact Sub.refl c

theorem isCh_succCh {le : σ → σ → Prop} {c : σ → Prop} (hc : IsCh le c) :
    IsCh le (succCh le c) := by
  by_cases h : ∃ d, IsCh le d ∧ Sub c d ∧ ∃ x, d x ∧ ¬ c x
  · rw [succCh_of_pos h]
    exact (Classical.choose_spec h).1
  · rw [succCh_of_neg h]
    exact hc

/-- A chain fixed by `succCh` has no strictly larger chain. -/
theorem sub_of_fixed {le : σ → σ → Prop} {c : σ → Prop} (heq : succCh le c = c)
    {d : σ → Prop} (hd : IsCh le d) (hcd : Sub c d) : Sub d c := by
  intro x hx
  refine Classical.byContradiction fun hxc => ?_
  have h : ∃ d, IsCh le d ∧ Sub c d ∧ ∃ x, d x ∧ ¬ c x := ⟨d, hd, hcd, x, hx, hxc⟩
  have hspec := Classical.choose_spec h
  rw [succCh_of_pos h] at heq
  obtain ⟨y, hy1, hy2⟩ := hspec.2.2
  rw [heq] at hy1
  exact hy2 hy1

/-- The smallest family of chains closed under `succCh` and unions. -/
inductive Tower (le : σ → σ → Prop) : (σ → Prop) → Prop
  | succ {c : σ → Prop} : Tower le c → Tower le (succCh le c)
  | union (A : (σ → Prop) → Prop) :
      (∀ a, A a → Tower le a) → Tower le (fun x => ∃ a, A a ∧ a x)

/-- `c` is comparable with every `succCh` step below it. -/
def Normal (le : σ → σ → Prop) (c : σ → Prop) : Prop :=
  ∀ d, Tower le d → Sub d c → d = c ∨ Sub (succCh le d) c

theorem normal_cmp {le : σ → σ → Prop} {c : σ → Prop} (hn : Normal le c)
    {d : σ → Prop} (hd : Tower le d) : Sub d c ∨ Sub (succCh le c) d := by
  induction hd with
  | @succ d' hd' ih =>
    rcases ih with h | h
    · rcases hn d' hd' h with heq | h'
      · exact Or.inr (heq ▸ Sub.refl _)
      · exact Or.inl h'
    · exact Or.inr (h.trans (sub_succCh le d'))
  | union A hA ih =>
    by_cases h : ∀ a, A a → Sub a c
    · left
      intro x hx
      obtain ⟨a, ha, hxa⟩ := hx
      exact h a ha x hxa
    · right
      obtain ⟨a, ha, hna⟩ : ∃ a, A a ∧ ¬ Sub a c := by
        refine Classical.byContradiction fun hcon => h ?_
        intro a ha
        refine Classical.byContradiction fun hna => hcon ⟨a, ha, hna⟩
      rcases ih a ha with h1 | h1
      · exact (hna h1).elim
      · intro x hx
        exact ⟨a, ha, h1 x hx⟩

theorem tower_normal {le : σ → σ → Prop} {c : σ → Prop} (hc : Tower le c) :
    Normal le c := by
  induction hc with
  | @succ c' hc' ih =>
    intro d hd hdc
    rcases normal_cmp ih hd with h | h
    · rcases ih d hd h with heq | h'
      · right
        rw [heq]
        exact Sub.refl _
      · right
        exact h'.trans (sub_succCh le c')
    · left
      exact Sub.antisymm hdc h
  | union A hA ih =>
    intro d hd hdU
    by_cases h : ∃ a, A a ∧ Sub (succCh le d) a
    · right
      obtain ⟨a, ha, h⟩ := h
      intro x hx
      exact ⟨a, ha, h x hx⟩
    · left
      have key : ∀ a, A a → Sub a d := by
        intro a ha
        rcases normal_cmp (ih a ha) hd with h1 | h1
        · rcases ih a ha d hd h1 with heq | h2
          · rw [heq]
            exact Sub.refl _
          · exact (h ⟨a, ha, h2⟩).elim
        · exact (sub_succCh le a).trans h1
      refine Sub.antisymm hdU ?_
      intro x hx
      obtain ⟨a, ha, hxa⟩ := hx
      exact key a ha x hxa

theorem tower_total {le : σ → σ → Prop} {c d : σ → Prop}
    (hc : Tower le c) (hd : Tower le d) : Sub c d ∨ Sub d c := by
  rcases normal_cmp (tower_normal hc) hd with h | h
  · exact Or.inr h
  · exact Or.inl ((sub_succCh le c).trans h)

theorem tower_isCh {le : σ → σ → Prop} {c : σ → Prop} (hc : Tower le c) :
    IsCh le c := by
  induction hc with
  | succ hc' ih => exact isCh_succCh ih
  | union A hA ih =>
    intro x y hx hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    rcases tower_total (hA a ha) (hA b hb) with h | h
    · exact ih b hb x y (h x hxa) hyb
    · exact ih a ha x y hxa (h y hyb)

/-- There is a chain that `succCh` leaves unchanged. -/
theorem exists_fixed (le : σ → σ → Prop) :
    ∃ U : σ → Prop, IsCh le U ∧ succCh le U = U := by
  have hU : Tower le (fun x => ∃ a, Tower le a ∧ a x) :=
    Tower.union (fun a => Tower le a) (fun a h => h)
  refine ⟨_, tower_isCh hU, ?_⟩
  refine Sub.antisymm ?_ (sub_succCh le _)
  intro x hx
  exact ⟨_, Tower.succ hU, hx⟩

end ZornAux

/-- Zorn's lemma for preorders: if every chain has an upper bound, there is a maximal element. -/
theorem Zorn.exists_maximal {σ : Sort _} (le : σ → σ → Prop)
    (refl : ∀ x, le x x) (trans : ∀ x y z, le x y → le y z → le x z)
    (chain_bound : ∀ c : σ → Prop, (∀ x y, c x → c y → le x y ∨ le y x) →
      ∃ ub, ∀ x, c x → le x ub) :
    ∃ m, ∀ x, le m x → le x m := by
  obtain ⟨U, hUc, hUf⟩ := ZornAux.exists_fixed le
  obtain ⟨ub, hub⟩ := chain_bound U hUc
  refine ⟨ub, fun x hx => ?_⟩
  have hd : ZornAux.IsCh le (fun y => U y ∨ y = x) := by
    intro y z hy hz
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact hUc y z hy hz
    · left
      rw [hz]
      exact trans _ _ _ (hub y hy) hx
    · right
      rw [hy]
      exact trans _ _ _ (hub z hz) hx
    · left
      rw [hy, hz]
      exact refl x
  have hsub : ZornAux.Sub (fun y => U y ∨ y = x) U :=
    ZornAux.sub_of_fixed hUf hd (fun y hy => Or.inl hy)
  exact hub x (hsub x (Or.inr rfl))
