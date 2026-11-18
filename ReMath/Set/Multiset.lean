def Multiset (α : Type u) := Quotient (List.isSetoid α)

namespace Multiset

def mk {α} (a : List α) : Multiset α :=
  Quotient.mk (List.isSetoid α) a

def Nodup {α} (A : Multiset α) : Prop :=
  A.liftOn List.Nodup <| by
    intro a b h
    refine iff_iff_eq.mp ?_
    exact List.Perm.nodup_iff h

def Mem {α} (x : α) (A : Multiset α) : Prop :=
  A.liftOn (List.Mem x) <| by
    intro a b h
    refine iff_iff_eq.mp ?_
    exact List.Perm.mem_iff h

instance {α} : EmptyCollection (Multiset α) where
  emptyCollection := mk []

instance {α} : Singleton α (Multiset α) where
  singleton x := mk [x]

instance {α} : Insert α (Multiset α) where
  insert x A := A.liftOn (fun a => mk <| x::a) <| by
    intro a b h
    apply Quotient.sound
    exact List.perm_cons x |>.mpr h

instance {α} : LawfulSingleton α (Multiset α) where
  insert_empty_eq _ := rfl

instance {α} : Membership α (Multiset α) := ⟨fun A x => Mem x A⟩

/-- Sub-multiset relation: `A` is contained in `B` counting multiplicities. -/
def Subset {α} (A B : Multiset α) : Prop :=
  A.liftOn₂ B (fun a b => ∃ c, (a ++ c).Perm b) <| by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    refine iff_iff_eq.mp ⟨?_, ?_⟩
    · rintro ⟨c, h⟩
      exact ⟨c, (h₁.symm.append_right c).trans (h.trans h₂)⟩
    · rintro ⟨c, h⟩
      exact ⟨c, (h₁.append_right c).trans (h.trans h₂.symm)⟩

instance {α} : HasSubset (Multiset α) := ⟨Multiset.Subset⟩

/-- A sub-multiset has only members of the larger multiset. -/
theorem mem_of_subset {α} {A B : Multiset α} (h : A ⊆ B) {x : α}
    (hx : x ∈ A) : x ∈ B := by
  induction A using Quotient.inductionOn with | _ a =>
  induction B using Quotient.inductionOn with | _ b =>
  obtain ⟨c, hc⟩ := h
  exact hc.mem_iff.mp (List.mem_append_left c hx)

instance {α} : HasSSubset (Multiset α) where
  SSubset a b := a ⊆ b ∧ ¬ b ⊆ a

/-- Cartesian product of two lists, pairing each element of `a` with every element of `b`. -/
def listProd {α β} (a : List α) (b : List β) : List (α × β) :=
  a.flatMap fun x => b.map (Prod.mk x)

/-- Permuting the outer list of a `flatMap` yields a permutation of the result. -/
theorem flatMap_perm_left {α γ} (F : α → List γ) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : (l₁.flatMap F).Perm (l₂.flatMap F) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih =>
    simp only [List.flatMap_cons]
    exact ih.append_left _
  | swap x y l =>
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem listProd_perm_left {α β} (b : List β) {a₁ a₂ : List α}
    (h : a₁.Perm a₂) : (listProd a₁ b).Perm (listProd a₂ b) :=
  flatMap_perm_left _ h

theorem listProd_perm_right {α β} (a : List α) {b₁ b₂ : List β}
    (h : b₁.Perm b₂) : (listProd a b₁).Perm (listProd a b₂) := by
  induction a with
  | nil => exact .nil
  | cons x a ih =>
    simp only [listProd, List.flatMap_cons]
    exact (h.map _).append ih

theorem listProd_perm {α β} {a₁ a₂ : List α} {b₁ b₂ : List β}
    (ha : a₁.Perm a₂) (hb : b₁.Perm b₂) :
    (listProd a₁ b₁).Perm (listProd a₂ b₂) :=
  (listProd_perm_left b₁ ha).trans (listProd_perm_right a₂ hb)

def prod {α β} (A : Multiset α) (B : Multiset β) : Multiset (α × β) :=
  A.liftOn₂ B (fun a b => mk <| listProd a b) <| by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    exact Quotient.sound (listProd_perm h₁ h₂)

def coprod {α β} (A : Multiset α) (B : Multiset β) : Multiset (α ⊕ β) :=
  A.liftOn₂ B (
    fun a b =>
      mk <| a.map Sum.inl ++ b.map Sum.inr
  ) <| by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    apply Quotient.sound
    apply List.Perm.append
    <;> apply List.Perm.map
    <;> assumption

/-- Removes one occurrence of each element of `t` from `l`. -/
def listDiff {α} [DecidableEq α] : List α → List α → List α
  | l, [] => l
  | l, a :: t => listDiff (l.erase a) t

theorem listDiff_perm_left {α} [DecidableEq α] (t : List α) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : (listDiff l₁ t).Perm (listDiff l₂ t) := by
  induction t generalizing l₁ l₂ with
  | nil => exact h
  | cons a t ih => exact ih (h.erase a)

theorem listDiff_perm_right {α} [DecidableEq α] (l : List α) {t₁ t₂ : List α}
    (h : t₁.Perm t₂) : (listDiff l t₁).Perm (listDiff l t₂) := by
  induction h generalizing l with
  | nil => exact .refl _
  | cons x _ ih => exact ih _
  | swap x y t =>
    simp only [listDiff]
    rw [List.erase_comm] <;> exact .refl _
  | trans _ _ ih₁ ih₂ => exact (ih₁ l).trans (ih₂ l)

theorem listDiff_perm {α} [DecidableEq α] {l₁ l₂ t₁ t₂ : List α}
    (hl : l₁.Perm l₂) (ht : t₁.Perm t₂) :
    (listDiff l₁ t₁).Perm (listDiff l₂ t₂) :=
  (listDiff_perm_left t₁ hl).trans (listDiff_perm_right l₂ ht)

/-- Removing elements from a duplicate-free list leaves a duplicate-free list. -/
theorem listDiff_nodup {α} [DecidableEq α] (t : List α) {l : List α}
    (h : l.Nodup) : (listDiff l t).Nodup := by
  induction t generalizing l with
  | nil => exact h
  | cons b t ih =>
    refine ih ?_
    rw [List.nodup_iff_count] at h ⊢
    intro x
    rw [l.count_erase (a := x) (b := b)]
    exact Nat.le_trans (Nat.sub_le _ _) (h x)

/-- The multiplicity of `x` in `listDiff l t` is the truncated difference of multiplicities. -/
theorem count_listDiff {α} [DecidableEq α] (x : α) (t : List α) {l : List α} :
    (listDiff l t).count x = l.count x - t.count x := by
  induction t generalizing l with
  | nil => simp [listDiff]
  | cons b t ih =>
    rw [listDiff, ih, List.count_erase, List.count_cons]
    split <;> omega

/--
Multiset difference: the multiplicity of `x` is the truncated subtraction `count x A - count x B`.
-/
def diff {α} [DecidableEq α] (A B : Multiset α) : Multiset α :=
  A.liftOn₂ B (fun a b => mk <| listDiff a b) <| by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    exact Quotient.sound (listDiff_perm h₁ h₂)

/-- Multiset union: the multiplicity of `x` is the maximum of its multiplicities in `A` and `B`. -/
def union {α} [DecidableEq α] (A B : Multiset α) : Multiset α :=
  A.liftOn₂ B (fun a b => mk <| a ++ listDiff b a) <| by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    exact Quotient.sound (h₁.append (listDiff_perm h₂ h₁))

/-- The union of two duplicate-free multisets is duplicate-free. -/
theorem union_nodup {α} [DecidableEq α] {A B : Multiset α}
    (hA : A.Nodup) (hB : B.Nodup) : (A.union B).Nodup := by
  induction A using Quotient.inductionOn with | _ a =>
  induction B using Quotient.inductionOn with | _ b =>
  change (a ++ Multiset.listDiff b a).Nodup
  rw [List.nodup_append]
  refine ⟨hA, Multiset.listDiff_nodup a hB, ?_⟩
  intro p hp q hq hpq
  subst hpq
  have h2 : 0 < List.count p (Multiset.listDiff b a) :=
    List.count_pos_iff.mpr hq
  rw [Multiset.count_listDiff, Nat.sub_pos_iff_lt] at h2
  exact Nat.lt_irrefl 1 <| calc
    1 ≤ List.count p a := List.count_pos_iff.mpr hp
    _ < List.count p b := h2
    _ ≤ 1 := List.nodup_iff_count.mp hB p

/-- Multiset intersection: the multiplicity of `x` is the minimum of its multiplicities in `A` and `B`. -/
def inter {α} [DecidableEq α] (A B : Multiset α) : Multiset α :=
  A.liftOn₂ B (fun a b => mk <| listDiff a (listDiff a b)) <| by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    exact Quotient.sound (listDiff_perm h₁ (listDiff_perm h₁ h₂))

instance {α} [DecidableEq α] : Union (Multiset α) := ⟨union⟩

instance {α} [DecidableEq α] : Inter (Multiset α) := ⟨inter⟩

instance {α} [DecidableEq α] : SDiff (Multiset α) := ⟨diff⟩

/-- Keeps the elements of the multiset satisfying `p`, preserving multiplicities. -/
def filter {α} (p : α → Prop) [DecidablePred p] (A : Multiset α) : Multiset α :=
  A.liftOn (fun a => mk <| a.filter fun x => decide (p x)) <| by
    intro a b h
    exact Quotient.sound (List.Perm.filter _ h)

/-- `Sep` takes an arbitrary predicate, so decidability is supplied classically. -/
noncomputable instance {α} : Sep α (Multiset α) :=
  ⟨fun p A => open Classical in filter p A⟩

/-- Applies `f` to every element, preserving multiplicities. -/
def map {α β} (f : α → β) (A : Multiset α) : Multiset β :=
  A.liftOn (fun a => mk <| a.map f) <| by
    intro a b h
    exact Quotient.sound (h.map f)

/-- Removes repeated elements from a list, keeping the last occurrence of each. -/
def listDedup {α} [DecidableEq α] : List α → List α
  | [] => []
  | x :: t => if x ∈ t then listDedup t else x :: listDedup t

/-- `listDedup` keeps exactly the elements of the original list. -/
theorem mem_listDedup {α} [DecidableEq α] (x : α) (l : List α) :
    x ∈ listDedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [listDedup]
  | cons y t ih =>
    by_cases hy : y ∈ t
    · rw [listDedup, if_pos hy, ih]
      constructor
      · exact List.mem_cons_of_mem y
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact hy
        · exact h
    · rw [listDedup, if_neg hy, List.mem_cons, List.mem_cons, ih]

/-- `listDedup` produces a duplicate-free list. -/
theorem nodup_listDedup {α} [DecidableEq α] (l : List α) : (listDedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons y t ih =>
    by_cases hy : y ∈ t
    · rw [listDedup, if_pos hy]
      exact ih
    · rw [listDedup, if_neg hy]
      exact List.nodup_cons.mpr ⟨fun h => hy ((mem_listDedup y t).mp h), ih⟩

/-- Duplicate-free lists with the same members are permutations of each other. -/
theorem perm_of_nodup_of_mem_iff {α} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro x
  have c₁ := List.nodup_iff_count.mp h₁ x
  have c₂ := List.nodup_iff_count.mp h₂ x
  by_cases hx : x ∈ l₁
  · have p₁ := List.count_pos_iff.mpr hx
    have p₂ := List.count_pos_iff.mpr ((h x).mp hx)
    omega
  · have hx₂ : x ∉ l₂ := fun h' => hx ((h x).mpr h')
    rw [List.count_eq_zero.mpr hx, List.count_eq_zero.mpr hx₂]

/-- Removes duplicates, leaving every element with multiplicity one. -/
def dedup {α} [DecidableEq α] (A : Multiset α) : Multiset α :=
  A.liftOn (fun a => mk <| listDedup a) <| by
    intro a b h
    apply Quotient.sound
    refine perm_of_nodup_of_mem_iff (nodup_listDedup a) (nodup_listDedup b) ?_
    intro x
    rw [mem_listDedup, mem_listDedup]
    exact h.mem_iff

/-- The result of `dedup` is duplicate-free. -/
theorem nodup_dedup {α} [DecidableEq α] (A : Multiset α) : A.dedup.Nodup := by
  induction A using Quotient.inductionOn with | _ a =>
  exact nodup_listDedup a

def toSortedList {α} [LE α] [DecidableLE α] [Std.IsLinearOrder α] (A : Multiset α) : List α :=
  A.liftOn List.mergeSort <| by
    intro a b h
    have hle : ∀ l : List α, (List.mergeSort l).Pairwise (· ≤ ·) := fun l => by
      have := List.pairwise_mergeSort (l := l) (le := fun x y => decide (x ≤ y))
        (by simpa using fun x y z => (Std.le_trans : x ≤ y → y ≤ z → x ≤ z))
        (by simpa using fun x y => (Std.le_total : x ≤ y ∨ y ≤ x))
      simpa using this
    exact List.Perm.eq_of_pairwise
      (fun x y _ _ hxy hyx => Std.le_antisymm hxy hyx)
      (hle a) (hle b)
      ((List.mergeSort_perm a _).trans (h.trans (List.mergeSort_perm b _).symm))

/-- Applies `g` to every element, keeping only the `some` results. -/
def filterMap {α β} (g : α → Option β) (A : Multiset α) : Multiset β :=
  A.liftOn (fun a => mk <| a.filterMap g) <| by
    intro a b h
    exact Quotient.sound (h.filterMap g)

/-- `filterMap` with a function that never sends two inputs to the same output keeps a list duplicate-free. -/
theorem nodup_filterMap {α β} (g : α → Option β)
    (hg : ∀ y z x, g y = some x → g z = some x → y = z) :
    ∀ l : List α, l.Nodup → (l.filterMap g).Nodup
  | [], _ => List.nodup_nil
  | y :: t, h => by
    rw [List.nodup_cons] at h
    cases hy : g y with
    | none =>
      rw [List.filterMap_cons_none hy]
      exact nodup_filterMap g hg t h.2
    | some x =>
      rw [List.filterMap_cons_some hy, List.nodup_cons]
      refine ⟨?_, nodup_filterMap g hg t h.2⟩
      intro hx
      obtain ⟨z, hz, hgz⟩ := List.mem_filterMap.mp hx
      exact h.1 (by rw [hg y z x hy hgz]; exact hz)

instance {α} [Repr α] [LE α] [DecidableLE α] [Std.IsLinearOrder α] : Repr (Multiset α) where
  reprPrec A _ :=
    let items := (toSortedList A).map repr
    Std.Format.bracket "{" (Std.Format.joinSep items ("," ++ Std.Format.line)) "}"

/-- Fallback for types without an order: elements are sorted by their rendered text. -/
instance (priority := low) {α} [Repr α] : Repr (Multiset α) where
  reprPrec A _ :=
    let items := toSortedList (A.map fun x => toString (repr x))
    Std.Format.bracket "{" (Std.Format.joinSep (items.map Std.Format.text) ("," ++ Std.Format.line)) "}"

end Multiset
