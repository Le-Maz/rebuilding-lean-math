import ReMath.Set.Multiset

/-- Finite sets, represented as duplicate-free multisets. -/
def Finset (α : Type u) := { S : Multiset α // S.Nodup }

namespace Finset

/-- Builds a finite set from a multiset together with a proof that it has no duplicates. -/
def mk {α} (A : Multiset α) (h : A.Nodup) : Finset α :=
  Subtype.mk A h

/-- `x` belongs to `A` when it belongs to the underlying multiset. -/
def Mem {α} (x : α) (A : Finset α) : Prop := x ∈ A.val

/-- A singleton list is duplicate-free. -/
private theorem nodup_singleton {α} (x : α) : [x].Nodup :=
  List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

instance {α} : EmptyCollection (Finset α) where
  emptyCollection := mk ∅ List.nodup_nil

instance {α} : Singleton α (Finset α) where
  singleton x := mk {x} (nodup_singleton x)

instance {α} [DecidableEq α] : Insert α (Finset α) where
  insert x A := mk ({x} ∪ A.val) <|
    Multiset.union_nodup (nodup_singleton x) A.property

instance {α} [DecidableEq α] : LawfulSingleton α (Finset α) where
  insert_empty_eq _ := rfl

instance {α} : Membership α (Finset α) := ⟨fun A x => Mem x A⟩

instance {α} : HasSubset (Finset α) where
  Subset a b := ∀ x, x ∈ a → x ∈ b

instance {α} : HasSSubset (Finset α) where
  SSubset a b := a ⊆ b ∧ ¬ b ⊆ a

/-- Cartesian product of two finite sets. -/
def prod {α β} (A : Finset α) (B : Finset β) : Finset (α × β) :=
  mk (A.val.prod B.val) <| by
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    induction A using Quotient.inductionOn with | _ a
    induction B using Quotient.inductionOn with | _ b
    change a.Nodup at hA
    change b.Nodup at hB
    change (a.flatMap <| b.map ∘ Prod.mk).Nodup
    induction a with
    | nil => exact List.nodup_nil
    | cons x l ih =>
      rw [List.nodup_cons] at hA
      change (b.map (Prod.mk x) ++ l.flatMap (b.map ∘ Prod.mk)).Nodup
      rw [List.nodup_append]
      refine ⟨?_, ih hA.right, ?_⟩
      · exact List.Pairwise.map (Prod.mk x) (fun y z h e => h (Prod.mk.inj e).right) hB
      · intro p hp₁ q hp₂ hpq
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp₁
        obtain ⟨z, hz, hzp⟩ := List.mem_flatMap.mp hp₂
        change q ∈ b.map (Prod.mk z) at hzp
        obtain ⟨w, _, hw⟩ := List.mem_map.mp hzp
        have hzx : z = x := (Prod.mk.inj (hw.trans hpq.symm)).left
        rw [hzx] at hz
        exact hA.left hz

/-- Disjoint union of two finite sets, tagging elements of `A` with `inl` and of `B` with `inr`. -/
def coprod {α β} (A : Finset α) (B : Finset β) : Finset (α ⊕ β) :=
  mk (A.val.coprod B.val) <| by
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    induction A using Quotient.inductionOn with | _ a =>
    induction B using Quotient.inductionOn with | _ b =>
    change (a.map Sum.inl ++ b.map Sum.inr).Nodup
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map Sum.inl (fun y z h e => h (Sum.inl.inj e)) hA
    · exact List.Pairwise.map Sum.inr (fun y z h e => h (Sum.inr.inj e)) hB
    · intro p hp q hq hpq
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hq
      cases hpq

/-- Set difference: the elements of `A` that are not in `B`. -/
def diff {α} [DecidableEq α] (A B : Finset α) : Finset α :=
  mk (A.val.diff B.val) <| by
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, _⟩ := B
    induction A using Quotient.inductionOn with | _ a =>
    induction B using Quotient.inductionOn with | _ b =>
    exact Multiset.listDiff_nodup b hA

/-- Set union: the elements that are in `A` or in `B`. -/
def union {α} [DecidableEq α] (A B : Finset α) : Finset α :=
  mk (A.val.union B.val) (Multiset.union_nodup A.property B.property)

/-- Set intersection: the elements that are in both `A` and `B`. -/
def inter {α} [DecidableEq α] (A B : Finset α) : Finset α :=
  mk (A.val.inter B.val) <| by
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    induction A using Quotient.inductionOn with | _ a =>
    induction B using Quotient.inductionOn with | _ b =>
    exact Multiset.listDiff_nodup _ hA

instance {α} [DecidableEq α] : Union (Finset α) := ⟨union⟩

instance {α} [DecidableEq α] : Inter (Finset α) := ⟨inter⟩

instance {α} [DecidableEq α] : SDiff (Finset α) := ⟨diff⟩

/-- Keeps the elements of the finite set satisfying `p`. -/
def filter {α} (p : α → Prop) [DecidablePred p] (A : Finset α) : Finset α :=
  mk (A.val.filter p) <| by
    obtain ⟨A, hA⟩ := A
    induction A using Quotient.inductionOn with | _ a =>
    change (a.filter fun x => decide (p x)).Nodup
    exact List.Pairwise.filter _ hA

/-- `Sep` takes an arbitrary predicate, so decidability is supplied classically. -/
noncomputable instance {α} : Sep α (Finset α) :=
  ⟨fun p A => open Classical in filter p A⟩

end Finset
