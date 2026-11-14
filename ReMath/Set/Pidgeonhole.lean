import ReMath.Function.Basic
import ReMath.Set.Equinum
import ReMath.Set.Subnum

namespace Pigeonhole

/-- Swaps the values `a` and `b` and fixes every other natural number. -/
private def swapNat (a b x : Nat) : Nat :=
  if x = a then b else if x = b then a else x

private theorem swapNat_self (a b : Nat) : swapNat a b a = b := by
  simp [swapNat]

private theorem swapNat_inj (a b x y : Nat)
    (h : swapNat a b x = swapNat a b y) : x = y := by
  simp only [swapNat] at h
  grind only

private theorem swapNat_lt (a b x bound : Nat)
    (ha : a < bound) (hb : b < bound) (hx : x < bound) :
    swapNat a b x < bound := by
  simp only [swapNat]
  grind only

/-- Pigeonhole on bounded naturals: an injection of `[0, n)` into `[0, m)` forces `n ≤ m`. -/
private theorem le_of_inj_nat : ∀ (n m : Nat) (f : Nat → Nat),
    (∀ i, i < n → f i < m) →
    (∀ i j, i < n → j < n → f i = f j → i = j) → n ≤ m := by
  intro n
  induction n with
  | zero =>
    intro m f _ _
    exact Nat.zero_le _
  | succ n ih =>
    intro m f hlt hinj
    have hfn : f n < m := hlt n (Nat.lt_succ_self n)
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hlast : swapNat (f n) m' (f n) = m' := swapNat_self _ _
    have hle : n ≤ m' := by
      refine ih m' (fun i => swapNat (f n) m' (f i)) ?_ ?_
      · intro i hi
        have hlt' : swapNat (f n) m' (f i) < m' + 1 :=
          swapNat_lt _ _ _ _ hfn (Nat.lt_succ_self m')
            (hlt i (Nat.lt_succ_of_lt hi))
        have hne : swapNat (f n) m' (f i) ≠ m' := by
          intro heq
          have h1 : f i = f n := swapNat_inj (f n) m' _ _ (heq.trans hlast.symm)
          have h2 := hinj i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n) h1
          omega
        omega
      · intro i j hi hj h
        exact hinj i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj)
          (swapNat_inj (f n) m' _ _ h)
    omega

/-- An injection `Fin n → Fin m` forces `n ≤ m`. -/
theorem le_of_injective_fin {n m : Nat} {f : Fin n → Fin m}
    (hf : Function.Injective f) : n ≤ m := by
  refine le_of_inj_nat n m (fun i => if h : i < n then (f ⟨i, h⟩).val else 0) ?_ ?_
  · intro i hi
    simp only [dif_pos hi]
    exact (f ⟨i, hi⟩).isLt
  · intro i j hi hj h
    simp only [dif_pos hi, dif_pos hj] at h
    exact congrArg Fin.val (hf (Fin.ext h))

end Pigeonhole

namespace Subnum

/-- If `Fin n` is subnumerous to `Fin m`, then `n ≤ m`. -/
theorem fin_le {n m : Nat} (h : Subnum (Fin n) (Fin m)) : n ≤ m := by
  obtain ⟨f, hf⟩ := h.exists_inj
  exact Pigeonhole.le_of_injective_fin hf

/-- `Fin n` is subnumerous to `Fin m` exactly when `n ≤ m`. -/
theorem fin_iff {n m : Nat} : Subnum (Fin n) (Fin m) ↔ n ≤ m :=
  ⟨fin_le, fun h =>
    ⟨fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt h⟩,
      fun a b hab => by
        apply Fin.ext
        simp at hab
        exact hab⟩⟩

/-- Pigeonhole principle: `Fin n` does not inject into a strictly smaller `Fin m`. -/
theorem not_fin_of_lt {n m : Nat} (h : m < n) : ¬ Subnum (Fin n) (Fin m) :=
  fun hs => Nat.not_le.mpr h (fin_le hs)

end Subnum

namespace Equinum

/-- Equinumerous finite ordinals have the same size. -/
theorem eq_of_fin {n m : Nat} (h : Equinum (Fin n) (Fin m)) : n = m :=
  Nat.le_antisymm
    (Subnum.fin_le (Subnum.of_equinum h))
    (Subnum.fin_le (Subnum.of_equinum h.symm))

/-- `Fin n` and `Fin m` are equinumerous exactly when `n = m`. -/
theorem fin_iff {n m : Nat} : Equinum (Fin n) (Fin m) ↔ n = m :=
  ⟨eq_of_fin, fun h => by subst h; exact Equinum.refl _⟩

end Equinum
