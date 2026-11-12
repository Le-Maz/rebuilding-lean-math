import ReMath.DiscreteCalc.Defs
import ReMath.Alg.Defs
import ReMath.Alg.Lemmas

namespace DiscreteCalc

/-- The discrete product rule. -/
theorem fwd_add {M : Type _} [Alg.Ring M] (f g : Nat → M) (n : Nat) :
    Δ (fun i => f i + g i) n = Δ f n + Δ g n := by
  change _ - _ = (_ - _) + (_ - _)
  simp only [Alg.sub_add, Alg.add_sub_assoc]
  simp only [Alg.sub_eq_add_neg]
  ac_rfl

/-- The discrete product rule. -/
theorem fwd_mul {M : Type _} [Alg.Ring M] (f g : Nat → M) (n : Nat) :
    Δ (fun i => f i * g i) n = f (n + 1) * Δ g n + Δ f n * g n := by
  change f (n + 1) * g (n + 1) - f n * g n =
    f (n + 1) * (g (n + 1) - g n) + (f (n + 1) - f n) * g n
  rw [Alg.mul_sub, Alg.sub_mul, Alg.add_comm, Alg.sub_add_sub_cancel]

@[simp]
theorem fwdIter_zero {α} [Sub α] (f : Nat → α) (n : Nat) :
  Δ^[0] f n = f n := rfl

@[simp]
theorem fwdIter_succ {α} [Sub α] (f : Nat → α) (k n : Nat) :
  Δ^[k+1] f n = Δ (Δ^[k] f) n := rfl

@[simp]
theorem finSum_nil {α} [Zero α] [Add α] (f : Fin 0 → α) :
    finSum 0 f = 0 := by
  simp [finSum]

theorem finSum_succ {α} [Zero α] [Add α] {m : Nat}
    (f : Fin (m + 1) → α) :
    finSum (m + 1) f = f 0 + finSum m (fun k => f k.succ) := by
  simp [finSum, Fin.foldr_succ]

/-- Sums of pointwise equal functions are equal. -/
theorem finSum_congr {α} [Zero α] [Add α] {m : Nat}
    {f g : Fin m → α} (h : ∀ k, f k = g k) :
    finSum m f = finSum m g :=
  congrArg (finSum m) (funext h)

/-- A sum of zeros is zero. -/
@[simp]
theorem finSum_const_zero {α} [Alg.AddMonoid α] (m : Nat) :
    finSum m (fun _ => (0 : α)) = 0 := by
  induction m with
  | zero => exact finSum_nil _
  | succ m ih =>
    rw [finSum_succ]
    exact (congrArg (0 + ·) ih).trans (Alg.zero_add 0)

/-- Rearranging four summands. -/
theorem add_add_add_comm' {α} [Alg.AddCommMonoid α] (a b c d : α) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Alg.add_assoc, ← Alg.add_assoc b c d, Alg.add_comm b c,
    Alg.add_assoc c b d, ← Alg.add_assoc]

/-- Sums are additive. -/
theorem finSum_add {α} [Alg.AddCommMonoid α] {m : Nat}
    (f g : Fin m → α) :
    finSum m (fun k => f k + g k) = finSum m f + finSum m g := by
  induction m with
  | zero => simp only [finSum_nil, Alg.add_zero]
  | succ m ih =>
    simp only [finSum_succ]
    rw [ih (fun k => f k.succ) (fun k => g k.succ)]
    exact add_add_add_comm' _ _ _ _

/-- Negation distributes over sums. -/
theorem finSum_neg {α} [Alg.AddCommGroup α] {m : Nat}
    (f : Fin m → α) :
    finSum m (fun k => -f k) = -finSum m f := by
  induction m with
  | zero =>
    simp only [finSum_nil]
    exact (Alg.add_zero _).symm.trans (Alg.neg_add_cancel _) |>.symm
  | succ m ih =>
    simp only [finSum_succ]
    rw [ih (fun k => f k.succ), Alg.neg_add]

/-- Sums distribute over subtraction. -/
theorem finSum_sub {α} [Alg.AddCommGroup α] {m : Nat}
    (f g : Fin m → α) :
    finSum m (fun k => f k - g k) = finSum m f - finSum m g := by
  simp only [Alg.sub_eq_add_neg]
  rw [finSum_add, finSum_neg]

/-- Multiplication on the left distributes over sums. -/
theorem mul_finSum {α} [Alg.Semiring α] {m : Nat}
    (c : α) (f : Fin m → α) :
    c * finSum m f = finSum m (fun k => c * f k) := by
  induction m with
  | zero => simp only [finSum_nil, Alg.mul_zero]
  | succ m ih =>
    simp only [finSum_succ]
    rw [Alg.mul_add, ih (fun k => f k.succ)]

/-- Multiplication on the right distributes over sums. -/
theorem finSum_mul {α} [Alg.Semiring α] {m : Nat}
    (f : Fin m → α) (c : α) :
    finSum m f * c = finSum m (fun k => f k * c) := by
  induction m with
  | zero => simp only [finSum_nil, Alg.zero_mul]
  | succ m ih =>
    simp only [finSum_succ]
    rw [Alg.add_mul, ih (fun k => f k.succ)]

/-- Double sums can be taken in either order. -/
theorem finSum_comm {α} [Alg.AddCommMonoid α] {n m : Nat}
    (f : Fin n → Fin m → α) :
    finSum n (fun i => finSum m (fun j => f i j)) =
      finSum m (fun j => finSum n (fun i => f i j)) := by
  induction n with
  | zero => simp only [finSum_nil, finSum_const_zero]
  | succ n ih =>
    simp only [finSum_succ]
    rw [finSum_add, ih (fun i => f i.succ)]

/-- A sum with a single nonzero term. -/
theorem finSum_ite_eq {α} [Alg.AddMonoid α] {m : Nat}
    (f : Fin m → α) (j : Fin m) :
    finSum m (fun k => if k = j then f k else 0) = f j := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    cases j using Fin.cases with
    | zero =>
      rw [finSum_succ, if_pos rfl,
        finSum_congr (g := fun _ => 0)
          fun k => if_neg (Fin.succ_ne_zero k)]
      simp only [finSum_const_zero, Alg.add_zero]
    | succ j =>
      rw [finSum_succ, if_neg (Fin.succ_ne_zero j).symm, Alg.zero_add,
        finSum_congr (g := fun k => if k = j then f k.succ else 0)
          fun k => by simp only [Fin.succ_inj]]
      exact ih (fun k => f k.succ) j

/-- A sum with a single nonzero term, with the test flipped. -/
theorem finSum_ite_eq' {α} [Alg.AddMonoid α] {m : Nat}
    (f : Fin m → α) (j : Fin m) :
    finSum m (fun k => if j = k then f k else 0) = f j := by
  rw [← finSum_ite_eq f j]
  refine finSum_congr fun k => ?_
  by_cases h : j = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

@[simp]
theorem sum_zero {M : Type _} [Zero M] [Add M] (f : Nat → M) :
    ∑ f 0 = 0 :=
  finSum_nil _

theorem sum_succ {M : Type _} [Zero M] [Add M] (f : Nat → M) (n : Nat) :
    ∑ f (n + 1) = f 0 + ∑ (fun i => f (i + 1)) n :=
  finSum_succ _

theorem sum_succ' {M : Type _} [Alg.AddMonoid M] (f : Nat → M) (n : Nat) :
    ∑ f (n + 1) = ∑ f n + f n := by
  induction n generalizing f with
  | zero =>
    rw [sum_succ, sum_zero, sum_zero, Alg.add_zero, Alg.zero_add]
  | succ n ih =>
    rw [sum_succ, ih]
    rw [← Alg.add_assoc, ← sum_succ]

theorem sum_const {M : Type _} [Alg.AddMonoid M] (x : M) (n : Nat) :
    ∑ (fun _ => x) n = n • x := by
  induction n with
  | zero =>
    simp [sum_zero, Alg.zero_nsmul]
  | succ n ih =>
    rw [sum_succ', Alg.succ_nsmul]
    congr 1

theorem nsmul_sum {M : Type _} [Alg.AddCommMonoid M] (f : Nat → M) (k n : Nat) :
    k • ∑ f n = ∑ (fun i => k • f i) n := by
  induction n with
  | zero =>
    simp [sum_zero, Alg.nsmul_zero]
  | succ n ih =>
    rw [sum_succ', sum_succ']
    rw [Alg.nsmul_add, ih]

theorem mul_sum {M : Type _} [Alg.Semiring M] (f : Nat → M) (x : M) (n : Nat) :
    x * ∑ f n = ∑ (fun i => x * f i) n :=
  mul_finSum x _

/-- The sum of forward differences telescopes. -/
theorem sum_fwd {M : Type _} [Alg.Ring M] (f : Nat → M) (n : Nat) :
    ∑ Δ f n = f n - f 0 := by
  induction n with
  | zero =>
    rw [sum_zero, Alg.sub_self]
  | succ n ih =>
    rw [sum_succ', ih]
    exact Alg.sub_add_sub_cancel (f n) (f 0) (f (n + 1))

/-- The forward difference of a sum recovers the summand. -/
theorem fwd_sum {M : Type _} [Alg.Ring M] (f : Nat → M) (n : Nat) :
    Δ ∑ f n = f n := by
  change ∑ f (n + 1) - ∑ f n = f n
  rw [sum_succ']
  exact Alg.add_sub_cancel_left (∑ f n) (f n)

/-- Negation distributes over finite sums. -/
theorem sum_neg {M : Type _} [Alg.AddCommGroup M]
    (f : Nat → M) (n : Nat) :
    ∑ (fun i => -f i) n = -(∑ f n) :=
  finSum_neg _

/-- Finite sums distribute over addition. -/
theorem sum_add {M : Type _} [Alg.AddCommMonoid M]
    (f g : Nat → M) (n : Nat) :
    ∑ (fun i => f i + g i) n =
      ∑ f n + ∑ g n :=
  finSum_add _ _

/-- Finite sums distribute over subtraction. -/
theorem sum_sub {M : Type _} [Alg.AddCommGroup M]
    (f g : Nat → M) (n : Nat) :
    ∑ (fun i => f i - g i) n =
      ∑ f n - ∑ g n :=
  finSum_sub _ _

/-- Discrete summation by parts. -/
theorem sum_parts {M : Type _} [Alg.Ring M]
    (f g : Nat → M) (n : Nat) :
    ∑ (fun i => f i * Δ g i) n =
      f n * g n - f 0 * g 0 -
        ∑ (fun i => Δ f i * g (i + 1)) n := by
  have hpoint (i : Nat) :
      f i * Δ g i =
        Δ (fun j => f j * g j) i -
          Δ f i * g (i + 1) := by
    rw [fwd_mul, ← Alg.add_sub_assoc]
    rw [← Alg.mul_sub]
    simp only [fwd] at *
    grind only

  calc
    ∑ (fun i => f i * Δ g i) n =
        ∑ (fun i =>
          Δ (fun j => f j * g j) i -
            Δ f i * g (i + 1)) n := by
              congr 1
              funext i
              exact hpoint i
    _ = (∑ (fun i => Δ (fun j => f j * g j) i) n) -
        (∑ (fun i => Δ f i * g (i + 1)) n) := by
          exact sum_sub _ _ _
    _ = f n * g n - f 0 * g 0 -
        ∑ (fun i => Δ f i * g (i + 1)) n := by
          rw [sum_fwd]

/-- Shifting a finite sum by one, without requiring subtraction. -/
theorem sum_shift {M : Type _} [Alg.AddMonoid M]
    (f : Nat → M) (n : Nat) :
    f 0 + ∑ (fun i => f (i + 1)) n =
      ∑ f n + f n := by
  induction n with
  | zero =>
    simp [sum_zero]
  | succ n ih =>
    rw [sum_succ', sum_succ']
    rw [← Alg.add_assoc, ih]

end DiscreteCalc
