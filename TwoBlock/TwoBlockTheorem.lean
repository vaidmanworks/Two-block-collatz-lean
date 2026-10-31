import TwoBlock.Tree

/-!
# The two-block theorem, the Farey-pair families, and any pair

The paper: Theorem 3.1, Corollary 3.2 and Theorem 4.2.

The two cited inputs are hypotheses of the theorems, not axioms:
* `EllisonBound`: Ellison's bound `|2^x - 3^y| > 2^x e^(-x/10)` for `x ≥ 28` and `y ≥ 1` (Ellison 1971,
  Theorem 3, stated there for positive `x ∉ {1, …, 11, 13, 14, 16, 19, 27}` and positive `y`; quoted in
  Waldschmidt 2009, §2.2.2);
* `VerifiedBelow (2^37)`: every positive integer below `2^37` reaches 1. Barina (2025) verifies this
  below `2^71`; `VerifiedBelow.mono` passes from his bound to the one used here.
-/

namespace TwoBlock

/-! ### The cited inputs -/

/-- Ellison's bound (his Theorem 3), in the range the paper uses: `x ≥ 28` and `y` positive. -/
def EllisonBound : Prop :=
  ∀ x y : ℕ, 28 ≤ x → 1 ≤ y →
    (2 : ℝ) ^ x * Real.exp (-(x : ℝ) / 10) < |(2 : ℝ) ^ x - (3 : ℝ) ^ y|

/-- The orbit of `x` reaches 1. -/
def ReachesOne (x : ℤ) : Prop := ∃ m : ℕ, T^[m] x = 1

/-- The conjecture verified below `B`. -/
def VerifiedBelow (B : ℤ) : Prop := ∀ x : ℤ, 0 < x → x < B → ReachesOne x

theorem VerifiedBelow.mono {B B' : ℤ} (h : VerifiedBelow B') (hB : B ≤ B') : VerifiedBelow B :=
  fun x hx hxB => h x hx (lt_of_lt_of_le hxB hB)

/-! ### The range `N ≤ 27` -/

/-- A positive cycle of length at most 27 has its point below `2^37`, so the verification makes it the
trivial cycle. -/
theorem small_cycle (hV : VerifiedBelow (2 ^ 37)) {x : ℤ} {w : Word} (hx : 0 < x) (h : IsCycle x w)
    (hN : 0 < N w) (hN27 : N w ≤ 27) : x = 1 ∨ x = 2 := by
  have hxM := h.eq
  have hcn := c_nonneg w
  have hM : 0 < M w := by
    rcases lt_or_gt_of_ne (M_ne_zero hN) with hlt | hgt
    · have : x * M w < 0 := mul_neg_of_pos_of_neg hx hlt
      linarith
    · exact hgt
  have hxc : x ≤ c w := by nlinarith
  have h2N : (2 : ℤ) ^ N w ≤ 2 ^ 27 := pow_le_pow_right₀ (by norm_num) hN27
  have h3 : (3 : ℤ) ^ r w < 2 ^ 27 := by unfold M at hM; linarith
  have hr17 : r w ≤ 17 := by
    by_contra h18
    push_neg at h18
    have h318 : (3 : ℤ) ^ 18 ≤ 3 ^ r w := pow_le_pow_right₀ (by norm_num) h18
    have e1 : (3 : ℤ) ^ 18 = 387420489 := by norm_num
    have e2 : (2 : ℤ) ^ 27 = 134217728 := by norm_num
    rw [e1] at h318
    rw [e2] at h3
    linarith
  have h1 : 2 ^ r w * c w < 2 ^ 27 * 3 ^ r w :=
    lt_of_lt_of_le (c_bound w) (mul_le_mul_of_nonneg_right h2N (by positivity))
  have hcw : c w < 2 ^ 37 := by
    generalize r w = ρ at h1 hr17
    generalize c w = C at h1 ⊢
    interval_cases ρ <;> norm_num at h1 ⊢ <;> omega
  obtain ⟨m, hm⟩ := hV x hx (by linarith)
  exact eq_one_or_two_of_reaches hN h.2 hm

/-! ### Real-number steps -/

theorem ellison_M (hE : EllisonBound) {w : Word} (h28 : 28 ≤ N w) (hr : 0 < r w) :
    (2 : ℝ) ^ N w * Real.exp (-(N w : ℝ) / 10) < |((M w : ℤ) : ℝ)| := by
  have := hE (N w) (r w) h28 hr
  simpa [M] using this

/-- Taking logarithms in `2^n e^(-n/10) < m < d b^E`. -/
theorem log_lt_of_ellison {n E : ℕ} {d b m : ℝ} (hd : 0 < d) (hb : 0 < b)
    (hlow : (2 : ℝ) ^ n * Real.exp (-(n : ℝ) / 10) < m) (hup : m < d * b ^ E) :
    (n : ℝ) * Real.log 2 - n / 10 < Real.log d + E * Real.log b := by
  have hpos : 0 < (2 : ℝ) ^ n * Real.exp (-(n : ℝ) / 10) := by positivity
  have := Real.log_lt_log hpos (hlow.trans hup)
  rw [Real.log_mul (pow_pos two_pos n).ne' (Real.exp_pos _).ne', Real.log_mul hd.ne' (pow_pos hb E).ne',
    Real.log_pow, Real.log_pow, Real.log_exp] at this
  linarith

theorem log_three_lt : Real.log 3 < 1.099 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.099 by norm_num)
  have h3 : Real.exp 1.099 = Real.exp 1 * Real.exp 0.099 := by rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith [Real.exp_pos 0.099]

theorem q_pos : 0 < Real.log 2 ^ 2 - (Real.log 2 + Real.log 3) / 10 := by
  have h1 := Real.log_two_gt_d9
  have h2 := log_three_lt
  nlinarith

/-- The straddling case of Theorems 3.1 and Corollary 3.2, after taking logarithms:
with `A = nk`, `B = n'l` and `LD = log |D|`. -/
theorem straddle_core {A B LD : ℝ}
    (h1 : (A + B) * Real.log 2 - (A + B) / 10 < LD + B * Real.log 2)
    (h2 : (A + B) * Real.log 2 - (A + B) / 10 < LD + A * Real.log 3) :
    (A + B) * (Real.log 2 ^ 2 - (Real.log 2 + Real.log 3) / 10) < LD * (Real.log 2 + Real.log 3) := by
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1' : A * Real.log 2 < (A + B) / 10 + LD := by linarith
  nlinarith [mul_lt_mul_of_pos_right h2 hL2, mul_lt_mul_of_pos_right h1' hL3]

/-- The both-falling case of Corollary 3.2, after taking logarithms. -/
theorem falling_core {A B LD : ℝ}
    (h1 : (A + B) * Real.log 2 - (A + B) / 10 < LD + A * Real.log 2)
    (h2 : (A + B) * Real.log 2 - (A + B) / 10 < LD + B * Real.log 2) :
    (A + B) * (Real.log 2 - 1 / 5) < 2 * LD := by
  linarith

/-- The constants of Corollary 3.2 in the straddling case (`a = log 2`, `b = log 3`). -/
theorem straddle_final {a b n S LD : ℝ} (ha1 : 0.6931471803 < a) (hb1 : 0 < b) (hb2 : b < 1.099)
    (hS : 0 ≤ S) (hLD : LD ≤ a + S * b) (h : n * (a ^ 2 - (a + b) / 10) < LD * (a + b)) :
    n < 6.54 * S + 4.13 := by
  have ha0 : 0 < a := by linarith
  have hsq : a * 0.6931471803 ≤ a * a := mul_le_mul_of_nonneg_left ha1.le ha0.le
  have hq : 0 < a ^ 2 - (a + b) / 10 := by nlinarith
  have c1 : b * (a + b) ≤ 6.54 * (a ^ 2 - (a + b) / 10) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb2.le) (by linarith : (0 : ℝ) ≤ a + b + 1.753)]
  have c0 : a * (a + b) ≤ 4.13 * (a ^ 2 - (a + b) / 10) := by
    nlinarith [mul_le_mul_of_nonneg_left hb2.le ha0.le]
  have e1 : LD * (a + b) ≤ (a + S * b) * (a + b) := mul_le_mul_of_nonneg_right hLD (by linarith)
  have e2 : (a + S * b) * (a + b) ≤ (6.54 * S + 4.13) * (a ^ 2 - (a + b) / 10) := by
    nlinarith [mul_le_mul_of_nonneg_left c1 hS]
  have : n * (a ^ 2 - (a + b) / 10) < (6.54 * S + 4.13) * (a ^ 2 - (a + b) / 10) := by linarith
  exact lt_of_mul_lt_mul_right this hq.le

/-- The constants of Corollary 3.2 in the both-falling case. -/
theorem falling_final {a b n S LD : ℝ} (ha1 : 0.6931471803 < a) (hb2 : b < 1.099)
    (hS : 0 ≤ S) (hLD : LD ≤ a + S * b) (h : n * (a - 1 / 5) < 2 * LD) :
    n < 6.54 * S + 4.13 := by
  have hq : 0 < a - 1 / 5 := by linarith
  have c1 : 2 * b ≤ 6.54 * (a - 1 / 5) := by linarith
  have e2 : 2 * (a + S * b) ≤ (6.54 * S + 4.13) * (a - 1 / 5) := by
    nlinarith [mul_le_mul_of_nonneg_left c1 hS]
  have : n * (a - 1 / 5) < (6.54 * S + 4.13) * (a - 1 / 5) := by linarith
  exact lt_of_mul_lt_mul_right this hq.le

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1 (the two-block theorem).** Let `(X, Y)` be a unimodular pair with
`M_X < 0 < M_Y`. Then for no `k, l ≥ 1` is `X^k Y^l` the parity vector of a non-trivial positive
integer cycle: a positive cycle point at the start of `X^k Y^l` is 1 or 2. -/
theorem two_block {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    (hE : EllisonBound) (hV : VerifiedBelow (2 ^ 37)) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (wpow X k ++ wpow Y l)) : x = 1 ∨ x = 2 := by
  have hrX := r_pos_of_M_neg hX
  have hNY := N_pos_of_M_ne_zero hY.ne'
  have hN : 0 < N (wpow X k ++ wpow Y l) := by
    rw [N_append, N_wpow, N_wpow]; have := Nat.mul_pos hNY hl; omega
  have hr : 0 < r (wpow X k ++ wpow Y l) := by
    rw [r_append, r_wpow, r_wpow]; have := Nat.mul_pos hrX hk; omega
  rcases le_or_gt (N (wpow X k ++ wpow Y l)) 27 with h27 | h28
  · exact small_cycle hV hx h hN h27
  exfalso
  obtain ⟨dY, dX⟩ := two_block_dvd_of_unimodular hU hN hr h.eq
  have hMY : |M (wpow X k ++ wpow Y l)| ≤ F Y l :=
    Int.le_of_dvd (F_pos Y hl) ((abs_dvd _ _).mpr dY)
  have hMX : |M (wpow X k ++ wpow Y l)| ≤ F X k :=
    Int.le_of_dvd (F_pos X hk) ((abs_dvd _ _).mpr dX)
  have h3 : (3 : ℤ) ^ (r X * k) ≤ 3 ^ (N X * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right k (r_le_N X))
  have e1 : |((M (wpow X k ++ wpow Y l) : ℤ) : ℝ)| < 1 * (2 : ℝ) ^ (N Y * l) := by
    rw [one_mul]; exact_mod_cast lt_of_le_of_lt hMY (F_lt_of_M_pos hY hl)
  have e2 : |((M (wpow X k ++ wpow Y l) : ℤ) : ℝ)| < 1 * (3 : ℝ) ^ (N X * k) := by
    rw [one_mul]; exact_mod_cast lt_of_le_of_lt hMX (lt_of_lt_of_le (F_lt_of_M_neg hX hk) h3)
  have hlow := ellison_M hE (w := wpow X k ++ wpow Y l) (by omega) hr
  have l1 := log_lt_of_ellison one_pos two_pos hlow e1
  have l2 := log_lt_of_ellison one_pos three_pos hlow e2
  have hNw : ((N (wpow X k ++ wpow Y l) : ℕ) : ℝ) = ((N X * k : ℕ) : ℝ) + ((N Y * l : ℕ) : ℝ) := by
    rw [N_append, N_wpow, N_wpow, Nat.cast_add]
  rw [Real.log_one, hNw] at l1 l2
  have key := straddle_core l1 l2
  have hA : (0 : ℝ) ≤ ((N X * k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB : (0 : ℝ) < ((N Y * l : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hNY hl
  nlinarith [mul_pos (add_pos_of_nonneg_of_pos hA hB) q_pos]

/-- **Theorem 3.1**, the other orientation: `M_X > 0 > M_Y` (a rotation of the first case). -/
theorem two_block_rev {X Y : Word} (hU : Unimodular X Y) (hX : 0 < M X) (hY : M Y < 0)
    (hE : EllisonBound) (hV : VerifiedBelow (2 ^ 37)) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (wpow X k ++ wpow Y l)) : x = 1 ∨ x = 2 := by
  obtain ⟨hrot, hback⟩ := h.rotate
  have hy := two_block hU.symm hY hX hE hV hl hk (iterate_T_pos hx _) hrot
  rw [← hback]
  exact iterate_T_trivial hy _

/-! ### Theorem 4.2 -/

/-- **Theorem 4.2 (the Farey-pair theorem).** Let `(u, v)` be a pair of the Christoffel tree on the
path of `log₂ 3`. Then for no `k, l ≥ 1` is `u^k v^l` the parity vector of a non-trivial positive
integer cycle. -/
theorem farey_pair {d : ℕ} {u v : Word} (hp : OnPath d u v) (hE : EllisonBound)
    (hV : VerifiedBelow (2 ^ 37)) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {x : ℤ} (hx : 0 < x)
    (h : IsCycle x (wpow u k ++ wpow v l)) : x = 1 ∨ x = 2 :=
  two_block_rev hp.1.unimodular hp.2.1 hp.2.2 hE hV hk hl hx h

/-- **Theorem 4.2 at depth 1** (the pair `(01, 1)`; Mimuro 2005): `(01)^k 1^l`,
read cyclically, is not the parity vector of a non-trivial positive integer cycle. The words
`1^m (10)^b` are rotations of these. -/
theorem depth_one (hE : EllisonBound) (hV : VerifiedBelow (2 ^ 37)) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) {x : ℤ} (hx : 0 < x) (h : IsCycle x (wpow [false, true] k ++ wpow [true] l)) :
    x = 1 ∨ x = 2 :=
  farey_pair ⟨TreePair.right TreePair.root, by simp [M], by simp [M]⟩ hE hV hk hl hx h

/-! ### Corollary 3.2 -/

theorem abs_D_le (X Y : Word) : |D X Y| ≤ 2 * 3 ^ (N X + N Y) := by
  have hp : |c X * M Y| ≤ 3 ^ N X * 3 ^ N Y := by
    rw [abs_mul, abs_of_nonneg (c_nonneg X)]
    exact mul_le_mul (c_lt_three_pow X).le (abs_M_le Y) (abs_nonneg _) (by positivity)
  have hq : |c Y * M X| ≤ 3 ^ N Y * 3 ^ N X := by
    rw [abs_mul, abs_of_nonneg (c_nonneg Y)]
    exact mul_le_mul (c_lt_three_pow Y).le (abs_M_le X) (abs_nonneg _) (by positivity)
  obtain ⟨p1, p2⟩ := abs_le.mp hp
  obtain ⟨q1, q2⟩ := abs_le.mp hq
  rw [D, abs_le, pow_add]
  constructor <;> linarith

theorem log_abs_D_le {X Y : Word} (hD : D X Y ≠ 0) :
    Real.log |((D X Y : ℤ) : ℝ)| ≤ Real.log 2 + ((N X + N Y : ℕ) : ℝ) * Real.log 3 := by
  have hpos : (0 : ℝ) < |((D X Y : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hD)
  have h : |((D X Y : ℤ) : ℝ)| ≤ 2 * (3 : ℝ) ^ (N X + N Y) := by exact_mod_cast abs_D_le X Y
  calc Real.log |((D X Y : ℤ) : ℝ)| ≤ Real.log (2 * (3 : ℝ) ^ (N X + N Y)) := Real.log_le_log hpos h
    _ = Real.log 2 + ((N X + N Y : ℕ) : ℝ) * Real.log 3 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]

theorem M_ne_zero_left {X Y : Word} (hD : D X Y ≠ 0) : M X ≠ 0 := by
  intro hM
  apply hD
  have hN : N X = 0 := by
    by_contra h
    exact M_ne_zero (Nat.pos_of_ne_zero h) hM
  have hc : c X = 0 := c_eq_zero_of_r_eq_zero (by have := r_le_N X; omega)
  unfold D; rw [hc, hM]; ring

theorem M_ne_zero_right {X Y : Word} (hD : D X Y ≠ 0) : M Y ≠ 0 := by
  apply M_ne_zero_left (Y := X)
  rw [D_swap]; exact neg_ne_zero.mpr hD

/-- Corollary 3.2 once rotated so that `M_Y > 0`. -/
theorem any_pair_core {X Y : Word} (hD : D X Y ≠ 0) (hY : 0 < M Y) (hX : M X ≠ 0)
    (hE : EllisonBound) (hV : VerifiedBelow (2 ^ 37)) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (wpow X k ++ wpow Y l))
    (hlen : 6.54 * ((N X + N Y : ℕ) : ℝ) + 4.13 < N (wpow X k ++ wpow Y l)) : x = 1 ∨ x = 2 := by
  have hNY := N_pos_of_M_ne_zero hY.ne'
  have hN : 0 < N (wpow X k ++ wpow Y l) := by
    rw [N_append, N_wpow, N_wpow]; have := Nat.mul_pos hNY hl; omega
  have hr : 0 < r (wpow X k ++ wpow Y l) := by
    rw [r_append, r_wpow, r_wpow]
    rcases r_pos_of_D_ne_zero hD with h1 | h1
    · have := Nat.mul_pos h1 hk; omega
    · have := Nat.mul_pos h1 hl; omega
  rcases le_or_gt (N (wpow X k ++ wpow Y l)) 27 with h27 | h28
  · exact small_cycle hV hx h hN h27
  exfalso
  obtain ⟨dY, dX⟩ := two_block_dvd hN hr h.eq (i := 0) (j := 0) (E := D X Y) (by ring)
  have hDF : ∀ {G : ℤ}, 0 < G → M (wpow X k ++ wpow Y l) ∣ D X Y * G →
      |M (wpow X k ++ wpow Y l)| ≤ |D X Y| * G := by
    intro G hG hd
    have := Int.le_of_dvd (abs_pos.mpr (mul_ne_zero hD hG.ne')) ((abs_dvd_abs _ _).mpr hd)
    rwa [abs_mul, abs_of_pos hG] at this
  have hMY := hDF (F_pos Y hl) dY
  have hMX := hDF (F_pos X hk) dX
  have hDpos : (0 : ℤ) < |D X Y| := abs_pos.mpr hD
  have hDr : (0 : ℝ) < |((D X Y : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hD)
  have hlow := ellison_M hE (w := wpow X k ++ wpow Y l) (by omega) hr
  have hNw : ((N (wpow X k ++ wpow Y l) : ℕ) : ℝ) = ((N X * k : ℕ) : ℝ) + ((N Y * l : ℕ) : ℝ) := by
    rw [N_append, N_wpow, N_wpow, Nat.cast_add]
  have hLD := log_abs_D_le hD
  have hS : (0 : ℝ) ≤ ((N X + N Y : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha1 := Real.log_two_gt_d9
  have hb1 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hb2 := log_three_lt
  rw [hNw] at hlen
  rcases lt_or_gt_of_ne hX with hXn | hXp
  · -- the pair straddles
    have h3 : (3 : ℤ) ^ (r X * k) ≤ 3 ^ (N X * k) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right k (r_le_N X))
    have e1 : |((M (wpow X k ++ wpow Y l) : ℤ) : ℝ)| <
        |((D X Y : ℤ) : ℝ)| * (2 : ℝ) ^ (N Y * l) := by
      have : |M (wpow X k ++ wpow Y l)| < |D X Y| * 2 ^ (N Y * l) :=
        lt_of_le_of_lt hMY (mul_lt_mul_of_pos_left (F_lt_of_M_pos hY hl) hDpos)
      exact_mod_cast this
    have e2 : |((M (wpow X k ++ wpow Y l) : ℤ) : ℝ)| <
        |((D X Y : ℤ) : ℝ)| * (3 : ℝ) ^ (N X * k) := by
      have : |M (wpow X k ++ wpow Y l)| < |D X Y| * 3 ^ (N X * k) :=
        lt_of_le_of_lt hMX
          (mul_lt_mul_of_pos_left (lt_of_lt_of_le (F_lt_of_M_neg hXn hk) h3) hDpos)
      exact_mod_cast this
    have l1 := log_lt_of_ellison hDr two_pos hlow e1
    have l2 := log_lt_of_ellison hDr three_pos hlow e2
    rw [hNw] at l1 l2
    have := straddle_final ha1 hb1 hb2 hS hLD (straddle_core l1 l2)
    linarith
  · -- both blocks fall
    have e1 : |((M (wpow X k ++ wpow Y l) : ℤ) : ℝ)| <
        |((D X Y : ℤ) : ℝ)| * (2 : ℝ) ^ (N X * k) := by
      have : |M (wpow X k ++ wpow Y l)| < |D X Y| * 2 ^ (N X * k) :=
        lt_of_le_of_lt hMX (mul_lt_mul_of_pos_left (F_lt_of_M_pos hXp hk) hDpos)
      exact_mod_cast this
    have e2 : |((M (wpow X k ++ wpow Y l) : ℤ) : ℝ)| <
        |((D X Y : ℤ) : ℝ)| * (2 : ℝ) ^ (N Y * l) := by
      have : |M (wpow X k ++ wpow Y l)| < |D X Y| * 2 ^ (N Y * l) :=
        lt_of_le_of_lt hMY (mul_lt_mul_of_pos_left (F_lt_of_M_pos hY hl) hDpos)
      exact_mod_cast this
    have l1 := log_lt_of_ellison hDr two_pos hlow e1
    have l2 := log_lt_of_ellison hDr two_pos hlow e2
    rw [hNw] at l1 l2
    have := falling_final ha1 hb2 hS hLD (falling_core l1 l2)
    linarith

/-- **Corollary 3.2 (any pair).** Let `X`, `Y` be parity words with `p_X ≠ p_Y`, i.e. `D(X, Y) ≠ 0`.
No non-trivial positive integer cycle has parity vector `X^k Y^l` (`k, l ≥ 1`) with
`N = nk + n'l > 6.54 (n + n') + 4.13`. -/
theorem any_pair {X Y : Word} (hD : D X Y ≠ 0) (hE : EllisonBound) (hV : VerifiedBelow (2 ^ 37))
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {x : ℤ} (hx : 0 < x) (h : IsCycle x (wpow X k ++ wpow Y l))
    (hlen : 6.54 * ((N X + N Y : ℕ) : ℝ) + 4.13 < N (wpow X k ++ wpow Y l)) : x = 1 ∨ x = 2 := by
  have hX := M_ne_zero_left hD
  have hY := M_ne_zero_right hD
  rcases lt_or_gt_of_ne hY with hYn | hYp
  · rcases lt_or_gt_of_ne hX with hXn | hXp
    · -- both blocks rise: then `M_w < 0 ≤ c_w = x M_w`, impossible for `x > 0`
      exfalso
      have hFX := F_pos X hk
      have hFY := F_pos Y hl
      have h3 : (0 : ℤ) < 3 ^ (r Y * l) := by positivity
      have h2 : (0 : ℤ) < 2 ^ (N X * k) := by positivity
      have hM : M (wpow X k ++ wpow Y l) < 0 := by
        rw [M_two_block]
        have t1 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h3 hXn) hFX
        have t2 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h2 hYn) hFY
        linarith
      have := h.eq
      have := c_nonneg (wpow X k ++ wpow Y l)
      have := mul_neg_of_pos_of_neg hx hM
      linarith
    · -- `M_X > 0 > M_Y`: read the cycle from the start of `Y^l`
      obtain ⟨hrot, hback⟩ := h.rotate
      have e1 : N Y + N X = N X + N Y := Nat.add_comm _ _
      have e2 : N (wpow Y l ++ wpow X k) = N (wpow X k ++ wpow Y l) := by
        simp only [N_append]; omega
      have hlen' : 6.54 * ((N Y + N X : ℕ) : ℝ) + 4.13 < N (wpow Y l ++ wpow X k) := by
        rw [e1, e2]; exact hlen
      have hy := any_pair_core (by rw [D_swap]; exact neg_ne_zero.mpr hD) hXp hY hE hV hl hk
        (iterate_T_pos hx _) hrot hlen'
      rw [← hback]
      exact iterate_T_trivial hy _
  · exact any_pair_core hD hYp hX hE hV hk hl hx h hlen

end TwoBlock
