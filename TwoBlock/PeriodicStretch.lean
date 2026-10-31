import TwoBlock.Stretch
import TwoBlock.CitedBounds

/-!
# The periodic-stretch bound: Theorem 7.2

Section 7 of the paper. A point `x` of a non-trivial positive integer cycle, followed
by `k ≥ 2` copies of a word `X` (`x ≠ p_X`), satisfies

  `n k log 2 ≤ log(x / x_min) + log |M_X| + log(2r/3) - log Λ`,   `Λ = N log 2 - r log 3`.

With Laurent's bound this is the paper's Theorem 7.2. With Rhin's measure in the Simons–de Weger form
it gives `-log Λ < 13.3 (0.46057 + log r)` in place of Laurent's term (the remark after Lemma 7.3).

As in `cycle_repeat`, the cycle's minimum may be replaced by any positive lower bound `m` for its
points, and the cycle length `N` by any return time `n` of `x`, with `r` the number of odd steps among
the first `n`.

The paper's proof uses the verification below `2^71` only for `n ≤ 2`, where it needs `x > 9`. Here
that comes from `verifiedBelow_ten`, checked by running the map, so the verification is not a
hypothesis.
-/

namespace TwoBlock

/-- `4^n < 2 · 3^n` only for `n ≤ 2`. -/
theorem le_two_of_four_pow_lt {n : ℕ} (h : (4 : ℤ) ^ n < 2 * 3 ^ n) : n ≤ 2 := by
  by_contra h3
  push_neg at h3
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have h43 : (3 : ℤ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have h30 : (0 : ℤ) < 3 ^ j := by positivity
  rw [pow_add, pow_add] at h
  linarith

/-- **The congruence step of Theorem 7.2.** If `x ≥ 10` is followed by `k ≥ 2` copies of `X` and
`x ≠ p_X`, then `2^(nk) ≤ 2 |M_X| x`. -/
theorem stretch_pow_le {X : Word} {k : ℕ} (hk : 2 ≤ k) {x : ℤ} (hx : 10 ≤ x)
    (hX : Follows x (wpow X k)) (hpX : x * M X ≠ c X) :
    (2 : ℤ) ^ (N X * k) ≤ 2 * |M X| * x := by
  have hd := stretch_dvd hX
  have hne : M X * x - c X ≠ 0 := by
    intro h0; apply hpX; linarith
  have h1 : (2 : ℤ) ^ (N X * k) ≤ |M X * x - c X| :=
    Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hd)
  have hc0 := c_nonneg X
  have hc3 := c_lt_three_pow X
  have hMne : M X ≠ 0 := by
    intro hM
    apply hpX
    have hN : N X = 0 := by
      by_contra hN
      exact M_ne_zero (Nat.pos_of_ne_zero hN) hM
    have hc : c X = 0 := c_eq_zero_of_r_eq_zero (by have := r_le_N X; omega)
    rw [hM, hc, mul_zero]
  have hM1 : 1 ≤ |M X| := Int.one_le_abs hMne
  have hx0 : (0 : ℤ) ≤ x := by linarith
  have h2 : |M X * x - c X| ≤ |M X| * x + c X := by
    rw [abs_le]
    have l1 := mul_le_mul_of_nonneg_right (neg_abs_le (M X)) hx0
    have l2 := mul_le_mul_of_nonneg_right (le_abs_self (M X)) hx0
    constructor <;> linarith
  rcases le_or_gt (c X) (|M X| * x) with hcx | hcx
  · linarith
  · exfalso
    have h4 : (4 : ℤ) ^ N X ≤ 2 ^ (N X * k) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by rw [mul_comm]; exact Nat.mul_le_mul le_rfl hk)
    have hlt : (4 : ℤ) ^ N X < 2 * 3 ^ N X := by linarith
    have hn2 := le_two_of_four_pow_lt hlt
    have h9 : (3 : ℤ) ^ N X ≤ 9 := by
      calc (3 : ℤ) ^ N X ≤ 3 ^ 2 := pow_le_pow_right₀ (by norm_num) hn2
        _ = 9 := by norm_num
    have : x ≤ |M X| * x := by nlinarith
    linarith

/-- **Theorem 7.2, before the Baker step.** Let `x > 0` lie on a non-trivial cycle (`T^n(x) = x`),
with every point at least `m > 0`, and let `x` be followed by `k ≥ 2` copies of `X`, `x ≠ p_X`. With
`r` the number of odd steps and `Λ = n log 2 - r log 3`,
`n_X k log 2 ≤ log(x/m) + log |M_X| + log(2r/3) - log Λ`. -/
theorem periodic_stretch_core {X : Word} {k : ℕ} (hk : 2 ≤ k) {x : ℤ} (hx : 0 < x) {n : ℕ}
    (hn : 0 < n) (hc : T^[n] x = x) (hnt : ¬(x = 1 ∨ x = 2)) {m : ℤ} (hm0 : 0 < m)
    (hm : ∀ t < n, m ≤ T^[t] x) (hX : Follows x (wpow X k)) (hpX : x * M X ≠ c X) :
    ((N X * k : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((x : ℝ) / m) + Real.log |((M X : ℤ) : ℝ)| +
      Real.log (2 * (oddSteps x n).card / 3) - Real.log (Lambda x n) := by
  have h10 := ten_le_of_cycle hx hn hc hnt
  have hpow := stretch_pow_le hk h10 hX hpX
  have hΛ := Lambda_pos hx hn hc
  have hb := Lambda_min_bound hx hc hm0 hm
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hrR : (0 : ℝ) < (oddSteps x n).card := by
    have : 0 < 3 * Lambda x n * m := mul_pos (mul_pos three_pos hΛ) hmR
    linarith
  have hMR : (0 : ℝ) < |((M X : ℤ) : ℝ)| := by
    have h2 : (0 : ℤ) < 2 * |M X| * x := lt_of_lt_of_le (by positivity) hpow
    have : (0 : ℤ) < |M X| := by nlinarith [abs_nonneg (M X)]
    exact_mod_cast this
  have hpowR : (2 : ℝ) ^ (N X * k) ≤ 2 * |((M X : ℤ) : ℝ)| * x := by exact_mod_cast hpow
  have l1 := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow, Real.log_mul (mul_pos two_pos hMR).ne' hxR.ne',
    Real.log_mul two_ne_zero hMR.ne'] at l1
  have e3 : Real.log ((x : ℝ) / m) = Real.log x - Real.log m := Real.log_div hxR.ne' hmR.ne'
  have l2 : Real.log m ≤ Real.log (oddSteps x n).card - Real.log 3 - Real.log (Lambda x n) := by
    have hle : (m : ℝ) ≤ (oddSteps x n).card / (3 * Lambda x n) := by
      rw [le_div_iff₀ (mul_pos three_pos hΛ)]; linarith
    have := Real.log_le_log hmR hle
    rw [Real.log_div hrR.ne' (mul_pos three_pos hΛ).ne', Real.log_mul three_ne_zero hΛ.ne'] at this
    linarith
  have e4 : Real.log (2 * (oddSteps x n).card / 3) =
      Real.log 2 + Real.log (oddSteps x n).card - Real.log 3 := by
    rw [Real.log_div (mul_pos two_pos hrR).ne' three_ne_zero, Real.log_mul two_ne_zero hrR.ne']
  linarith

/-- **Theorem 7.2 (the periodic-stretch bound).** Let `x > 0` lie on a non-trivial positive integer
cycle of length `n` with `r` odd steps, every point at least `m > 0` (the minimum, or any lower
bound), and let `x` be followed by `X^k` with `k ≥ 2` and `x ≠ p_X`. Then
`n_X k log 2 ≤ log(x/m) + log |M_X| + log(2r/3)
  + 28.161 · log 3 · (max(log(((1 + log 2)/log 3) n) + 0.21, 14))²`.
(The paper writes `30.9381` for `28.161 · log 3 = 30.93802…` and `1.5412` for
`(1 + log 2)/log 3 = 1.541169…`, both rounded up.) Input: Laurent's bound. -/
theorem periodic_stretch (hL : LaurentBound) {X : Word} {k : ℕ} (hk : 2 ≤ k) {x : ℤ} (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) (hc : T^[n] x = x) (hnt : ¬(x = 1 ∨ x = 2)) {m : ℤ} (hm0 : 0 < m)
    (hm : ∀ t < n, m ≤ T^[t] x) (hX : Follows x (wpow X k)) (hpX : x * M X ≠ c X) :
    ((N X * k : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((x : ℝ) / m) + Real.log |((M X : ℤ) : ℝ)| +
      Real.log (2 * (oddSteps x n).card / 3) +
        28.161 * Real.log 3 * (max (Real.log ((1 + Real.log 2) / Real.log 3 * n) + 0.21) 14) ^ 2 := by
  have hcore := periodic_stretch_core hk hx hn hc hnt hm0 hm hX hpX
  have hΛ := Lambda_pos hx hn hc
  have hb := Lambda_min_bound hx hc hm0 hm
  have hr : 0 < (oddSteps x n).card := by
    have : (0 : ℝ) < (oddSteps x n).card := by
      have : 0 < 3 * Lambda x n * m := mul_pos (mul_pos three_pos hΛ) (by exact_mod_cast hm0)
      linarith
    exact_mod_cast this
  have hΛ' : 0 < (n : ℝ) * Real.log 2 - (oddSteps x n).card * Real.log 3 := hΛ
  have hlau := laurent_neg_log_le hL hn hr hΛ'
  unfold Lambda at hcore
  linarith

/-- **Theorem 7.2 with Rhin's measure** in the Simons–de Weger form: in the setting of
`periodic_stretch`, `n_X k log 2 ≤ log(x/m) + log |M_X| + log(2r/3) + 13.3 (0.46057 + log r)`. -/
theorem periodic_stretch_rhin (hR : RhinBound) {X : Word} {k : ℕ} (hk : 2 ≤ k) {x : ℤ}
    (hx : 0 < x) {n : ℕ} (hn : 0 < n) (hc : T^[n] x = x) (hnt : ¬(x = 1 ∨ x = 2)) {m : ℤ}
    (hm0 : 0 < m) (hm : ∀ t < n, m ≤ T^[t] x) (hX : Follows x (wpow X k)) (hpX : x * M X ≠ c X) :
    ((N X * k : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((x : ℝ) / m) + Real.log |((M X : ℤ) : ℝ)| +
      Real.log (2 * (oddSteps x n).card / 3) + 13.3 * (0.46057 + Real.log (oddSteps x n).card) := by
  have hcore := periodic_stretch_core hk hx hn hc hnt hm0 hm hX hpX
  have hΛ := Lambda_pos hx hn hc
  have hb := Lambda_min_bound hx hc hm0 hm
  have hr : 0 < (oddSteps x n).card := by
    have : (0 : ℝ) < (oddSteps x n).card := by
      have : 0 < 3 * Lambda x n * m := mul_pos (mul_pos three_pos hΛ) (by exact_mod_cast hm0)
      linarith
    exact_mod_cast this
  have hΛ' : 0 < (n : ℝ) * Real.log 2 - (oddSteps x n).card * Real.log 3 := hΛ
  have hrh := rhin_neg_log_lt hR hr hΛ'
  unfold Lambda at hcore
  linarith

end TwoBlock
