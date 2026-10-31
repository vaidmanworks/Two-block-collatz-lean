import TwoBlock.TwoBlockTheorem

/-!
# The cited inputs of Sections 6 and 7

The paper, Sections 6–7. As with `EllisonBound`, each cited result is a `Prop`
that the theorems take as a hypothesis, never an axiom.

* `LaurentBound`: Laurent's bound for two logarithms (Laurent 2008, Corollary 1 and pp. 346–347), in
  the form Bennett and Siksek (2023, Theorem 9) derive, for the logarithms of 2 and 3, as the paper
  quotes it in the proof of Theorem 6.2: with `b' = r + N / log 3`,
  `log |N log 2 - r log 3| ≥ -28.161 · log 3 · (max(log b' + 0.21, 14))²`.
* `RhinBound`: Rhin's measure (1987, p. 160) in the form of Simons and de Weger (2005, Lemma 12):
  `N log 2 - r log 3 > exp(-13.3 (0.46057 + log r))` whenever the left side is positive and `r ≥ 1`.
* `CycleLengthBound B`: every non-trivial positive integer cycle has length at least `B`. Eliahou
  (1993) gives `B = 17087915`.

On a cycle `r log 3 < N log 2`, so `b' < ((1 + log 2) / log 3) N`, with
`(1 + log 2) / log 3 = 1.541169…`; the paper rounds this factor up to `1.5412`. The statements below
keep the exact factor `(1 + log 2) / log 3`, and likewise the exact constant
`28.161 · log 3 = 30.93802…`, which the paper rounds up to `30.9381`.
-/

namespace TwoBlock

/-! ### The cited inputs -/

/-- Laurent's bound for two logarithms (Laurent 2008, Corollary 1 and pp. 346–347) in the form of
Bennett and Siksek (2023, Theorem 9), for `β₂ = 2`, `c₂ = N`, `β₁ = 3`, `c₁ = r`, as quoted in the paper
(proof of Theorem 6.2): with `b' = r + N / log 3`,
`log |N log 2 - r log 3| ≥ -28.161 · log 3 · (max(log b' + 0.21, 14))²`. -/
def LaurentBound : Prop :=
  ∀ Nn r : ℕ, 0 < Nn → 0 < r →
    -(28.161 * Real.log 3 * (max (Real.log (r + Nn / Real.log 3) + 0.21) 14) ^ 2) ≤
      Real.log |Nn * Real.log 2 - r * Real.log 3|

/-- Rhin's measure (Rhin 1987, p. 160) in the form of Simons and de Weger (2005, Lemma 12), as quoted
in the paper (remark after Theorem 6.5): `N log 2 - r log 3 > exp(-13.3 (0.46057 + log r))` whenever
`r ≥ 1` and the left side is positive. -/
def RhinBound : Prop :=
  ∀ Nn r : ℕ, 0 < r → 0 < (Nn : ℝ) * Real.log 2 - r * Real.log 3 →
    Real.exp (-(13.3 * (0.46057 + Real.log r))) < Nn * Real.log 2 - r * Real.log 3

/-- A lower bound `B` for the length of a non-trivial positive integer cycle: a positive `x` with
`T^n(x) = x` for some `n ≥ 1`, other than 1 and 2, has `n ≥ B`. Eliahou (1993) proves this for
`B = 17087915`. (Any return time is a multiple of the period, so this is the bound on periods.) -/
def CycleLengthBound (B : ℕ) : Prop :=
  ∀ x : ℤ, 0 < x → ∀ n : ℕ, 0 < n → T^[n] x = x → ¬(x = 1 ∨ x = 2) → B ≤ n

theorem CycleLengthBound.mono {B B' : ℕ} (h : CycleLengthBound B') (hB : B ≤ B') :
    CycleLengthBound B :=
  fun x hx n hn hc hnt => le_trans hB (h x hx n hn hc hnt)

/-- The conjecture below 10, checked by running the map. -/
theorem verifiedBelow_ten : VerifiedBelow 10 := by
  intro x hx hx10
  interval_cases x
  · exact ⟨0, rfl⟩
  · exact ⟨1, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨6, by decide⟩
  · exact ⟨11, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨13, by decide⟩

/-- A point of a non-trivial positive cycle is at least 10. -/
theorem ten_le_of_cycle {x : ℤ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (hc : T^[n] x = x)
    (hnt : ¬(x = 1 ∨ x = 2)) : 10 ≤ x := by
  by_contra h10
  push_neg at h10
  obtain ⟨m, hm⟩ := verifiedBelow_ten x hx h10
  exact hnt (eq_one_or_two_of_reaches hn hc hm)

/-! ### Logarithms -/

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- **Laurent's bound, in the form used.** If `0 < Λ = N log 2 - r log 3` with `N, r ≥ 1`, then
`-log Λ ≤ 28.161 · log 3 · (max(log(((1 + log 2) / log 3) N) + 0.21, 14))²`. -/
theorem laurent_neg_log_le (hL : LaurentBound) {Nn r : ℕ} (hN : 0 < Nn) (hr : 0 < r)
    (hΛ : 0 < (Nn : ℝ) * Real.log 2 - r * Real.log 3) :
    -Real.log ((Nn : ℝ) * Real.log 2 - r * Real.log 3) ≤
      28.161 * Real.log 3 * (max (Real.log ((1 + Real.log 2) / Real.log 3 * Nn) + 0.21) 14) ^ 2 := by
  have h := hL Nn r hN hr
  rw [abs_of_pos hΛ] at h
  have hl3 := log_three_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hNR : (0 : ℝ) < Nn := by exact_mod_cast hN
  have hl3ne : Real.log 3 ≠ 0 := hl3.ne'
  have hdiff : (1 + Real.log 2) / Real.log 3 * Nn - (r + Nn / Real.log 3) =
      (Nn * Real.log 2 - r * Real.log 3) / Real.log 3 := by
    field_simp; ring
  have hb : (r : ℝ) + Nn / Real.log 3 ≤ (1 + Real.log 2) / Real.log 3 * Nn := by
    have := div_pos hΛ hl3
    linarith
  have hb0 : 0 < (r : ℝ) + Nn / Real.log 3 := add_pos hrR (div_pos hNR hl3)
  have hlog := Real.log_le_log hb0 hb
  have hmax : max (Real.log ((r : ℝ) + Nn / Real.log 3) + 0.21) 14 ≤
      max (Real.log ((1 + Real.log 2) / Real.log 3 * Nn) + 0.21) 14 :=
    max_le_max (by linarith) le_rfl
  have hm0 : (0 : ℝ) ≤ max (Real.log ((r : ℝ) + Nn / Real.log 3) + 0.21) 14 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hsq := pow_le_pow_left₀ hm0 hmax 2
  have hC : 0 ≤ 28.161 * Real.log 3 := mul_nonneg (by norm_num) hl3.le
  have := mul_le_mul_of_nonneg_left hsq hC
  linarith

/-- **Rhin's measure, in the form used.** If `0 < Λ = N log 2 - r log 3` with `r ≥ 1`, then
`-log Λ < 13.3 (0.46057 + log r)`. -/
theorem rhin_neg_log_lt (hR : RhinBound) {Nn r : ℕ} (hr : 0 < r)
    (hΛ : 0 < (Nn : ℝ) * Real.log 2 - r * Real.log 3) :
    -Real.log ((Nn : ℝ) * Real.log 2 - r * Real.log 3) < 13.3 * (0.46057 + Real.log r) := by
  have h := (Real.lt_log_iff_exp_lt hΛ).mpr (hR Nn r hr hΛ)
  linarith

/-! ### The largest root -/

/-- `(P + log t)² ≤ t P²` for `t ≥ 1` and `P ≥ 2`, since `log t ≤ 2 (√t - 1)`. -/
theorem sq_add_log_le {P t : ℝ} (hP : 2 ≤ P) (ht : 1 ≤ t) : (P + Real.log t) ^ 2 ≤ t * P ^ 2 := by
  have hs1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hs1)
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h2 := mul_le_mul_of_nonneg_right hP (sub_nonneg.mpr hs1)
  have key : P + Real.log t ≤ P * Real.sqrt t := by nlinarith
  calc (P + Real.log t) ^ 2 ≤ (P * Real.sqrt t) ^ 2 := pow_le_pow_left₀ (by linarith) key 2
    _ = t * P ^ 2 := by rw [mul_pow, hsq]; ring

/-- **The largest root.** If `ρ N₀ ≥ log(2s) + 28.161 · log 3 · (max(log(κ N₀) + 0.21, 14))²`, with
`κ = (1 + log 2) / log 3`, then the same holds at every `N ≥ N₀`: the right side divided by `N`
decreases. So a length bound `N₀` at which this inequality holds puts every larger length beyond the
largest root of Theorem 6.3's equation. -/
theorem laurent_root {ρ s N₀ N : ℝ} (hs : 1 ≤ s) (hN₀ : 0 < N₀) (hN : N₀ ≤ N)
    (h0 : Real.log (2 * s) + 28.161 * Real.log 3 *
        (max (Real.log ((1 + Real.log 2) / Real.log 3 * N₀) + 0.21) 14) ^ 2 ≤ ρ * N₀) :
    Real.log (2 * s) + 28.161 * Real.log 3 *
        (max (Real.log ((1 + Real.log 2) / Real.log 3 * N) + 0.21) 14) ^ 2 ≤ ρ * N := by
  obtain ⟨t, ht1, rfl⟩ : ∃ t : ℝ, 1 ≤ t ∧ N = N₀ * t :=
    ⟨N / N₀, by rw [le_div_iff₀ hN₀]; linarith, by rw [mul_comm, div_mul_cancel₀ N hN₀.ne']⟩
  have hl2 := log_two_pos'
  have hl3 := log_three_pos
  have hκ : 0 < (1 + Real.log 2) / Real.log 3 := div_pos (by linarith) hl3
  have hκN₀ : 0 < (1 + Real.log 2) / Real.log 3 * N₀ := mul_pos hκ hN₀
  have ht0 : 0 < t := by linarith
  have hlogN : Real.log ((1 + Real.log 2) / Real.log 3 * (N₀ * t)) =
      Real.log ((1 + Real.log 2) / Real.log 3 * N₀) + Real.log t := by
    rw [← mul_assoc, Real.log_mul hκN₀.ne' ht0.ne']
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hP14 : 14 ≤ max (Real.log ((1 + Real.log 2) / Real.log 3 * N₀) + 0.21) 14 :=
    le_max_right _ _
  have hmax : max (Real.log ((1 + Real.log 2) / Real.log 3 * (N₀ * t)) + 0.21) 14 ≤
      max (Real.log ((1 + Real.log 2) / Real.log 3 * N₀) + 0.21) 14 + Real.log t := by
    rw [hlogN]
    apply max_le
    · have := le_max_left (Real.log ((1 + Real.log 2) / Real.log 3 * N₀) + 0.21) 14
      linarith
    · linarith
  have hsq := sq_add_log_le (by linarith : (2 : ℝ) ≤
    max (Real.log ((1 + Real.log 2) / Real.log 3 * N₀) + 0.21) 14) ht1
  have hmax0 : 0 ≤ max (Real.log ((1 + Real.log 2) / Real.log 3 * (N₀ * t)) + 0.21) 14 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hsq2 := le_trans (pow_le_pow_left₀ hmax0 hmax 2) hsq
  have hC : 0 ≤ 28.161 * Real.log 3 := mul_nonneg (by norm_num) hl3.le
  have hlog2s : 0 ≤ Real.log (2 * s) := Real.log_nonneg (by linarith)
  have i1 := mul_le_mul_of_nonneg_left hsq2 hC
  have i2 := mul_le_mul_of_nonneg_right ht1 hlog2s
  have i3 := mul_le_mul_of_nonneg_left h0 ht0.le
  linarith

/-- The numerical check at Eliahou's bound, for two alternations and the rate `1/16`:
`log 4 + 28.161 · log 3 · (max(log(κ · 17087915) + 0.21, 14))² ≤ 17087915 / 16`. -/
theorem eliahou_check :
    Real.log (2 * 2) + 28.161 * Real.log 3 *
        (max (Real.log ((1 + Real.log 2) / Real.log 3 * 17087915) + 0.21) 14) ^ 2 ≤
      1 / 16 * 17087915 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := log_two_pos'
  have hl3 := log_three_lt
  have hl3' := one_lt_log_three
  have hκ : (1 + Real.log 2) / Real.log 3 ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hκ0 : 0 < (1 + Real.log 2) / Real.log 3 * 17087915 :=
    mul_pos (div_pos (by linarith) (by linarith)) (by norm_num)
  have hlog : Real.log ((1 + Real.log 2) / Real.log 3 * 17087915) ≤ 18 := by
    rw [Real.log_le_iff_le_exp hκ0]
    have he : (2.7 : ℝ) ^ 18 ≤ Real.exp 18 := by
      rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 18
    have h27 : (2 : ℝ) * 17087915 ≤ 2.7 ^ 18 := by norm_num
    linarith
  have hmax : max (Real.log ((1 + Real.log 2) / Real.log 3 * 17087915) + 0.21) 14 ≤ 18.21 :=
    max_le (by linarith) (by norm_num)
  have hmax0 : 0 ≤ max (Real.log ((1 + Real.log 2) / Real.log 3 * 17087915) + 0.21) 14 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hsq := pow_le_pow_left₀ hmax0 hmax 2
  have hlog4 : Real.log (2 * 2) < 1.3863 := by
    rw [Real.log_mul two_ne_zero two_ne_zero]; linarith
  have hC : 28.161 * Real.log 3 ≤ 28.161 * 1.099 := by linarith
  have := mul_le_mul hC hsq (sq_nonneg _) (by norm_num)
  linarith

end TwoBlock
