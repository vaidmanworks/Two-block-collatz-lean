import TwoBlock.SeveralAlternations

/-!
# Deep pairs by Baker alone: Theorem 6.5

Section 6 of the paper. For a pair `(u, v)` on the path of `log₂ 3` with
`n + n' ≥ 2.5 · 10^5` and `s ≤ K/2`, `K = min(n a', a n')`, no word with `s` alternations over the
pair is the parity vector of a positive integer cycle. The only input is Laurent's bound: no
verification and no cycle-length bound. (The proof excludes the trivial cycle as well, so the
conclusion is `False`.)

The proof follows the paper. A word with `s` alternations has `N ≥ s (n + n')`; by Lemma 6.4 the
combined rate is at least `log 2 / (4s)`; and since `s ≤ K/2 ≤ (n + n')²/8`, Theorem 6.3's
inequality fails at `N = s (n + n')`, hence (`laurent_root`) at every larger `N`. The numerical check
at `n + n' = 2.5 · 10^5` uses `log(m³/4) ≤ 36` in place of the paper's `3 log m - 1.4368`, which
`κ = (1 + log 2)/log 3 ≤ 2` gives without a sharp bound on `log 3`.
-/

namespace TwoBlock

/-- The combined rate of two rates that both exceed `p > 0` is at least `p/2`. -/
theorem combinedRate_ge_half {ρ₁ ρ₂ p : ℝ} (hp : 0 < p) (h1 : p ≤ ρ₁) (h2 : p ≤ ρ₂) :
    p / 2 ≤ combinedRate ρ₁ ρ₂ := by
  unfold combinedRate
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ ρ₁),
    mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ ρ₂)]

/-- `(P + c log t)² ≤ t P²` for `t ≥ 1`, `c ≥ 0` and `P ≥ 2c`, since `log t ≤ 2 (√t - 1)`. -/
theorem sq_add_mul_log_le {P c t : ℝ} (hc : 0 ≤ c) (hP : 2 * c ≤ P) (ht : 1 ≤ t) :
    (P + c * Real.log t) ^ 2 ≤ t * P ^ 2 := by
  have hs1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hs1)
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 := mul_le_mul_of_nonneg_left hlog hc
  have h2 := mul_le_mul_of_nonneg_right hP (sub_nonneg.mpr hs1)
  have key : P + c * Real.log t ≤ P * Real.sqrt t := by linarith
  have h0 : 0 ≤ P + c * Real.log t := by
    have := mul_nonneg hc hlog0
    linarith
  calc (P + c * Real.log t) ^ 2 ≤ (P * Real.sqrt t) ^ 2 := pow_le_pow_left₀ h0 key 2
    _ = t * P ^ 2 := by rw [mul_pow, hsq]; ring

/-- The numerical check of Theorem 6.5: for `m ≥ 2.5 · 10^5`,
`log(m²/4) + 28.161 · log 3 · (max(log(m³/4) + 0.21, 14))² ≤ (log 2 / 4) m`. -/
theorem deep_check {m : ℝ} (hm : 250000 ≤ m) :
    Real.log (m ^ 2 / 4) + 28.161 * Real.log 3 * (max (Real.log (m ^ 3 / 4) + 0.21) 14) ^ 2 ≤
      Real.log 2 / 4 * m := by
  obtain ⟨t, ht1, rfl⟩ : ∃ t : ℝ, 1 ≤ t ∧ m = 250000 * t :=
    ⟨m / 250000, by rw [le_div_iff₀ (by norm_num)]; linarith, by ring⟩
  have ht0 : 0 < t := by linarith
  have e2 : (250000 * t) ^ 2 / 4 = 250000 ^ 2 / 4 * t ^ 2 := by ring
  have e3 : (250000 * t) ^ 3 / 4 = 250000 ^ 3 / 4 * t ^ 3 := by ring
  have hl2 : Real.log ((250000 * t) ^ 2 / 4) = Real.log (250000 ^ 2 / 4) + 2 * Real.log t := by
    rw [e2, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have hl3 : Real.log ((250000 * t) ^ 3 / 4) = Real.log (250000 ^ 3 / 4) + 3 * Real.log t := by
    rw [e3, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hb2 : Real.log ((250000 : ℝ) ^ 2 / 4) ≤ 24 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have : (2.718 : ℝ) ^ 24 ≤ Real.exp 24 := by
      rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) he1 24
    have h : (250000 : ℝ) ^ 2 / 4 ≤ 2.718 ^ 24 := by norm_num
    linarith
  have hb3 : Real.log ((250000 : ℝ) ^ 3 / 4) ≤ 36 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have : (2.718 : ℝ) ^ 36 ≤ Real.exp 36 := by
      rw [show (36 : ℝ) = ((36 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) he1 36
    have h : (250000 : ℝ) ^ 3 / 4 ≤ 2.718 ^ 36 := by norm_num
    linarith
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlt1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
  have hP14 : 14 ≤ max (Real.log ((250000 : ℝ) ^ 3 / 4) + 0.21) 14 := le_max_right _ _
  have hP : max (Real.log ((250000 : ℝ) ^ 3 / 4) + 0.21) 14 ≤ 36.21 :=
    max_le (by linarith) (by norm_num)
  have hmax : max (Real.log ((250000 * t) ^ 3 / 4) + 0.21) 14 ≤
      max (Real.log ((250000 : ℝ) ^ 3 / 4) + 0.21) 14 + 3 * Real.log t := by
    rw [hl3]
    apply max_le
    · have := le_max_left (Real.log ((250000 : ℝ) ^ 3 / 4) + 0.21) 14
      linarith
    · linarith
  have hmax0 : 0 ≤ max (Real.log ((250000 * t) ^ 3 / 4) + 0.21) 14 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hsq := le_trans (pow_le_pow_left₀ hmax0 hmax 2)
    (sq_add_mul_log_le (by norm_num : (0 : ℝ) ≤ 3) (by linarith) ht1)
  have hP2 : (max (Real.log ((250000 : ℝ) ^ 3 / 4) + 0.21) 14) ^ 2 ≤ 36.21 ^ 2 :=
    pow_le_pow_left₀ (by linarith) hP 2
  have hl3' := log_three_lt
  have hl2' := Real.log_two_gt_d9
  have hC : 28.161 * Real.log 3 ≤ 28.161 * 1.099 := by linarith
  have hC0 : 0 ≤ 28.161 * Real.log 3 := mul_nonneg (by norm_num) log_three_pos.le
  have i1 := mul_le_mul_of_nonneg_left hsq hC0
  have i2 := mul_le_mul hC hP2 (sq_nonneg _) (by norm_num)
  have i3 := mul_le_mul_of_nonneg_left i2 ht0.le
  have i4 := mul_le_mul_of_nonneg_right hl2'.le ht0.le
  rw [hl2]
  linarith

/-- **Theorem 6.5 (deep pairs, by Baker alone).** Let `(u, v)` be a pair on the path of `log₂ 3`
(`u` falling of type `(n', a')`, `v` rising of type `(n, a)`) with `n + n' ≥ 2.5 · 10^5`, and let
`1 ≤ s ≤ K/2`, `K = min(n a', a n')`. Then no word `v^(k_1) u^(l_1) ⋯ v^(k_s) u^(l_s)` is the parity
vector of a positive integer cycle. Input: Laurent's bound only. -/
theorem deep_pairs {d : ℕ} {u v : Word} (hp : OnPath d u v) (hL : LaurentBound)
    (hsize : 250000 ≤ N v + N u) {e : List (ℕ × ℕ)} (hne : e ≠ [])
    (hsK : 2 * e.length ≤ min (N v * r u) (r v * N u)) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt v u e)) : False := by
  have hs : 0 < e.length := List.length_pos_iff.mpr hne
  have hK2 : 2 ≤ min (N v * r u) (r v * N u) := le_trans (by omega) hsK
  have hru : 0 < r u := by
    by_contra h0
    push_neg at h0
    have h00 : r u = 0 := by omega
    rw [h00, mul_zero] at hK2
    simp at hK2
  -- the rates, by Lemma 6.4
  obtain ⟨hX, hY⟩ := hp.rates_gt hru hs
  have hsR : (0 : ℝ) < e.length := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ e.length := by exact_mod_cast hs
  have hl2 := log_two_pos'
  have hKR : (2 * e.length : ℝ) ≤ ((min (N v * r u) (r v * N u) : ℕ) : ℝ) := by exact_mod_cast hsK
  have hKpos : (0 : ℝ) < ((min (N v * r u) (r v * N u) : ℕ) : ℝ) := by linarith
  have hinv : 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ) ≤ 1 / (2 * e.length) :=
    one_div_le_one_div_of_le (by linarith) hKR
  have hq : 1 / (2 * (e.length : ℝ)) = 1 / e.length / 2 := by rw [div_div, mul_comm]
  have hdiff : 1 / (2 * (e.length : ℝ)) ≤
      1 / e.length - 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ) := by
    rw [hq] at hinv ⊢; linarith
  have hp0 : Real.log 2 * (1 / (2 * e.length)) ≤
      Real.log 2 * (1 / e.length - 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiff hl2.le
  have hp_pos : 0 < Real.log 2 * (1 / (2 * e.length)) :=
    mul_pos hl2 (one_div_pos.mpr (by linarith))
  have h1 : 0 < rateX e.length (N v) (r v) := by linarith
  have h2 : 0 < rateY e.length (N u) (r u) := by linarith
  have hρ := combinedRate_ge_half hp_pos (by linarith) (by linarith) (ρ₁ := rateX e.length (N v) (r v))
    (ρ₂ := rateY e.length (N u) (r u))
  -- Theorem 6.3
  have main := s_alternations_laurent hp.1.unimodular.symm hp.2.2 hp.2.1 hne he h1 h2 hL hx h
  -- the length: `N ≥ s (n + n')`
  have hSK := length_le_sumK he
  have hSL := length_le_sumL he
  have hNlen : e.length * (N v + N u) ≤ N (alt v u e) := by
    rw [N_alt]
    have a1 : N v * e.length ≤ N v * sumK e := Nat.mul_le_mul le_rfl hSK
    have a2 : N u * e.length ≤ N u * sumL e := Nat.mul_le_mul le_rfl hSL
    linarith
  have hmR : (250000 : ℝ) ≤ ((N v + N u : ℕ) : ℝ) := by exact_mod_cast hsize
  have hm0 : (0 : ℝ) < ((N v + N u : ℕ) : ℝ) := by linarith
  have hN₀ : (0 : ℝ) < e.length * ((N v + N u : ℕ) : ℝ) := mul_pos hsR hm0
  have hNR : (e.length : ℝ) * ((N v + N u : ℕ) : ℝ) ≤ N (alt v u e) := by exact_mod_cast hNlen
  -- `2s ≤ K ≤ n a' ≤ n n' ≤ (n + n')² / 4`
  have hru' : (r u : ℝ) ≤ N u := by exact_mod_cast r_le_N u
  have hK1 : ((min (N v * r u) (r v * N u) : ℕ) : ℝ) ≤ (N v : ℝ) * r u := by
    have : min (N v * r u) (r v * N u) ≤ N v * r u := min_le_left _ _
    exact_mod_cast this
  have hNv0 : (0 : ℝ) ≤ N v := Nat.cast_nonneg _
  have hNu0 : (0 : ℝ) ≤ N u := Nat.cast_nonneg _
  have hs2 : (2 * e.length : ℝ) ≤ ((N v + N u : ℕ) : ℝ) ^ 2 / 4 := by
    push_cast
    have b1 := mul_le_mul_of_nonneg_left hru' hNv0
    have b2 := sq_nonneg ((N v : ℝ) - N u)
    linarith
  -- the inequality at `N₀ = s (n + n')`
  have hκ : (1 + Real.log 2) / Real.log 3 ≤ 2 := by
    rw [div_le_iff₀ log_three_pos]; linarith [Real.log_two_lt_d9, one_lt_log_three]
  have hκ0 : 0 < (1 + Real.log 2) / Real.log 3 := div_pos (by linarith) log_three_pos
  have hκN : (1 + Real.log 2) / Real.log 3 * (e.length * ((N v + N u : ℕ) : ℝ)) ≤
      ((N v + N u : ℕ) : ℝ) ^ 3 / 4 := by
    have a1 := mul_le_mul_of_nonneg_right hκ hN₀.le
    have a2 := mul_le_mul_of_nonneg_right hs2 hm0.le
    linarith
  have hlogκ := Real.log_le_log (mul_pos hκ0 hN₀) hκN
  have hlog2s : Real.log (2 * e.length) ≤ Real.log (((N v + N u : ℕ) : ℝ) ^ 2 / 4) :=
    Real.log_le_log (by linarith) hs2
  have hmaxle : max (Real.log ((1 + Real.log 2) / Real.log 3 * (e.length * ((N v + N u : ℕ) : ℝ))) +
      0.21) 14 ≤ max (Real.log (((N v + N u : ℕ) : ℝ) ^ 3 / 4) + 0.21) 14 :=
    max_le_max (by linarith) le_rfl
  have hmaxle0 : (0 : ℝ) ≤ max (Real.log ((1 + Real.log 2) / Real.log 3 *
      (e.length * ((N v + N u : ℕ) : ℝ))) + 0.21) 14 :=
    le_trans (by norm_num) (le_max_right _ _)
  have hmaxle2 := pow_le_pow_left₀ hmaxle0 hmaxle 2
  have hC0 : 0 ≤ 28.161 * Real.log 3 := mul_nonneg (by norm_num) log_three_pos.le
  have hcheck := deep_check hmR
  have hρN : Real.log 2 / 4 * ((N v + N u : ℕ) : ℝ) ≤
      combinedRate (rateX e.length (N v) (r v)) (rateY e.length (N u) (r u)) *
        (e.length * ((N v + N u : ℕ) : ℝ)) := by
    have a1 := mul_le_mul_of_nonneg_right hρ hN₀.le
    have hs0 : (e.length : ℝ) ≠ 0 := hsR.ne'
    have a2 : Real.log 2 * (1 / (2 * e.length)) / 2 * (e.length * ((N v + N u : ℕ) : ℝ)) =
        Real.log 2 / 4 * ((N v + N u : ℕ) : ℝ) := by
      field_simp
      try ring
    linarith
  have h0 : Real.log (2 * e.length) + 28.161 * Real.log 3 *
      (max (Real.log ((1 + Real.log 2) / Real.log 3 * (e.length * ((N v + N u : ℕ) : ℝ))) + 0.21)
        14) ^ 2 ≤
      combinedRate (rateX e.length (N v) (r v)) (rateY e.length (N u) (r u)) *
        (e.length * ((N v + N u : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hmaxle2 hC0
    linarith
  have root := laurent_root (N := (N (alt v u e) : ℝ)) hs1 hN₀ hNR h0
  linarith

end TwoBlock
