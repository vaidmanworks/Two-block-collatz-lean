import TwoBlock.Integrality

/-!
# Periodic stretches and repeats

Section 7 of the paper: Lemma 7.1 (the stretch congruence), Lemma 7.3 (repeats in a
cycle, with the cycle product) and Proposition 7.4 (repeats in any orbit; in print as Dubickas's
inequality, 2009).
-/

namespace TwoBlock

/-! ### Lemma 7.1 -/

/-- **Lemma 7.1 (the stretch congruence).** If an integer `x` is followed by `k` copies of `X`, then
`2^(nk)` divides `M_X x - c_X`. This holds on any orbit, not only on cycles. -/
theorem stretch_dvd {X : Word} {k : ℕ} {x : ℤ} (h : Follows x (wpow X k)) :
    (2 : ℤ) ^ (N X * k) ∣ M X * x - c X := by
  have hit := follows_iterate h
  rw [N_wpow, r_wpow, c_wpow] at hit
  have hg : (2 : ℤ) ^ (N X * k) - 3 ^ (r X * k) = M X * F X k := (M_mul_F X k).symm
  have key : (2 : ℤ) ^ (N X * k) * (M X * T^[N X * k] x - c X) =
      3 ^ (r X * k) * (M X * x - c X) := by
    linear_combination (M X) * hit - c X * hg
  exact (isCoprime_two_pow_three_pow _ _).dvd_of_dvd_mul_left ⟨_, key.symm⟩

/-- **Lemma 7.1, exact form.** If the cycle word read from `x` is `X^k W`, then
`M_w (c_X - M_X x) = 2^(nk) D(X, W)`. -/
theorem stretch_exact {X W : Word} {k : ℕ} {x : ℤ} (h : IsCycle x (wpow X k ++ W)) :
    M (wpow X k ++ W) * (c X - M X * x) = 2 ^ (N X * k) * D X W := by
  have hx := h.eq
  rw [c_append, M_append, c_wpow, M_wpow, N_wpow] at hx
  rw [M_append, M_wpow, N_wpow]
  unfold D
  linear_combination (-(M X)) * hx

/-- **Lemma 7.1, exact form.** `M_w` divides `D(X, W)`, so `D(X, W) / M_w` is an integer, and
`M_X x - c_X = -2^(nk) D(X, W) / M_w`. -/
theorem stretch_exact_dvd {X W : Word} {k : ℕ} {x : ℤ} (h : IsCycle x (wpow X k ++ W))
    (hN : 0 < N (wpow X k ++ W)) : M (wpow X k ++ W) ∣ D X W :=
  (isCoprime_M_two_pow hN _).dvd_of_dvd_mul_left ⟨_, (stretch_exact h).symm⟩

/-! ### Repeats -/

/-- Two integers that follow the same word are congruent modulo `2^N`. -/
theorem follows_dvd_sub {a b : ℤ} {w : Word} (ha : Follows a w) (hb : Follows b w) :
    (2 : ℤ) ^ N w ∣ a - b := by
  have h1 := follows_iterate ha
  have h2 := follows_iterate hb
  have key : 2 ^ N w * (T^[N w] a - T^[N w] b) = 3 ^ r w * (a - b) := by
    linear_combination h1 - h2
  exact (isCoprime_two_pow_three_pow _ _).dvd_of_dvd_mul_left ⟨_, key.symm⟩

/-- The next `L` parities of `x`. -/
def parities : ℤ → ℕ → Word
  | _, 0 => []
  | x, L + 1 => decide (x % 2 = 1) :: parities (T x) L

@[simp] theorem N_parities (x : ℤ) (L : ℕ) : N (parities x L) = L := by
  induction L generalizing x with
  | zero => rfl
  | succ L ih => simp [parities, ih]

theorem follows_parities (x : ℤ) (L : ℕ) : Follows x (parities x L) := by
  induction L generalizing x with
  | zero => trivial
  | succ L ih => exact ⟨by simp, ih (T x)⟩

/-- **Lemma 7.3 and Proposition 7.4, the congruence.** Distinct integers with the same next `L`
parities differ by at least `2^L`. -/
theorem two_pow_le_of_same_parities {a b : ℤ} {L : ℕ} (hne : a ≠ b)
    (hL : parities a L = parities b L) : (2 : ℤ) ^ L ≤ |a - b| := by
  have hd : (2 : ℤ) ^ L ∣ a - b := by
    have := follows_dvd_sub (a := a) (b := b) (follows_parities a L)
      (by rw [hL]; exact follows_parities b L)
    rwa [N_parities] at this
  exact Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs _ _).mpr hd)

theorem two_mul_T_add_one_le {x : ℤ} (hx : 0 < x) : 2 * (T x + 1) ≤ 3 * (x + 1) := by
  unfold T; split_ifs <;> omega

/-- Growth along an orbit: `x_(u+1) + 1 ≤ (3/2)(x_u + 1)` at every step. -/
theorem growth {x : ℤ} (hx : 0 < x) (u : ℕ) : 2 ^ u * (T^[u] x + 1) ≤ 3 ^ u * (x + 1) := by
  induction u generalizing x with
  | zero => simp
  | succ u ih =>
    rw [Function.iterate_succ_apply]
    have h1 := ih (T_pos hx)
    have h2 := two_mul_T_add_one_le hx
    have h3 : (0 : ℤ) ≤ 3 ^ u := by positivity
    calc 2 ^ (u + 1) * (T^[u] (T x) + 1) = 2 * (2 ^ u * (T^[u] (T x) + 1)) := by ring
      _ ≤ 2 * (3 ^ u * (T x + 1)) := by linarith
      _ = 3 ^ u * (2 * (T x + 1)) := by ring
      _ ≤ 3 ^ u * (3 * (x + 1)) := mul_le_mul_of_nonneg_left h2 h3
      _ = 3 ^ (u + 1) * (x + 1) := by ring

/-- **Proposition 7.4 (repeats in any orbit).** Let `x > 0` with orbit `x_0 = x, x_1, …`. If two
distinct points `x_s, x_t` (`s ≤ t`) have the same next `L` parities, then
`2^L ≤ |x_s - x_t|` and `|x_s - x_t| < (3/2)^t (x + 1)`. -/
theorem repeat_in_orbit {x : ℤ} (hx : 0 < x) {s t L : ℕ} (hst : s ≤ t)
    (hne : T^[s] x ≠ T^[t] x) (hL : parities (T^[s] x) L = parities (T^[t] x) L) :
    (2 : ℤ) ^ L ≤ |T^[s] x - T^[t] x| ∧ 2 ^ t * |T^[s] x - T^[t] x| < 3 ^ t * (x + 1) := by
  refine ⟨two_pow_le_of_same_parities hne hL, ?_⟩
  have ps := iterate_T_pos hx s
  have pt := iterate_T_pos hx t
  have h2t : (0 : ℤ) < 2 ^ t := by positivity
  have gs : 2 ^ t * (T^[s] x + 1) ≤ 3 ^ t * (x + 1) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
    have h23 : (2 : ℤ) ^ d ≤ 3 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have g := growth hx s
    have hx1 : (0 : ℤ) ≤ 3 ^ s * (x + 1) := mul_nonneg (by positivity) (by linarith)
    calc 2 ^ (s + d) * (T^[s] x + 1) = 2 ^ d * (2 ^ s * (T^[s] x + 1)) := by ring
      _ ≤ 2 ^ d * (3 ^ s * (x + 1)) := mul_le_mul_of_nonneg_left g (by positivity)
      _ ≤ 3 ^ d * (3 ^ s * (x + 1)) := mul_le_mul_of_nonneg_right h23 hx1
      _ = 3 ^ (s + d) * (x + 1) := by ring
  have gt := growth hx t
  rcases le_total (T^[t] x) (T^[s] x) with h | h
  · have habs : |T^[s] x - T^[t] x| < T^[s] x + 1 := by
      rw [abs_of_nonneg (by linarith)]; linarith
    calc 2 ^ t * |T^[s] x - T^[t] x| < 2 ^ t * (T^[s] x + 1) := mul_lt_mul_of_pos_left habs h2t
      _ ≤ 3 ^ t * (x + 1) := gs
  · have habs : |T^[s] x - T^[t] x| < T^[t] x + 1 := by
      rw [abs_of_nonpos (by linarith)]; linarith
    calc 2 ^ t * |T^[s] x - T^[t] x| < 2 ^ t * (T^[t] x + 1) := mul_lt_mul_of_pos_left habs h2t
      _ ≤ 3 ^ t * (x + 1) := gt

/-- **Proposition 7.4**, combined: `2^(L+t) < 3^t (x + 1)`, i.e.
`L < t log₂(3/2) + log₂(x + 1)`. -/
theorem repeat_in_orbit_bound {x : ℤ} (hx : 0 < x) {s t L : ℕ} (hst : s ≤ t)
    (hne : T^[s] x ≠ T^[t] x) (hL : parities (T^[s] x) L = parities (T^[t] x) L) :
    (2 : ℤ) ^ (L + t) < 3 ^ t * (x + 1) := by
  obtain ⟨h1, h2⟩ := repeat_in_orbit hx hst hne hL
  rw [pow_add]
  calc 2 ^ L * 2 ^ t ≤ |T^[s] x - T^[t] x| * 2 ^ t := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 ^ t * |T^[s] x - T^[t] x| := mul_comm _ _
    _ < 3 ^ t * (x + 1) := h2

/-! ### The cycle product -/

/-- The odd steps among the first `n` points of the orbit of `x`; on a cycle of length `n` their
number is `r`. -/
def oddSteps (x : ℤ) (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun t => T^[t] x % 2 = 1)

/-- `Λ = n log 2 - r log 3` for the first `n` steps of the orbit of `x`. -/
noncomputable def Lambda (x : ℤ) (n : ℕ) : ℝ := n * Real.log 2 - (oddSteps x n).card * Real.log 3

theorem log_odd_step {z : ℝ} (hz : 0 < z) :
    Real.log ((3 * z + 1) / 2) - Real.log z =
      -Real.log 2 + (Real.log 3 + Real.log (1 + 1 / (3 * z))) := by
  have h3z : 0 < 3 * z := mul_pos three_pos hz
  have hpos : 0 < 1 + 1 / (3 * z) := add_pos one_pos (one_div_pos.mpr h3z)
  have h1 : (3 * z + 1) / 2 = 3 * z * (1 + 1 / (3 * z)) / 2 := by
    rw [mul_add, mul_one, mul_one_div_cancel h3z.ne']
  rw [h1, Real.log_div (mul_pos h3z hpos).ne' (by norm_num), Real.log_mul h3z.ne' hpos.ne',
    Real.log_mul (by norm_num) hz.ne']
  ring

theorem log_step {x : ℤ} (hx : 0 < x) (t : ℕ) :
    Real.log ((T^[t + 1] x : ℤ) : ℝ) - Real.log ((T^[t] x : ℤ) : ℝ) =
      -Real.log 2 + (if T^[t] x % 2 = 1 then
        Real.log 3 + Real.log (1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ))) else 0) := by
  have hz : (0 : ℝ) < ((T^[t] x : ℤ) : ℝ) := by exact_mod_cast iterate_T_pos hx t
  rw [Function.iterate_succ_apply']
  split_ifs with h
  · have h2 := two_mul_T_of_odd h
    have h2' : ((T (T^[t] x) : ℤ) : ℝ) = (3 * ((T^[t] x : ℤ) : ℝ) + 1) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
      have : T (T^[t] x) * 2 = 3 * T^[t] x + 1 := by linarith
      exact_mod_cast this
    rw [h2']
    exact log_odd_step hz
  · have h2 := two_mul_T_of_even (by omega : T^[t] x % 2 = 0)
    have h2' : ((T (T^[t] x) : ℤ) : ℝ) = ((T^[t] x : ℤ) : ℝ) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
      have : T (T^[t] x) * 2 = T^[t] x := by linarith
      exact_mod_cast this
    rw [h2', Real.log_div hz.ne' (by norm_num)]
    ring

/-- **The cycle product.** On a positive cycle of length `n`,
`n log 2 - r log 3 = Σ_(odd t) log(1 + 1/(3 x_t))`. -/
theorem cycle_product {x : ℤ} (hx : 0 < x) {n : ℕ} (hc : T^[n] x = x) :
    Lambda x n = ∑ t ∈ oddSteps x n, Real.log (1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ))) := by
  have hsum := Finset.sum_range_sub (fun t => Real.log ((T^[t] x : ℤ) : ℝ)) n
  simp only [hc, Function.iterate_zero_apply, sub_self] at hsum
  simp only [log_step hx] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_filter, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  unfold Lambda oddSteps
  linarith

theorem log_one_add_pos {z : ℝ} (hz : 0 < z) : 0 < Real.log (1 + 1 / (3 * z)) :=
  Real.log_pos (by have := one_div_pos.mpr (mul_pos three_pos hz); linarith)

/-- `Λ > 0` on a positive cycle. -/
theorem Lambda_pos {x : ℤ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (hc : T^[n] x = x) :
    0 < Lambda x n := by
  rcases (oddSteps x n).eq_empty_or_nonempty with he | hne
  · exfalso
    have h := cycle_product hx hc
    rw [he, Finset.sum_empty] at h
    unfold Lambda at h
    rw [he, Finset.card_empty, Nat.cast_zero, zero_mul, sub_zero] at h
    have : (0 : ℝ) < n * Real.log 2 := mul_pos (by exact_mod_cast hn) (Real.log_pos (by norm_num))
    linarith
  · rw [cycle_product hx hc]
    exact Finset.sum_pos
      (fun t _ => log_one_add_pos (by exact_mod_cast iterate_T_pos hx t)) hne

/-- `3 Λ x_min ≤ r`: every term of the cycle product is at most `1/(3 x_min)`. -/
theorem Lambda_min_bound {x : ℤ} (hx : 0 < x) {n : ℕ} (hc : T^[n] x = x) {m : ℤ} (hm0 : 0 < m)
    (hm : ∀ t < n, m ≤ T^[t] x) : 3 * Lambda x n * m ≤ (oddSteps x n).card := by
  rw [cycle_product hx hc]
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have h3m : (0 : ℝ) < 3 * m := by linarith
  have hle : ∀ t ∈ oddSteps x n,
      Real.log (1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ))) ≤ 1 / (3 * (m : ℝ)) := by
    intro t ht
    have htn : t < n := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have hmt : (m : ℝ) ≤ ((T^[t] x : ℤ) : ℝ) := by exact_mod_cast hm t htn
    have hz : (0 : ℝ) < ((T^[t] x : ℤ) : ℝ) := by linarith
    have hpos : 0 < 1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ)) :=
      add_pos one_pos (one_div_pos.mpr (mul_pos three_pos hz))
    calc Real.log (1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ)))
        ≤ 1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ)) - 1 := Real.log_le_sub_one_of_pos hpos
      _ = 1 / (3 * ((T^[t] x : ℤ) : ℝ)) := by ring
      _ ≤ 1 / (3 * (m : ℝ)) := one_div_le_one_div_of_le h3m (by linarith)
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  calc 3 * (∑ t ∈ oddSteps x n, Real.log (1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ)))) * m
      = (∑ t ∈ oddSteps x n, Real.log (1 + 1 / (3 * ((T^[t] x : ℤ) : ℝ)))) * (3 * m) := by ring
    _ ≤ ((oddSteps x n).card * (1 / (3 * (m : ℝ)))) * (3 * m) :=
        mul_le_mul_of_nonneg_right hsum h3m.le
    _ = (oddSteps x n).card := by rw [mul_assoc, one_div_mul_cancel h3m.ne', mul_one]

/-- **Lemma 7.3 (repeats in a cycle).** Let `x > 0` lie on a cycle of length `n` with minimum at least
`m > 0`. If two distinct points `x_s, x_t` have the same next `L` parities, then
`2^L ≤ |x_s - x_t|`, and `2^L · 3 Λ m < max(x_s, x_t) · r`; that is,
`L ln 2 < ln(max(x_s, x_t)/m) + ln(r/3) - ln Λ`. -/
theorem cycle_repeat {x : ℤ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) (hc : T^[n] x = x) {m : ℤ}
    (hm0 : 0 < m) (hm : ∀ t < n, m ≤ T^[t] x) {s t L : ℕ} (hne : T^[s] x ≠ T^[t] x)
    (hL : parities (T^[s] x) L = parities (T^[t] x) L) :
    (2 : ℤ) ^ L ≤ |T^[s] x - T^[t] x| ∧
      (2 : ℝ) ^ L * (3 * Lambda x n * m) <
        max ((T^[s] x : ℤ) : ℝ) ((T^[t] x : ℤ) : ℝ) * (oddSteps x n).card := by
  have h1 := two_pow_le_of_same_parities hne hL
  refine ⟨h1, ?_⟩
  have hΛ := Lambda_pos hx hn hc
  have hb := Lambda_min_bound hx hc hm0 hm
  have ps := iterate_T_pos hx s
  have pt := iterate_T_pos hx t
  have hmax : |T^[s] x - T^[t] x| < max (T^[s] x) (T^[t] x) := by
    rcases le_total (T^[t] x) (T^[s] x) with h | h
    · rw [abs_of_nonneg (by linarith), max_eq_left h]; linarith
    · rw [abs_of_nonpos (by linarith), max_eq_right h]; linarith
  have h2r : (2 : ℝ) ^ L < max ((T^[s] x : ℤ) : ℝ) ((T^[t] x : ℤ) : ℝ) := by
    exact_mod_cast lt_of_le_of_lt h1 hmax
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hpos : 0 < 3 * Lambda x n * m := mul_pos (mul_pos three_pos hΛ) hm0'
  have hmax0 : (0 : ℝ) ≤ max ((T^[s] x : ℤ) : ℝ) ((T^[t] x : ℤ) : ℝ) :=
    le_trans (by exact_mod_cast ps.le) (le_max_left _ _)
  calc (2 : ℝ) ^ L * (3 * Lambda x n * m)
      < max ((T^[s] x : ℤ) : ℝ) ((T^[t] x : ℤ) : ℝ) * (3 * Lambda x n * m) :=
        mul_lt_mul_of_pos_right h2r hpos
    _ ≤ max ((T^[s] x : ℤ) : ℝ) ((T^[t] x : ℤ) : ℝ) * (oddSteps x n).card :=
        mul_le_mul_of_nonneg_left hb hmax0

end TwoBlock
