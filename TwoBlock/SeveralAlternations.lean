import TwoBlock.Alternations
import TwoBlock.CitedBounds

/-!
# Several alternations: Theorems 6.2 and 6.3, Lemma 6.4

Section 6 of the paper. Throughout, `(X, Y)` is unimodular with `M_X < 0 < M_Y`, and
`alt X Y e` is a word with `s = e.length` alternations (`TwoBlock.Alternations`).

* `s_alternations` is Theorem 6.3's bound `M_w / 2^N < s e^(-ρ N)`, with `ρ` the combined rate.
* `s_alternations_laurent` is its consequence under Laurent's bound: the length lies below the largest
  root of `ρ N = log(2s) + 28.161 · log 3 · (max(log(κ N) + 0.21, 14))²`, `κ = (1 + log 2) / log 3`.
  `s_alternations_rhin` is the same with Rhin's measure in the Simons–de Weger form.
* `s_alternations_excluded`: no such cycle when a cycle-length bound lies beyond that root.
* `two_alternations` is Theorem 6.2, and `two_alternations_path` its case of the path pairs from
  depth 1 on.
* `OnPath.rates_gt` is Lemma 6.4, and `pathK_lt_left`, `pathK_lt_right` say that `K` increases.
-/

namespace TwoBlock

/-! ### The rates -/

/-- The first rate of Theorem 6.3, for a rising block of type `(n, a)` and `s` alternations:
`log 2 - ((s - 1)/s) (a/n) log 3`. -/
noncomputable def rateX (s n a : ℕ) : ℝ :=
  Real.log 2 - ((s - 1 : ℝ) / s) * ((a : ℝ) / n) * Real.log 3

/-- The second rate of Theorem 6.3, for a falling block of type `(n', a')` and `s` alternations:
`(a'/n') log 3 - ((s - 1)/s) log 2`. -/
noncomputable def rateY (s n a : ℕ) : ℝ :=
  ((a : ℝ) / n) * Real.log 3 - ((s - 1 : ℝ) / s) * Real.log 2

/-- The combined rate of Theorem 6.3: the product of the two rates divided by their sum. -/
noncomputable def combinedRate (ρ₁ ρ₂ : ℝ) : ℝ := ρ₁ * ρ₂ / (ρ₁ + ρ₂)

/-- The first bracket in logarithmic form: `log(M_w / 2^N) < log s - ρ₁ · (X-length)`, since
`s n K ≥ X-length`. -/
theorem log_bracket_X {m : ℝ} {s n a K S Nw : ℕ} (hm : 0 < m) (hs : 0 < s) (hn : 0 < n)
    (hρ : 0 < rateX s n a) (hS : S ≤ s * K)
    (h : m * 2 ^ (n * s * K) < s * 2 ^ Nw * 3 ^ (a * (s - 1) * K)) :
    Real.log (m / 2 ^ Nw) < Real.log s - rateX s n a * (n * S) := by
  have h2N : (0 : ℝ) < 2 ^ Nw := by positivity
  have h2 : (0 : ℝ) < 2 ^ (n * s * K) := by positivity
  have h3 : (0 : ℝ) < 3 ^ (a * (s - 1) * K) := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : m / 2 ^ Nw < s * 3 ^ (a * (s - 1) * K) / 2 ^ (n * s * K) := by
    rw [div_lt_div_iff₀ h2N h2]; linarith
  have hcast : ((a * (s - 1) * K : ℕ) : ℝ) = a * ((s : ℝ) - 1) * K := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]; push_cast; ring
  have hval : Real.log (s * 3 ^ (a * (s - 1) * K) / 2 ^ (n * s * K)) =
      Real.log s + a * ((s : ℝ) - 1) * K * Real.log 3 - n * s * K * Real.log 2 := by
    rw [Real.log_div (mul_pos hsR h3).ne' h2.ne', Real.log_mul hsR.ne' h3.ne', Real.log_pow,
      Real.log_pow, hcast]
    push_cast; ring
  have hlog := Real.log_lt_log (div_pos hm h2N) hlt
  rw [hval] at hlog
  have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hrate : (n : ℝ) * s * rateX s n a =
      n * s * Real.log 2 - a * ((s : ℝ) - 1) * Real.log 3 := by
    unfold rateX; field_simp
  have hrateK : (K : ℝ) * ((n : ℝ) * s * rateX s n a) =
      K * (n * s * Real.log 2 - a * ((s : ℝ) - 1) * Real.log 3) := by rw [hrate]
  have hSK : (n : ℝ) * rateX s n a * S ≤ n * rateX s n a * (s * K) := by
    have : (S : ℝ) ≤ s * K := by exact_mod_cast hS
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hnR.le hρ.le)
  linarith

/-- The second bracket in logarithmic form: `log(M_w / 2^N) < log s - ρ₂ · (Y-length)`. -/
theorem log_bracket_Y {m : ℝ} {s n a L T Nw : ℕ} (hm : 0 < m) (hs : 0 < s) (hn : 0 < n)
    (hρ : 0 < rateY s n a) (hT : T ≤ s * L)
    (h : m * 3 ^ (a * s * L) < s * 2 ^ Nw * 2 ^ (n * (s - 1) * L)) :
    Real.log (m / 2 ^ Nw) < Real.log s - rateY s n a * (n * T) := by
  have h2N : (0 : ℝ) < 2 ^ Nw := by positivity
  have h3 : (0 : ℝ) < 3 ^ (a * s * L) := by positivity
  have h2 : (0 : ℝ) < 2 ^ (n * (s - 1) * L) := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : m / 2 ^ Nw < s * 2 ^ (n * (s - 1) * L) / 3 ^ (a * s * L) := by
    rw [div_lt_div_iff₀ h2N h3]; linarith
  have hcast : ((n * (s - 1) * L : ℕ) : ℝ) = n * ((s : ℝ) - 1) * L := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]; push_cast; ring
  have hval : Real.log (s * 2 ^ (n * (s - 1) * L) / 3 ^ (a * s * L)) =
      Real.log s + n * ((s : ℝ) - 1) * L * Real.log 2 - a * s * L * Real.log 3 := by
    rw [Real.log_div (mul_pos hsR h2).ne' h3.ne', Real.log_mul hsR.ne' h2.ne', Real.log_pow,
      Real.log_pow, hcast]
    push_cast; ring
  have hlog := Real.log_lt_log (div_pos hm h2N) hlt
  rw [hval] at hlog
  have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hrate : (n : ℝ) * s * rateY s n a =
      a * s * Real.log 3 - n * ((s : ℝ) - 1) * Real.log 2 := by
    unfold rateY; field_simp
  have hrateL : (L : ℝ) * ((n : ℝ) * s * rateY s n a) =
      L * (a * s * Real.log 3 - n * ((s : ℝ) - 1) * Real.log 2) := by rw [hrate]
  have hTL : (n : ℝ) * rateY s n a * T ≤ n * rateY s n a * (s * L) := by
    have : (T : ℝ) ≤ s * L := by exact_mod_cast hT
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hnR.le hρ.le)
  linarith

/-- The worst split: `ρ (A + B) ≤ max(ρ₁ A, ρ₂ B)` for the combined rate `ρ`. -/
theorem combine_rates {ρ₁ ρ₂ A B : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) :
    combinedRate ρ₁ ρ₂ * (A + B) ≤ max (ρ₁ * A) (ρ₂ * B) := by
  unfold combinedRate
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have m1 := mul_le_mul_of_nonneg_left (le_max_left (ρ₁ * A) (ρ₂ * B)) h2.le
  have m2 := mul_le_mul_of_nonneg_left (le_max_right (ρ₁ * A) (ρ₂ * B)) h1.le
  linarith

/-- The lower bound: `M_w / 2^N ≥ Λ / (1 + Λ)` for `Λ = N log 2 - r log 3 > 0`, since
`2^N / 3^r = e^Λ ≥ 1 + Λ`. -/
theorem M_div_two_pow_ge (w : Word) (hΛ : 0 < (N w : ℝ) * Real.log 2 - r w * Real.log 3) :
    ((N w : ℝ) * Real.log 2 - r w * Real.log 3) /
        (1 + ((N w : ℝ) * Real.log 2 - r w * Real.log 3)) ≤
      ((M w : ℤ) : ℝ) / 2 ^ N w := by
  have h2 : Real.exp ((N w : ℝ) * Real.log 2) = 2 ^ N w := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have h3 : Real.exp ((r w : ℝ) * Real.log 3) = 3 ^ r w := by
    rw [Real.exp_nat_mul, Real.exp_log three_pos]
  have hexp := Real.add_one_le_exp ((N w : ℝ) * Real.log 2 - r w * Real.log 3)
  rw [Real.exp_sub, h2, h3, le_div_iff₀ (by positivity)] at hexp
  have hM : ((M w : ℤ) : ℝ) = 2 ^ N w - 3 ^ r w := by unfold M; push_cast; ring
  rw [div_le_div_iff₀ (by linarith) (by positivity), hM]
  nlinarith

/-- From the bracket to the length: if `Λ / (1 + Λ) ≤ y < s e^(-t)`, then
`t < log(2s) + max(-log Λ, 0)`. (If `Λ ≤ 1`, `y ≥ Λ/2`; otherwise `y > 1/2`.) -/
theorem rate_of_bracket {y s Λ t : ℝ} (hΛ : 0 < Λ) (hs : 0 < s) (hy : Λ / (1 + Λ) ≤ y)
    (h : y < s * Real.exp (-t)) : t < Real.log (2 * s) + max (-Real.log Λ) 0 := by
  have hy0 : 0 < y := lt_of_lt_of_le (div_pos hΛ (by linarith)) hy
  have hlog : Real.log y < Real.log s - t := by
    have := Real.log_lt_log hy0 h
    rwa [Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
  have h2s : Real.log (2 * s) = Real.log 2 + Real.log s := Real.log_mul two_ne_zero hs.ne'
  rcases le_or_gt Λ 1 with h1 | h1
  · have hle : Λ / 2 ≤ y := by
      refine le_trans ?_ hy
      rw [div_le_div_iff₀ two_pos (by linarith)]
      nlinarith
    have hl := Real.log_le_log (div_pos hΛ two_pos) hle
    rw [Real.log_div hΛ.ne' two_ne_zero] at hl
    have := le_max_left (-Real.log Λ) 0
    linarith
  · have hle : 1 / 2 < y := by
      refine lt_of_lt_of_le ?_ hy
      rw [div_lt_div_iff₀ two_pos (by linarith)]
      linarith
    have hl := Real.log_lt_log (by norm_num) hle
    rw [one_div, Real.log_inv] at hl
    have := le_max_right (-Real.log Λ) 0
    linarith

/-! ### Theorem 6.3 -/

theorem N_alt_pos {X Y : Word} (hX : M X < 0) {e : List (ℕ × ℕ)} (hne : e ≠ [])
    (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) : 0 < N (alt X Y e) := by
  have hNX : 0 < N X := lt_of_lt_of_le (r_pos_of_M_neg hX) (r_le_N X)
  have hs : 0 < e.length := List.length_pos_iff.mpr hne
  have hSK := length_le_sumK he
  rw [N_alt]
  have := Nat.mul_pos hNX (lt_of_lt_of_le hs hSK)
  omega

theorem r_alt_pos {X Y : Word} (hX : M X < 0) {e : List (ℕ × ℕ)} (hne : e ≠ [])
    (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) : 0 < r (alt X Y e) := by
  have hrX := r_pos_of_M_neg hX
  have hs : 0 < e.length := List.length_pos_iff.mpr hne
  have hSK := length_le_sumK he
  rw [r_alt]
  have := Nat.mul_pos hrX (lt_of_lt_of_le hs hSK)
  omega

/-- **Theorem 6.3 (`s` alternations), the bound.** Let `(X, Y)` be unimodular with `M_X < 0 < M_Y`,
let `s ≥ 1`, and suppose both rates are positive. If a positive integer cycle reads a word with `s`
alternations over `(X, Y)` from `x`, then `M_w / 2^N < s e^(-ρ N)`, with `ρ` the combined rate. -/
theorem s_alternations {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (hne : e ≠ []) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    (h1 : 0 < rateX e.length (N X) (r X)) (h2 : 0 < rateY e.length (N Y) (r Y))
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt X Y e)) :
    ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e) <
      e.length * Real.exp (-(combinedRate (rateX e.length (N X) (r X))
        (rateY e.length (N Y) (r Y)) * N (alt X Y e))) := by
  obtain ⟨⟨K, l⟩, hKl, hKmax⟩ := exists_max_run hne Prod.fst
  obtain ⟨⟨k, L⟩, hkL, hLmax⟩ := exists_max_run hne Prod.snd
  have hKmax' : ∀ q ∈ e, q.1 ≤ K := hKmax
  have hLmax' : ∀ q ∈ e, q.2 ≤ L := hLmax
  have hs : 0 < e.length := List.length_pos_iff.mpr hne
  have hNX : 0 < N X := lt_of_lt_of_le (r_pos_of_M_neg hX) (r_le_N X)
  have hNY : 0 < N Y := N_pos_of_M_ne_zero hY.ne'
  have hNw := N_alt_pos (Y := Y) hX hne he
  have hM := IsCycle.M_pos hx h hNw
  have hm : (0 : ℝ) < ((M (alt X Y e) : ℤ) : ℝ) := by exact_mod_cast hM
  have hbX : ((M (alt X Y e) : ℤ) : ℝ) * 2 ^ (N X * e.length * K) <
      e.length * 2 ^ N (alt X Y e) * 3 ^ (r X * (e.length - 1) * K) := by
    exact_mod_cast bracket_X_int hU hX hY he h hKl hKmax'
  have hbY : ((M (alt X Y e) : ℤ) : ℝ) * 3 ^ (r Y * e.length * L) <
      e.length * 2 ^ N (alt X Y e) * 2 ^ (N Y * (e.length - 1) * L) := by
    exact_mod_cast bracket_Y_int hU hX hY he hx h hkL hLmax'
  have lX := log_bracket_X hm hs hNX h1 (sumK_le hKmax') hbX
  have lY := log_bracket_Y hm hs hNY h2 (sumL_le hLmax') hbY
  have hNeq : ((N (alt X Y e) : ℕ) : ℝ) = (N X : ℝ) * sumK e + (N Y : ℝ) * sumL e := by
    rw [N_alt]; push_cast; ring
  have hc := combine_rates h1 h2 (A := (N X : ℝ) * sumK e) (B := (N Y : ℝ) * sumL e)
  have hlt : Real.log (((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e)) <
      Real.log e.length - combinedRate (rateX e.length (N X) (r X))
        (rateY e.length (N Y) (r Y)) * N (alt X Y e) := by
    rw [hNeq]
    rcases max_cases (rateX e.length (N X) (r X) * ((N X : ℝ) * sumK e))
      (rateY e.length (N Y) (r Y) * ((N Y : ℝ) * sumL e)) with ⟨hm1, -⟩ | ⟨hm2, -⟩
    · rw [hm1] at hc; linarith
    · rw [hm2] at hc; linarith
  have hy : (0 : ℝ) < ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e) :=
    div_pos hm (by positivity)
  have hsR : (0 : ℝ) < e.length := by exact_mod_cast hs
  calc ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e)
      = Real.exp (Real.log (((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e))) :=
        (Real.exp_log hy).symm
    _ < Real.exp (Real.log e.length - combinedRate (rateX e.length (N X) (r X))
          (rateY e.length (N Y) (r Y)) * N (alt X Y e)) := Real.exp_lt_exp.mpr hlt
    _ = e.length * Real.exp (-(combinedRate (rateX e.length (N X) (r X))
          (rateY e.length (N Y) (r Y)) * N (alt X Y e))) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hsR]

/-- The common step of the two forms of Theorem 6.3: `ρ N < log(2s) + max(-log Λ, 0)`. -/
theorem s_alternations_log {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (hne : e ≠ []) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    (h1 : 0 < rateX e.length (N X) (r X)) (h2 : 0 < rateY e.length (N Y) (r Y))
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt X Y e)) :
    0 < (N (alt X Y e) : ℝ) * Real.log 2 - r (alt X Y e) * Real.log 3 ∧
      combinedRate (rateX e.length (N X) (r X)) (rateY e.length (N Y) (r Y)) * N (alt X Y e) <
        Real.log (2 * e.length) +
          max (-Real.log ((N (alt X Y e) : ℝ) * Real.log 2 - r (alt X Y e) * Real.log 3)) 0 := by
  have ha := s_alternations hU hX hY hne he h1 h2 hx h
  have hs : 0 < e.length := List.length_pos_iff.mpr hne
  have hNw := N_alt_pos (Y := Y) hX hne he
  have hM := IsCycle.M_pos hx h hNw
  have hΛ : 0 < (N (alt X Y e) : ℝ) * Real.log 2 - r (alt X Y e) * Real.log 3 := by
    have := (M_pos_iff _).mp hM; linarith
  exact ⟨hΛ, rate_of_bracket hΛ (by exact_mod_cast hs) (M_div_two_pow_ge _ hΛ) ha⟩

/-- **Theorem 6.3 (`s` alternations), with Laurent's bound.** In the setting of `s_alternations`,
the length `N` of the cycle lies below the largest root of
`ρ N = log(2s) + 28.161 · log 3 · (max(log(κ N) + 0.21, 14))²`, `κ = (1 + log 2) / log 3`
(the paper's `30.9381` and `1.5412`, rounded up). -/
theorem s_alternations_laurent {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (hne : e ≠ []) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    (h1 : 0 < rateX e.length (N X) (r X)) (h2 : 0 < rateY e.length (N Y) (r Y))
    (hL : LaurentBound) {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt X Y e)) :
    combinedRate (rateX e.length (N X) (r X)) (rateY e.length (N Y) (r Y)) * N (alt X Y e) <
      Real.log (2 * e.length) + 28.161 * Real.log 3 *
        (max (Real.log ((1 + Real.log 2) / Real.log 3 * N (alt X Y e)) + 0.21) 14) ^ 2 := by
  obtain ⟨hΛ, key⟩ := s_alternations_log hU hX hY hne he h1 h2 hx h
  have hlau := laurent_neg_log_le hL (N_alt_pos (Y := Y) hX hne he) (r_alt_pos (Y := Y) hX hne he) hΛ
  have hC : 0 ≤ 28.161 * Real.log 3 *
      (max (Real.log ((1 + Real.log 2) / Real.log 3 * N (alt X Y e)) + 0.21) 14) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) log_three_pos.le) (sq_nonneg _)
  have := max_le hlau hC
  linarith

/-- **Theorem 6.3 with Rhin's measure** (the remark after Theorem 6.5): in the setting of
`s_alternations`, `ρ N < log(2s) + 13.3 (0.46057 + log r)`. -/
theorem s_alternations_rhin {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (hne : e ≠ []) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    (h1 : 0 < rateX e.length (N X) (r X)) (h2 : 0 < rateY e.length (N Y) (r Y))
    (hR : RhinBound) {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt X Y e)) :
    combinedRate (rateX e.length (N X) (r X)) (rateY e.length (N Y) (r Y)) * N (alt X Y e) <
      Real.log (2 * e.length) + 13.3 * (0.46057 + Real.log (r (alt X Y e))) := by
  obtain ⟨hΛ, key⟩ := s_alternations_log hU hX hY hne he h1 h2 hx h
  have hr := r_alt_pos (Y := Y) hX hne he
  have hrh := rhin_neg_log_lt hR hr hΛ
  have hr1 : (1 : ℝ) ≤ r (alt X Y e) := by exact_mod_cast hr
  have hC : 0 ≤ 13.3 * (0.46057 + Real.log (r (alt X Y e))) := by
    have := Real.log_nonneg hr1; linarith
  have := max_le hrh.le hC
  linarith

/-- **Theorem 6.3, the exclusion.** If a proved cycle-length bound `B` lies beyond the largest root,
i.e. `ρ B ≥ log(2s) + 28.161 · log 3 · (max(log(κ B) + 0.21, 14))²`, then no word with `s`
alternations over `(X, Y)` is the parity vector of a non-trivial positive integer cycle. -/
theorem s_alternations_excluded {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (hne : e ≠ []) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    (h1 : 0 < rateX e.length (N X) (r X)) (h2 : 0 < rateY e.length (N Y) (r Y))
    (hL : LaurentBound) {B : ℕ} (hB : CycleLengthBound B) (hB0 : 0 < B)
    (hroot : Real.log (2 * e.length) + 28.161 * Real.log 3 *
        (max (Real.log ((1 + Real.log 2) / Real.log 3 * B) + 0.21) 14) ^ 2 ≤
      combinedRate (rateX e.length (N X) (r X)) (rateY e.length (N Y) (r Y)) * B)
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt X Y e)) : x = 1 ∨ x = 2 := by
  by_contra hnt
  have hNw := N_alt_pos (Y := Y) hX hne he
  have hBN := hB x hx _ hNw h.2 hnt
  have main := s_alternations_laurent hU hX hY hne he h1 h2 hL hx h
  have hs1 : (1 : ℝ) ≤ e.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have := laurent_root (N := (N (alt X Y e) : ℝ)) hs1 (by exact_mod_cast hB0)
    (by exact_mod_cast hBN) hroot
  linarith

/-! ### Theorem 6.2 -/

/-- With two alternations and `a ≤ n`, the first rate exceeds `1/8` (it is at least `½ log(4/3)`). -/
theorem rateX_two_gt {n a : ℕ} (hn : 0 < n) (han : a ≤ n) : 1 / 8 < rateX 2 n a := by
  unfold rateX
  simp only [Nat.cast_ofNat]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (a : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast han
  have hl2 := Real.log_two_gt_d9
  have hl3 := log_three_lt
  have := mul_le_mul_of_nonneg_right hq log_three_pos.le
  linarith

/-- With two alternations and a falling block of slope `n'/a' ≤ 2`, the second rate exceeds `1/8`
(it is at least `½ log(3/2)`). -/
theorem rateY_two_gt {n a : ℕ} (hn : 0 < n) (hslope : n ≤ 2 * a) : 1 / 8 < rateY 2 n a := by
  unfold rateY
  simp only [Nat.cast_ofNat]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 1 / 2 ≤ (a : ℝ) / n := by
    rw [le_div_iff₀ hnR]
    have : (n : ℝ) ≤ 2 * a := by exact_mod_cast hslope
    linarith
  have hl2 := Real.log_two_lt_d9
  have hl3 := one_lt_log_three
  have := mul_le_mul_of_nonneg_right hq log_three_pos.le
  linarith

theorem combinedRate_ge {ρ₁ ρ₂ : ℝ} (h1 : 1 / 8 ≤ ρ₁) (h2 : 1 / 8 ≤ ρ₂) :
    1 / 16 ≤ combinedRate ρ₁ ρ₂ := by
  unfold combinedRate
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ ρ₁),
    mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ ρ₂)]

/-- **Theorem 6.2 (two alternations).** Let `(X, Y)` be unimodular with `M_X < 0 < M_Y`, and let the
falling block have slope `n'/a' ≤ 2`. Then no word with two alternations over `(X, Y)` is the parity
vector of a non-trivial positive integer cycle. Inputs: Laurent's bound and Eliahou's cycle-length
bound. (The proof uses the combined rate `≥ 1/16`; the paper's `0.08414` is sharper, but at
Eliahou's bound any rate above about `0.006` suffices.) -/
theorem two_alternations {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    (hslope : N Y ≤ 2 * r Y) (hL : LaurentBound) (hE : CycleLengthBound 17087915)
    {e : List (ℕ × ℕ)} (hlen : e.length = 2) (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2)
    {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt X Y e)) : x = 1 ∨ x = 2 := by
  have hne : e ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
  have hNX : 0 < N X := lt_of_lt_of_le (r_pos_of_M_neg hX) (r_le_N X)
  have hNY : 0 < N Y := N_pos_of_M_ne_zero hY.ne'
  have h1 := rateX_two_gt hNX (r_le_N X)
  have h2 := rateY_two_gt hNY hslope
  have h1' : 0 < rateX e.length (N X) (r X) := by rw [hlen]; linarith
  have h2' : 0 < rateY e.length (N Y) (r Y) := by rw [hlen]; linarith
  by_contra hnt
  have hNw := N_alt_pos (Y := Y) hX hne he
  have hBN := hE x hx _ hNw h.2 hnt
  have main := s_alternations_laurent hU hX hY hne he h1' h2' hL hx h
  rw [hlen] at main
  simp only [Nat.cast_ofNat] at main
  have hρ := combinedRate_ge h1.le h2.le
  have root := laurent_root (ρ := 1 / 16) (s := 2) (N := (N (alt X Y e) : ℝ)) (by norm_num)
    (by norm_num) (by exact_mod_cast hBN) eliahou_check
  have := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (α := ℝ) (N (alt X Y e)))
  linarith

/-! ### The path pairs -/

theorem slope_aux {a b c d : ℕ} (h : a * d = c * b + 1) (h2 : 2 * d ≤ c) : 2 * b ≤ a := by
  by_contra hc
  push_neg at hc
  have h1 : (a + 1) * d ≤ 2 * b * d := Nat.mul_le_mul (by omega) le_rfl
  have h3 : 2 * d * b ≤ c * b := Nat.mul_le_mul h2 le_rfl
  nlinarith

theorem slope_aux' {a b c d : ℕ} (h : a * d = c * b + 1) (h2 : a ≤ 2 * b) : c ≤ 2 * d := by
  by_contra hc
  push_neg at hc
  have h1 : (2 * d + 1) * b ≤ c * b := Nat.mul_le_mul (by omega) le_rfl
  have h3 : a * d ≤ 2 * b * d := Nat.mul_le_mul h2 le_rfl
  nlinarith

/-- Below the root, every pair of the tree has `N(u)/r(u) ≤ 2` or `N(v)/r(v) ≥ 2`: the slopes of the
pairs below `(01, 1)` lie in `[1, 2]`, those below `(0, 01)` in `[2, ∞]`. -/
theorem TreePair.slope {d : ℕ} {u v : Word} (h : TreePair d u v) :
    (d = 0 ∧ u = [false] ∧ v = [true]) ∨ N u ≤ 2 * r u ∨ 2 * r v ≤ N v := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @left d u v hp ih =>
    right
    rcases ih with ⟨-, rfl, rfl⟩ | hA | hB
    · right; decide
    · left; exact hA
    · right
      have := slope_aux hp.det hB
      simp only [N_append, r_append]
      omega
  | @right d u v hp ih =>
    right
    rcases ih with ⟨-, rfl, rfl⟩ | hA | hB
    · left; decide
    · left
      have := slope_aux' hp.det hA
      simp only [N_append, r_append]
      omega
    · right; exact hB

/-- On the path of `log₂ 3` from depth 1 on, the falling word has slope `n'/a' ≤ 2`. -/
theorem OnPath.falling_slope {d : ℕ} {u v : Word} (hp : OnPath d u v) (hd : 1 ≤ d) :
    N u ≤ 2 * r u := by
  rcases hp.1.slope with ⟨h0, -⟩ | hA | hB
  · omega
  · exact hA
  · exfalso
    have hv := hp.2.2
    unfold M at hv
    have h4 : (4 : ℤ) ^ r v ≤ 2 ^ N v := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) hB
    have h34 : (3 : ℤ) ^ r v ≤ 4 ^ r v := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    linarith

/-- **Theorem 6.2 for the path pairs.** For every pair `(u, v)` of the Christoffel tree on the path of
`log₂ 3` from depth 1 on (`u` falling, `v` rising), no word `v^(k_1) u^(l_1) v^(k_2) u^(l_2)` is the
parity vector of a non-trivial positive integer cycle. -/
theorem two_alternations_path {d : ℕ} {u v : Word} (hp : OnPath d u v) (hd : 1 ≤ d)
    (hL : LaurentBound) (hE : CycleLengthBound 17087915) {e : List (ℕ × ℕ)} (hlen : e.length = 2)
    (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) {x : ℤ} (hx : 0 < x) (h : IsCycle x (alt v u e)) :
    x = 1 ∨ x = 2 :=
  two_alternations hp.1.unimodular.symm hp.2.2 hp.2.1 (hp.falling_slope hd) hL hE hlen he hx h

/-! ### Lemma 6.4 -/

/-- **Lemma 6.4, the first rate.** For a pair `(u, v)` on the path, with rising `v` of type `(n, a)`
and falling `u` of type `(n', a')` (so `n' a - n a' = 1`), and `a' ≥ 1`:
the first rate of Theorem 6.3 exceeds `log 2 (1/s - 1/(n a'))`. -/
theorem OnPath.rateX_gt {d : ℕ} {u v : Word} (hp : OnPath d u v) (hru : 0 < r u) {s : ℕ}
    (hs : 0 < s) : Real.log 2 * (1 / s - 1 / ((N v : ℝ) * r u)) < rateX s (N v) (r v) := by
  have hdet := hp.1.det
  have hfall := (M_pos_iff u).mp hp.2.1
  have hNv : 0 < N v := N_pos_of_M_ne_zero hp.2.2.ne
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < N v := by exact_mod_cast hNv
  have haR : (0 : ℝ) < r u := by exact_mod_cast hru
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hdetR : (N u : ℝ) * r v = N v * r u + 1 := by exact_mod_cast hdet
  have hl2 := log_two_pos'
  have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
  have hn0 : (N v : ℝ) ≠ 0 := hnR.ne'
  have ha0 : (r u : ℝ) ≠ 0 := haR.ne'
  have key : (rateX s (N v) (r v) - Real.log 2 * (1 / s - 1 / ((N v : ℝ) * r u))) *
      (s * N v * r u) = ((s : ℝ) - 1) * N v * r u * Real.log 2 + s * Real.log 2 -
        ((s : ℝ) - 1) * r v * r u * Real.log 3 := by
    unfold rateX; field_simp; ring
  have hpos : 0 < ((s : ℝ) - 1) * N v * r u * Real.log 2 + s * Real.log 2 -
      ((s : ℝ) - 1) * r v * r u * Real.log 3 := by
    have h1 := mul_le_mul_of_nonneg_left hfall.le
      (mul_nonneg (sub_nonneg.mpr hs1) (Nat.cast_nonneg (α := ℝ) (r v)))
    have h2 : ((s : ℝ) - 1) * Real.log 2 * ((N u : ℝ) * r v) =
        ((s : ℝ) - 1) * Real.log 2 * (N v * r u + 1) := by rw [hdetR]
    linarith
  have hprod : 0 < (s : ℝ) * N v * r u := mul_pos (mul_pos hsR hnR) haR
  have hmul : 0 < (rateX s (N v) (r v) - Real.log 2 * (1 / s - 1 / ((N v : ℝ) * r u))) *
      (s * N v * r u) := by rw [key]; exact hpos
  by_contra hcon
  push_neg at hcon
  nlinarith

/-- **Lemma 6.4, the second rate.** In the same setting, the second rate exceeds
`log 2 (1/s - 1/(a n'))`. -/
theorem OnPath.rateY_gt {d : ℕ} {u v : Word} (hp : OnPath d u v) (hru : 0 < r u) {s : ℕ}
    (hs : 0 < s) : Real.log 2 * (1 / s - 1 / ((r v : ℝ) * N u)) < rateY s (N u) (r u) := by
  have hdet := hp.1.det
  have hrise := (M_neg_iff v).mp hp.2.2
  have hNu : 0 < N u := hp.1.N_pos_left
  have hrv : 0 < r v := r_pos_of_M_neg hp.2.2
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < N u := by exact_mod_cast hNu
  have haR : (0 : ℝ) < r v := by exact_mod_cast hrv
  have ha'R : (0 : ℝ) < r u := by exact_mod_cast hru
  have hdetR : (N u : ℝ) * r v = N v * r u + 1 := by exact_mod_cast hdet
  have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
  have hn0 : (N u : ℝ) ≠ 0 := hnR.ne'
  have ha0 : (r v : ℝ) ≠ 0 := haR.ne'
  have key : (rateY s (N u) (r u) - Real.log 2 * (1 / s - 1 / ((r v : ℝ) * N u))) *
      (s * r v * N u) = s * r v * r u * Real.log 3 - s * r v * N u * Real.log 2 +
        s * Real.log 2 := by
    unfold rateY; field_simp; ring
  have hpos : 0 < s * (r v : ℝ) * r u * Real.log 3 - s * r v * N u * Real.log 2 +
      s * Real.log 2 := by
    have h1 := mul_lt_mul_of_pos_left hrise (mul_pos hsR ha'R)
    have h2 : (s : ℝ) * Real.log 2 * ((N u : ℝ) * r v) = s * Real.log 2 * (N v * r u + 1) := by
      rw [hdetR]
    linarith
  have hprod : 0 < (s : ℝ) * r v * N u := mul_pos (mul_pos hsR haR) hnR
  have hmul : 0 < (rateY s (N u) (r u) - Real.log 2 * (1 / s - 1 / ((r v : ℝ) * N u))) *
      (s * r v * N u) := by rw [key]; exact hpos
  by_contra hcon
  push_neg at hcon
  nlinarith

/-- **Lemma 6.4.** For a pair `(u, v)` on the path with `a' = r(u) ≥ 1`, and `K = min(n a', a n')`,
both rates of Theorem 6.3 exceed `log 2 (1/s - 1/K)`. -/
theorem OnPath.rates_gt {d : ℕ} {u v : Word} (hp : OnPath d u v) (hru : 0 < r u) {s : ℕ}
    (hs : 0 < s) :
    Real.log 2 * (1 / s - 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ)) < rateX s (N v) (r v) ∧
      Real.log 2 * (1 / s - 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ)) <
        rateY s (N u) (r u) := by
  have hNv : 0 < N v := N_pos_of_M_ne_zero hp.2.2.ne
  have hNu : 0 < N u := hp.1.N_pos_left
  have hrv : 0 < r v := r_pos_of_M_neg hp.2.2
  have hK : 0 < min (N v * r u) (r v * N u) := lt_min (Nat.mul_pos hNv hru) (Nat.mul_pos hrv hNu)
  have hKR : (0 : ℝ) < ((min (N v * r u) (r v * N u) : ℕ) : ℝ) := by exact_mod_cast hK
  have hl2 := log_two_pos'
  have i1 : 1 / ((N v : ℝ) * r u) ≤ 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ) := by
    apply one_div_le_one_div_of_le hKR
    have : min (N v * r u) (r v * N u) ≤ N v * r u := min_le_left _ _
    exact_mod_cast this
  have i2 : 1 / ((r v : ℝ) * N u) ≤ 1 / ((min (N v * r u) (r v * N u) : ℕ) : ℝ) := by
    apply one_div_le_one_div_of_le hKR
    have : min (N v * r u) (r v * N u) ≤ r v * N u := min_le_right _ _
    exact_mod_cast this
  have hX := hp.rateX_gt hru hs
  have hY := hp.rateY_gt hru hs
  have j1 := mul_le_mul_of_nonneg_left i1 hl2.le
  have j2 := mul_le_mul_of_nonneg_left i2 hl2.le
  constructor <;> nlinarith

/-- **Lemma 6.4, `K` increases along the path**, when the rising word `v` is replaced by `uv`. -/
theorem pathK_lt_left {u v : Word} (hu : 0 < N u) (hru : 0 < r u) :
    min (N v * r u) (r v * N u) < min (N (u ++ v) * r u) (r (u ++ v) * N u) := by
  apply lt_min
  · calc min (N v * r u) (r v * N u) ≤ N v * r u := min_le_left _ _
      _ < N (u ++ v) * r u := by
        rw [N_append, add_mul]; have := Nat.mul_pos hu hru; omega
  · calc min (N v * r u) (r v * N u) ≤ r v * N u := min_le_right _ _
      _ < r (u ++ v) * N u := by
        rw [r_append, add_mul]; have := Nat.mul_pos hru hu; omega

/-- **Lemma 6.4, `K` increases along the path**, when the falling word `u` is replaced by `uv`. -/
theorem pathK_lt_right {u v : Word} (hv : 0 < N v) (hrv : 0 < r v) :
    min (N v * r u) (r v * N u) < min (N v * r (u ++ v)) (r v * N (u ++ v)) := by
  apply lt_min
  · calc min (N v * r u) (r v * N u) ≤ N v * r u := min_le_left _ _
      _ < N v * r (u ++ v) := by
        rw [r_append, mul_add]; have := Nat.mul_pos hv hrv; omega
  · calc min (N v * r u) (r v * N u) ≤ r v * N u := min_le_right _ _
      _ < r v * N (u ++ v) := by
        rw [N_append, mul_add]; have := Nat.mul_pos hrv hv; omega

end TwoBlock
