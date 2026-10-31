import TwoBlock.CycleEquation

/-!
# Integrality: Lemma 2.2 and same-side pairs (Proposition 5.2)

The paper, Sections 2 and 5. The paper's `D'(X, Y)` is `D(X, Y)` with every factor 2
and 3 removed. Here a pair is **unimodular** when `D(X, Y) = ± 2^i 3^j`, i.e. `D' = ±1`; Lemma 2.2 is
stated for any factorization `D = 2^i 3^j E`, which contains the case `E = D'`.
-/

namespace TwoBlock

theorem two_pow_mod_three (n : ℕ) : (2 : ℤ) ^ n % 3 = 1 ∨ (2 : ℤ) ^ n % 3 = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    generalize (2 : ℤ) ^ n = t at ih ⊢
    omega

theorem three_pow_mod_two (n : ℕ) : (3 : ℤ) ^ n % 2 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    generalize (3 : ℤ) ^ n = t at ih ⊢
    omega

/-- `M_w` is odd when `w` is not empty. -/
theorem M_mod_two {w : Word} (hN : 0 < N w) : M w % 2 = 1 := by
  unfold M
  obtain ⟨n, hn⟩ : ∃ n, N w = n + 1 := ⟨N w - 1, by omega⟩
  rw [hn, pow_succ]
  have h3 := three_pow_mod_two (r w)
  generalize (2 : ℤ) ^ n = t
  generalize (3 : ℤ) ^ r w = s at h3 ⊢
  omega

/-- `M_w` is prime to 3 when `w` has a one. -/
theorem M_mod_three {w : Word} (hr : 0 < r w) : M w % 3 ≠ 0 := by
  unfold M
  obtain ⟨m, hm⟩ : ∃ m, r w = m + 1 := ⟨r w - 1, by omega⟩
  rw [hm, pow_succ]
  have h2 := two_pow_mod_three (N w)
  generalize (2 : ℤ) ^ N w = t at h2 ⊢
  generalize (3 : ℤ) ^ m = s
  omega

theorem M_ne_zero {w : Word} (hN : 0 < N w) : M w ≠ 0 := by
  have := M_mod_two hN; omega

theorem N_pos_of_M_ne_zero {w : Word} (h : M w ≠ 0) : 0 < N w := by
  rcases Nat.eq_zero_or_pos (N w) with h0 | h0
  · have hr : r w = 0 := by have := r_le_N w; omega
    exfalso; apply h; simp [M, h0, hr]
  · exact h0

theorem r_pos_of_M_neg {w : Word} (h : M w < 0) : 0 < r w := by
  rcases Nat.eq_zero_or_pos (r w) with h0 | h0
  · unfold M at h; rw [h0, pow_zero] at h
    have : (0 : ℤ) < 2 ^ N w := by positivity
    omega
  · exact h0

theorem r_pos_of_D_ne_zero {X Y : Word} (h : D X Y ≠ 0) : 0 < r X ∨ 0 < r Y := by
  by_contra hc
  push_neg at hc
  apply h
  unfold D
  rw [c_eq_zero_of_r_eq_zero (by omega : r X = 0), c_eq_zero_of_r_eq_zero (by omega : r Y = 0)]
  ring

theorem D_swap (X Y : Word) : D Y X = -D X Y := by unfold D; ring

theorem isCoprime_of_mod_two {m : ℤ} (h : m % 2 = 1) : IsCoprime m 2 :=
  ⟨1, -(m / 2), by omega⟩

theorem isCoprime_of_mod_three {m : ℤ} (h : m % 3 ≠ 0) : IsCoprime m 3 := by
  rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h1 | h1
  · exact ⟨1, -(m / 3), by omega⟩
  · exact ⟨-1, m / 3 + 1, by omega⟩

/-- `M_w` is prime to 6 (for `w` with a one). -/
theorem isCoprime_M {w : Word} (hN : 0 < N w) (hr : 0 < r w) (i j : ℕ) :
    IsCoprime (M w) (2 ^ i * 3 ^ j) :=
  (isCoprime_of_mod_two (M_mod_two hN)).pow_right.mul_right
    (isCoprime_of_mod_three (M_mod_three hr)).pow_right

theorem isCoprime_M_two_pow {w : Word} (hN : 0 < N w) (i : ℕ) : IsCoprime (M w) (2 ^ i) :=
  (isCoprime_of_mod_two (M_mod_two hN)).pow_right

theorem isCoprime_two_pow_three_pow (m n : ℕ) : IsCoprime ((2 : ℤ) ^ m) ((3 : ℤ) ^ n) :=
  (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow

/-- A pair is unimodular when `D'(X, Y) = ±1`, i.e. `D(X, Y) = ± 2^i 3^j`. -/
def Unimodular (X Y : Word) : Prop :=
  ∃ i j : ℕ, D X Y = 2 ^ i * 3 ^ j ∨ D X Y = -(2 ^ i * 3 ^ j)

theorem Unimodular.D_ne_zero {X Y : Word} (h : Unimodular X Y) : D X Y ≠ 0 := by
  obtain ⟨i, j, hD | hD⟩ := h <;> rw [hD]
  · positivity
  · have : (0 : ℤ) < 2 ^ i * 3 ^ j := by positivity
    linarith

theorem Unimodular.symm {X Y : Word} (h : Unimodular X Y) : Unimodular Y X := by
  obtain ⟨i, j, hD | hD⟩ := h
  · exact ⟨i, j, Or.inr (by rw [D_swap, hD])⟩
  · exact ⟨i, j, Or.inl (by rw [D_swap, hD, neg_neg])⟩

/-- Cancelling a unimodular minor: if `M_w ∣ D · a` then `M_w ∣ a`. -/
theorem dvd_of_dvd_D_mul {X Y w : Word} (hU : Unimodular X Y) (hN : 0 < N w) (hr : 0 < r w)
    {a : ℤ} (h : M w ∣ D X Y * a) : M w ∣ a := by
  obtain ⟨i, j, hD | hD⟩ := hU
  · rw [hD] at h
    exact (isCoprime_M hN hr i j).dvd_of_dvd_mul_left h
  · rw [hD, neg_mul, dvd_neg] at h
    exact (isCoprime_M hN hr i j).dvd_of_dvd_mul_left h

/-- **Lemma 2.2 (integrality).** Let `w = X^k Y^l` have a one, and `x M_w = c_w`. For any
factorization `D(X, Y) = 2^i 3^j E` (in particular `E = D'(X, Y)`), `M_w` divides `E F_l(Y)` and
`E F_k(X)`. -/
theorem two_block_dvd {X Y : Word} {k l : ℕ} {x : ℤ}
    (hN : 0 < N (wpow X k ++ wpow Y l)) (hr : 0 < r (wpow X k ++ wpow Y l))
    (hx : x * M (wpow X k ++ wpow Y l) = c (wpow X k ++ wpow Y l))
    {i j : ℕ} {E : ℤ} (hD : D X Y = 2 ^ i * 3 ^ j * E) :
    M (wpow X k ++ wpow Y l) ∣ E * F Y l ∧ M (wpow X k ++ wpow Y l) ∣ E * F X k := by
  obtain ⟨h1, h2⟩ := two_block_identities hx
  rw [hD] at h1 h2
  constructor
  · have d : M (wpow X k ++ wpow Y l) ∣ 2 ^ (i + N X * k) * 3 ^ j * (E * F Y l) :=
      ⟨c X - M X * x, by rw [h1]; ring⟩
    exact (isCoprime_M hN hr _ _).dvd_of_dvd_mul_left d
  · have d : M (wpow X k ++ wpow Y l) ∣ 2 ^ i * 3 ^ (j + r Y * l) * (E * F X k) :=
      ⟨M Y * x - c Y, by rw [h2]; ring⟩
    exact (isCoprime_M hN hr _ _).dvd_of_dvd_mul_left d

/-- **Lemma 2.2** for a unimodular pair: `M_w` divides `F_l(Y)` and `F_k(X)`. -/
theorem two_block_dvd_of_unimodular {X Y : Word} (hU : Unimodular X Y) {k l : ℕ} {x : ℤ}
    (hN : 0 < N (wpow X k ++ wpow Y l)) (hr : 0 < r (wpow X k ++ wpow Y l))
    (hx : x * M (wpow X k ++ wpow Y l) = c (wpow X k ++ wpow Y l)) :
    M (wpow X k ++ wpow Y l) ∣ F Y l ∧ M (wpow X k ++ wpow Y l) ∣ F X k := by
  obtain ⟨i, j, hD | hD⟩ := hU
  · have := two_block_dvd hN hr hx (i := i) (j := j) (E := 1) (by rw [hD, mul_one])
    simpa using this
  · have := two_block_dvd hN hr hx (i := i) (j := j) (E := -1) (by rw [hD]; ring)
    simpa using this

/-- **Lemma 5.1, integrality.** If `(X, Y)` is unimodular and `p_w` is an integer, `M_w` divides both
weights. -/
theorem spell_dvd {X Y : Word} (hU : Unimodular X Y) {s : List Bool} {α β x : ℤ}
    (hN : 0 < N (spell X Y s)) (hr : 0 < r (spell X Y s))
    (hc : c (spell X Y s) = α * c X + β * c Y) (hM : M (spell X Y s) = α * M X + β * M Y)
    (hx : x * M (spell X Y s) = c (spell X Y s)) :
    M (spell X Y s) ∣ α ∧ M (spell X Y s) ∣ β := by
  obtain ⟨h1, h2⟩ := spell_minors hc hM hx
  exact ⟨dvd_of_dvd_D_mul hU hN hr ⟨M Y * x - c Y, by rw [h1]; ring⟩,
    dvd_of_dvd_D_mul hU hN hr ⟨c X - M X * x, by rw [h2]; ring⟩⟩

/-- **Proposition 5.2 (same-side pairs).** If `(X, Y)` is unimodular and `M_X`, `M_Y` have the same
sign, then no word made of copies of `X` and `Y`, both occurring, has an integral cycle point:
`x M_w ≠ c_w` for every integer `x`. No Baker-type input. -/
theorem same_side {X Y : Word} (hU : Unimodular X Y)
    (hside : (0 < M X ∧ 0 < M Y) ∨ (M X < 0 ∧ M Y < 0))
    {s : List Bool} (hsX : true ∈ s) (hsY : false ∈ s) (x : ℤ) :
    x * M (spell X Y s) ≠ c (spell X Y s) := by
  intro hx
  obtain ⟨α, β, hc, hM, hα, hβ, hαp, hβp⟩ := spell_weights X Y s
  have hα0 := hαp hsX
  have hβ0 := hβp hsY
  have hMX : M X ≠ 0 := by
    rcases hside with h | h
    · exact h.1.ne'
    · exact h.1.ne
  have hN : 0 < N (spell X Y s) := by
    have := N_pos_of_M_ne_zero hMX
    have := (N_spell_of_mem (X := X) (Y := Y) (s := s)).1 hsX
    omega
  have hr : 0 < r (spell X Y s) := by
    have h1 := (N_spell_of_mem (X := X) (Y := Y) (s := s)).1 hsX
    have h2 := (N_spell_of_mem (X := X) (Y := Y) (s := s)).2 hsY
    rcases r_pos_of_D_ne_zero hU.D_ne_zero with h | h <;> omega
  obtain ⟨dα, -⟩ := spell_dvd hU hN hr hc hM hx
  have hle : |M (spell X Y s)| ≤ α := Int.le_of_dvd hα0 ((abs_dvd _ _).mpr dα)
  rcases hside with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · have h1 : α * 1 ≤ α * M X := mul_le_mul_of_nonneg_left (by omega) hα
    have h2 : β * 1 ≤ β * M Y := mul_le_mul_of_nonneg_left (by omega) hβ
    have := le_abs_self (M (spell X Y s))
    linarith
  · have h1 : α * 1 ≤ α * -M X := mul_le_mul_of_nonneg_left (by omega) hα
    have h2 : β * 1 ≤ β * -M Y := mul_le_mul_of_nonneg_left (by omega) hβ
    have := neg_abs_le (M (spell X Y s))
    linarith

end TwoBlock
