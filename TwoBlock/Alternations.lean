import TwoBlock.Stretch

/-!
# Words with several alternations: Lemma 6.1 (the two brackets)

Section 6 of the paper. A word with `s` alternations over `(X, Y)` is
`X^(k_1) Y^(l_1) ⋯ X^(k_s) Y^(l_s)`, with every exponent at least 1. Here it is `alt X Y e` for the
list `e` of exponent pairs `(k_i, l_i)`, so `s` is the length of `e`. `sumK e` and `sumL e` are the
exponent totals, so the `X`-length and the `Y`-length are `N X * sumK e` and `N Y * sumL e`.

The weights of `alt X Y e` over the pair (Lemma 5.1) are `altα` and `altβ`:
`D(Z, alt X Y e) = α D(Z, X) + β D(Z, Y)` for every word `Z`.

Lemma 6.1 is proved as in the paper. Rotate the cycle to the start of its longest `X`-run (or
`Y`-run) and read Lemma 7.1's exact form there: the modulus divides the weight of the other block.
Then bound that weight run by run.
-/

namespace TwoBlock

/-! ### Words with alternations -/

/-- The word `X^(k_1) Y^(l_1) ⋯ X^(k_s) Y^(l_s)` for the list of exponent pairs `(k_i, l_i)`. -/
def alt (X Y : Word) : List (ℕ × ℕ) → Word
  | [] => []
  | (k, l) :: e => wpow X k ++ (wpow Y l ++ alt X Y e)

/-- The total `X`-exponent `k_1 + ⋯ + k_s`. -/
def sumK : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (k, _) :: e => k + sumK e

/-- The total `Y`-exponent `l_1 + ⋯ + l_s`. -/
def sumL : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, l) :: e => l + sumL e

@[simp] theorem alt_nil (X Y : Word) : alt X Y [] = [] := rfl

@[simp] theorem alt_cons (X Y : Word) (k l : ℕ) (e : List (ℕ × ℕ)) :
    alt X Y ((k, l) :: e) = wpow X k ++ (wpow Y l ++ alt X Y e) := rfl

@[simp] theorem sumK_nil : sumK [] = 0 := rfl

@[simp] theorem sumK_cons (k l : ℕ) (e : List (ℕ × ℕ)) : sumK ((k, l) :: e) = k + sumK e := rfl

@[simp] theorem sumL_nil : sumL [] = 0 := rfl

@[simp] theorem sumL_cons (k l : ℕ) (e : List (ℕ × ℕ)) : sumL ((k, l) :: e) = l + sumL e := rfl

theorem alt_append (X Y : Word) (e₁ e₂ : List (ℕ × ℕ)) :
    alt X Y (e₁ ++ e₂) = alt X Y e₁ ++ alt X Y e₂ := by
  induction e₁ with
  | nil => rfl
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [List.cons_append, alt_cons, alt_cons, ih]
    simp only [List.append_assoc]

theorem N_alt (X Y : Word) (e : List (ℕ × ℕ)) :
    N (alt X Y e) = N X * sumK e + N Y * sumL e := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [alt_cons, N_append, N_append, N_wpow, N_wpow, ih, sumK_cons, sumL_cons]
    ring

theorem r_alt (X Y : Word) (e : List (ℕ × ℕ)) :
    r (alt X Y e) = r X * sumK e + r Y * sumL e := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [alt_cons, r_append, r_append, r_wpow, r_wpow, ih, sumK_cons, sumL_cons]
    ring

theorem sumK_le {e : List (ℕ × ℕ)} {K : ℕ} (h : ∀ p ∈ e, p.1 ≤ K) : sumK e ≤ e.length * K := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    have hk : k ≤ K := h (k, l) (by simp)
    have he := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    rw [sumK_cons, List.length_cons, add_mul, one_mul]
    omega

theorem sumL_le {e : List (ℕ × ℕ)} {L : ℕ} (h : ∀ p ∈ e, p.2 ≤ L) : sumL e ≤ e.length * L := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    have hl : l ≤ L := h (k, l) (by simp)
    have he := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    rw [sumL_cons, List.length_cons, add_mul, one_mul]
    omega

/-- With every exponent at least 1, `s ≤ k_1 + ⋯ + k_s`. -/
theorem length_le_sumK {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    e.length ≤ sumK e := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    have hk : 1 ≤ k := (he (k, l) (by simp)).1
    have h := ih (fun q hq => he q (List.mem_cons_of_mem _ hq))
    rw [sumK_cons, List.length_cons]
    omega

/-- With every exponent at least 1, `s ≤ l_1 + ⋯ + l_s`. -/
theorem length_le_sumL {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    e.length ≤ sumL e := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    have hl : 1 ≤ l := (he (k, l) (by simp)).2
    have h := ih (fun q hq => he q (List.mem_cons_of_mem _ hq))
    rw [sumL_cons, List.length_cons]
    omega

/-- A non-empty list has an entry where `f` is largest (a longest run). -/
theorem exists_max_run {e : List (ℕ × ℕ)} (h : e ≠ []) (f : ℕ × ℕ → ℕ) :
    ∃ p ∈ e, ∀ q ∈ e, f q ≤ f p := by
  induction e with
  | nil => exact absurd rfl h
  | cons a e ih =>
    rcases eq_or_ne e [] with rfl | he
    · exact ⟨a, by simp, by simp⟩
    · obtain ⟨p, hp, hmax⟩ := ih he
      rcases le_total (f a) (f p) with hap | hpa
      · refine ⟨p, List.mem_cons_of_mem _ hp, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hap
        · exact hmax q hq'
      · refine ⟨a, by simp, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact le_rfl
        · exact (hmax q hq').trans hpa

/-! ### The weights over the pair -/

/-- The `X`-weight of `alt X Y e` (Lemma 5.1's `α`, the sum of the weights of the `X`-positions):
`c = α c_X + β c_Y` and `M = α M_X + β M_Y`. -/
def altα (X Y : Word) : List (ℕ × ℕ) → ℤ
  | [] => 0
  | (k, l) :: e => 3 ^ (r Y * l + r (alt X Y e)) * F X k + 2 ^ (N X * k + N Y * l) * altα X Y e

/-- The `Y`-weight of `alt X Y e` (Lemma 5.1's `β`). -/
def altβ (X Y : Word) : List (ℕ × ℕ) → ℤ
  | [] => 0
  | (k, l) :: e =>
    2 ^ (N X * k) * 3 ^ r (alt X Y e) * F Y l + 2 ^ (N X * k + N Y * l) * altβ X Y e

@[simp] theorem altα_nil (X Y : Word) : altα X Y [] = 0 := rfl

theorem altα_cons (X Y : Word) (k l : ℕ) (e : List (ℕ × ℕ)) :
    altα X Y ((k, l) :: e) =
      3 ^ (r Y * l + r (alt X Y e)) * F X k + 2 ^ (N X * k + N Y * l) * altα X Y e := rfl

@[simp] theorem altβ_nil (X Y : Word) : altβ X Y [] = 0 := rfl

theorem altβ_cons (X Y : Word) (k l : ℕ) (e : List (ℕ × ℕ)) :
    altβ X Y ((k, l) :: e) =
      2 ^ (N X * k) * 3 ^ r (alt X Y e) * F Y l + 2 ^ (N X * k + N Y * l) * altβ X Y e := rfl

/-- The minor along a concatenation: `D(Z, uv) = 3^r(v) D(Z, u) + 2^N(u) D(Z, v)`. -/
theorem D_append (Z u v : Word) : D Z (u ++ v) = 3 ^ r v * D Z u + 2 ^ N u * D Z v := by
  simp only [D, c_append, M_append]; ring

theorem D_wpow (Z X : Word) (k : ℕ) : D Z (wpow X k) = F X k * D Z X := by
  simp only [D, c_wpow, M_wpow]; ring

theorem D_self (X : Word) : D X X = 0 := by unfold D; ring

/-- **Lemma 5.1 for `alt`.** `D(Z, alt X Y e) = α D(Z, X) + β D(Z, Y)`. -/
theorem D_alt (Z X Y : Word) (e : List (ℕ × ℕ)) :
    D Z (alt X Y e) = altα X Y e * D Z X + altβ X Y e * D Z Y := by
  induction e with
  | nil => simp [D, M]
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [alt_cons, D_append, D_append, D_wpow, D_wpow, ih, altα_cons, altβ_cons]
    simp only [r_append, r_wpow, N_wpow, pow_add]
    ring

/-! ### Bounds on the weights -/

theorem F_nonneg (X : Word) (k : ℕ) : 0 ≤ F X k :=
  geom_nonneg (by positivity) (by positivity) k

theorem F_le_of_M_pos {X : Word} (h : 0 < M X) (k : ℕ) : F X k ≤ 2 ^ (N X * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [F]
  · exact (F_lt_of_M_pos h hk).le

theorem F_le_of_M_neg {X : Word} (h : M X < 0) (k : ℕ) : F X k ≤ 3 ^ (r X * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [F]
  · exact (F_lt_of_M_neg h hk).le

theorem two_pow_le_three_pow {X : Word} (h : M X < 0) (k : ℕ) :
    (2 : ℤ) ^ (N X * k) ≤ 3 ^ (r X * k) := by
  have h1 : (2 : ℤ) ^ N X ≤ 3 ^ r X := by unfold M at h; linarith
  rw [pow_mul, pow_mul]
  exact pow_le_pow_left₀ (by positivity) h1 k

theorem three_pow_le_two_pow {Y : Word} (h : 0 < M Y) (l : ℕ) :
    (3 : ℤ) ^ (r Y * l) ≤ 2 ^ (N Y * l) := by
  have h1 : (3 : ℤ) ^ r Y ≤ 2 ^ N Y := by unfold M at h; linarith
  rw [pow_mul, pow_mul]
  exact pow_le_pow_left₀ (by positivity) h1 l

/-- For `0 ≤ p ≤ q` and `i ≤ j`: `q^i p^j ≤ p^i q^j`. -/
theorem pow_swap_le {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q) {i j : ℕ} (hij : i ≤ j) :
    q ^ i * p ^ j ≤ p ^ i * q ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hq : 0 ≤ q := hp.trans hpq
  have h1 : p ^ d ≤ q ^ d := pow_le_pow_left₀ hp hpq d
  have h2 : 0 ≤ q ^ i * p ^ i := mul_nonneg (pow_nonneg hq i) (pow_nonneg hp i)
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  rw [pow_add, pow_add]
  linarith

theorem altα_nonneg (X Y : Word) (e : List (ℕ × ℕ)) : 0 ≤ altα X Y e := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [altα_cons]
    exact add_nonneg (mul_nonneg (by positivity) (F_nonneg X k)) (mul_nonneg (by positivity) ih)

theorem altβ_nonneg (X Y : Word) (e : List (ℕ × ℕ)) : 0 ≤ altβ X Y e := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [altβ_cons]
    exact add_nonneg (mul_nonneg (by positivity) (F_nonneg Y l)) (mul_nonneg (by positivity) ih)

/-- Run by run, the `X`-weight is at most `s 2^(n' (l_1 + ⋯ + l_s)) 3^(a (k_1 + ⋯ + k_s))`
(for `X` rising and `Y` falling). -/
theorem altα_le {X Y : Word} (hX : M X < 0) (hY : 0 < M Y) (e : List (ℕ × ℕ)) :
    altα X Y e ≤ e.length * (2 ^ (N Y * sumL e) * 3 ^ (r X * sumK e)) := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [altα_cons, r_alt, List.length_cons, sumL_cons, sumK_cons]
    have hF := F_le_of_M_neg hX k
    have hF0 := F_nonneg X k
    have ha := two_pow_le_three_pow hX k
    have hb := three_pow_le_two_pow hY l
    have hc := three_pow_le_two_pow hY (sumL e)
    have hA0 := altα_nonneg X Y e
    have e1 : (3 : ℤ) ^ (r Y * l + (r X * sumK e + r Y * sumL e)) =
        3 ^ (r Y * l) * (3 ^ (r X * sumK e) * 3 ^ (r Y * sumL e)) := by rw [pow_add, pow_add]
    have e2 : (2 : ℤ) ^ (N X * k + N Y * l) = 2 ^ (N X * k) * 2 ^ (N Y * l) := pow_add _ _ _
    have e3 : (2 : ℤ) ^ (N Y * (l + sumL e)) = 2 ^ (N Y * l) * 2 ^ (N Y * sumL e) := by
      rw [mul_add, pow_add]
    have e4 : (3 : ℤ) ^ (r X * (k + sumK e)) = 3 ^ (r X * k) * 3 ^ (r X * sumK e) := by
      rw [mul_add, pow_add]
    rw [e1, e2, e3, e4]
    push_cast
    have t1 : (3 : ℤ) ^ (r Y * l) * (3 ^ (r X * sumK e) * 3 ^ (r Y * sumL e)) * F X k ≤
        2 ^ (N Y * l) * (3 ^ (r X * sumK e) * 2 ^ (N Y * sumL e)) * 3 ^ (r X * k) := by
      have u1 : (3 : ℤ) ^ (r Y * l) * 3 ^ (r Y * sumL e) ≤ 2 ^ (N Y * l) * 2 ^ (N Y * sumL e) :=
        mul_le_mul hb hc (by positivity) (by positivity)
      have u2 := mul_le_mul u1 hF hF0 (by positivity)
      have u3 := mul_le_mul_of_nonneg_left u2 (show (0 : ℤ) ≤ 3 ^ (r X * sumK e) by positivity)
      linarith
    have t2 : (2 : ℤ) ^ (N X * k) * 2 ^ (N Y * l) * altα X Y e ≤
        3 ^ (r X * k) * 2 ^ (N Y * l) * (e.length * (2 ^ (N Y * sumL e) * 3 ^ (r X * sumK e))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right ha (by positivity)) ih hA0 (by positivity)
    linarith

/-- Run by run, the `Y`-weight is at most `s 2^(n' (l_1 + ⋯ + l_s)) 3^(a (k_1 + ⋯ + k_s))`. -/
theorem altβ_le {X Y : Word} (hX : M X < 0) (hY : 0 < M Y) (e : List (ℕ × ℕ)) :
    altβ X Y e ≤ e.length * (2 ^ (N Y * sumL e) * 3 ^ (r X * sumK e)) := by
  induction e with
  | nil => simp
  | cons p e ih =>
    obtain ⟨k, l⟩ := p
    rw [altβ_cons, r_alt, List.length_cons, sumL_cons, sumK_cons]
    have hG := F_le_of_M_pos hY l
    have hG0 := F_nonneg Y l
    have ha := two_pow_le_three_pow hX k
    have hc := three_pow_le_two_pow hY (sumL e)
    have hB0 := altβ_nonneg X Y e
    have e1 : (3 : ℤ) ^ (r X * sumK e + r Y * sumL e) =
        3 ^ (r X * sumK e) * 3 ^ (r Y * sumL e) := pow_add _ _ _
    have e2 : (2 : ℤ) ^ (N X * k + N Y * l) = 2 ^ (N X * k) * 2 ^ (N Y * l) := pow_add _ _ _
    have e3 : (2 : ℤ) ^ (N Y * (l + sumL e)) = 2 ^ (N Y * l) * 2 ^ (N Y * sumL e) := by
      rw [mul_add, pow_add]
    have e4 : (3 : ℤ) ^ (r X * (k + sumK e)) = 3 ^ (r X * k) * 3 ^ (r X * sumK e) := by
      rw [mul_add, pow_add]
    rw [e1, e2, e3, e4]
    push_cast
    have t1 : (2 : ℤ) ^ (N X * k) * (3 ^ (r X * sumK e) * 3 ^ (r Y * sumL e)) * F Y l ≤
        3 ^ (r X * k) * (3 ^ (r X * sumK e) * 2 ^ (N Y * sumL e)) * 2 ^ (N Y * l) := by
      have u1 : (2 : ℤ) ^ (N X * k) * 3 ^ (r Y * sumL e) ≤ 3 ^ (r X * k) * 2 ^ (N Y * sumL e) :=
        mul_le_mul ha hc (by positivity) (by positivity)
      have u2 := mul_le_mul u1 hG hG0 (by positivity)
      have u3 := mul_le_mul_of_nonneg_left u2 (show (0 : ℤ) ≤ 3 ^ (r X * sumK e) by positivity)
      linarith
    have t2 : (2 : ℤ) ^ (N X * k) * 2 ^ (N Y * l) * altβ X Y e ≤
        3 ^ (r X * k) * 2 ^ (N Y * l) * (e.length * (2 ^ (N Y * sumL e) * 3 ^ (r X * sumK e))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right ha (by positivity)) ih hB0 (by positivity)
    linarith

/-! ### Lemma 6.1 at the start of a longest run -/

/-- A positive integer cycle point makes the modulus positive: `x M_w = c_w ≥ 0`. -/
theorem IsCycle.M_pos {x : ℤ} {w : Word} (hx : 0 < x) (h : IsCycle x w) (hN : 0 < N w) :
    0 < M w := by
  have hxM := h.eq
  have hc := c_nonneg w
  rcases lt_or_gt_of_ne (M_ne_zero hN) with hlt | hgt
  · have := mul_neg_of_pos_of_neg hx hlt; linarith
  · exact hgt

/-- **Lemma 6.1, first bracket, at the start of a longest `X`-run.** The cycle reads
`X^K Y^l X^(k_2) Y^(l_2) ⋯ X^(k_s) Y^(l_s)` from `y`, with `K` at least every later `k_i`. Then
`M_w 2^(n s K) < s 2^N 3^(a (s-1) K)`. -/
theorem bracketX_core {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {K l : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ l) {e : List (ℕ × ℕ)} (hKe : ∀ p ∈ e, p.1 ≤ K)
    {y : ℤ} (h : IsCycle y (wpow X K ++ (wpow Y l ++ alt X Y e))) :
    M (wpow X K ++ (wpow Y l ++ alt X Y e)) * 2 ^ (N X * (e.length + 1) * K) <
      (e.length + 1) * 2 ^ N (wpow X K ++ (wpow Y l ++ alt X Y e)) *
        3 ^ (r X * e.length * K) := by
  have hrX := r_pos_of_M_neg hX
  have hNX := r_le_N X
  have key := stretch_exact h
  have hNeq : N (wpow X K ++ (wpow Y l ++ alt X Y e)) =
      N X * K + N Y * (l + sumL e) + N X * sumK e := by
    rw [N_append, N_append, N_wpow, N_wpow, N_alt]; ring
  have hNw : 0 < N (wpow X K ++ (wpow Y l ++ alt X Y e)) := by
    rw [hNeq]; have := Nat.mul_pos (lt_of_lt_of_le hrX hNX) hK; omega
  have hrw : 0 < r (wpow X K ++ (wpow Y l ++ alt X Y e)) := by
    rw [r_append, r_wpow]; have := Nat.mul_pos hrX hK; omega
  -- Lemma 7.1, exact form: `M_w (c_X - M_X y) = 2^(nK) D(X, Y^l ⋯) = 2^(nK) β D(X, Y)`
  have hD : D X (wpow Y l ++ alt X Y e) =
      (3 ^ r (alt X Y e) * F Y l + 2 ^ (N Y * l) * altβ X Y e) * D X Y := by
    rw [D_append, D_wpow, D_alt, D_self, N_wpow]; ring
  rw [hD] at key
  -- so `M_w` divides `β`
  have hdvd : M (wpow X K ++ (wpow Y l ++ alt X Y e)) ∣
      3 ^ r (alt X Y e) * F Y l + 2 ^ (N Y * l) * altβ X Y e := by
    have d1 : M (wpow X K ++ (wpow Y l ++ alt X Y e)) ∣
        D X Y * (2 ^ (N X * K) * (3 ^ r (alt X Y e) * F Y l + 2 ^ (N Y * l) * altβ X Y e)) :=
      ⟨c X - M X * y, by rw [key]; ring⟩
    exact (isCoprime_M_two_pow hNw _).dvd_of_dvd_mul_left (dvd_of_dvd_D_mul hU hNw hrw d1)
  have hFY := F_pos Y hl
  have hβpos : 0 < 3 ^ r (alt X Y e) * F Y l + 2 ^ (N Y * l) * altβ X Y e :=
    add_pos_of_pos_of_nonneg (mul_pos (by positivity) hFY)
      (mul_nonneg (by positivity) (altβ_nonneg X Y e))
  have hle := Int.le_of_dvd hβpos hdvd
  -- the weight, run by run
  have hβlt : 3 ^ r (alt X Y e) * F Y l + 2 ^ (N Y * l) * altβ X Y e <
      (e.length + 1) * (2 ^ (N Y * (l + sumL e)) * 3 ^ (r X * sumK e)) := by
    have hB := altβ_le hX hY e
    have hFl := F_lt_of_M_pos hY hl
    have hc := three_pow_le_two_pow hY (sumL e)
    have e1 : (3 : ℤ) ^ r (alt X Y e) = 3 ^ (r X * sumK e) * 3 ^ (r Y * sumL e) := by
      rw [r_alt, pow_add]
    have e2 : (2 : ℤ) ^ (N Y * (l + sumL e)) = 2 ^ (N Y * l) * 2 ^ (N Y * sumL e) := by
      rw [mul_add, pow_add]
    rw [e1, e2]
    have t1 : (3 : ℤ) ^ (r Y * sumL e) * F Y l ≤ 2 ^ (N Y * sumL e) * F Y l :=
      mul_le_mul_of_nonneg_right hc hFY.le
    have t2 : (2 : ℤ) ^ (N Y * sumL e) * F Y l < 2 ^ (N Y * sumL e) * 2 ^ (N Y * l) :=
      mul_lt_mul_of_pos_left hFl (by positivity)
    have t3 := mul_lt_mul_of_pos_left (lt_of_le_of_lt t1 t2)
      (show (0 : ℤ) < 3 ^ (r X * sumK e) by positivity)
    have t4 := mul_le_mul_of_nonneg_left hB (show (0 : ℤ) ≤ 2 ^ (N Y * l) by positivity)
    linarith
  -- the exponents
  have hS : sumK e ≤ e.length * K := sumK_le hKe
  have h23 : (2 : ℤ) ^ N X ≤ 3 ^ r X := by unfold M at hX; linarith
  have swap := pow_swap_le (p := (2 : ℤ) ^ N X) (q := 3 ^ r X) (by positivity) h23 hS
  simp only [← pow_mul] at swap
  have e1 : (2 : ℤ) ^ (N X * (e.length + 1) * K) = 2 ^ (N X * K) * 2 ^ (N X * (e.length * K)) := by
    rw [← pow_add]; ring_nf
  have e2 : (3 : ℤ) ^ (r X * e.length * K) = 3 ^ (r X * (e.length * K)) := by rw [mul_assoc]
  have e3 : (2 : ℤ) ^ N (wpow X K ++ (wpow Y l ++ alt X Y e)) =
      2 ^ (N X * K) * 2 ^ (N Y * (l + sumL e)) * 2 ^ (N X * sumK e) := by
    rw [hNeq, pow_add, pow_add]
  rw [e1, e2, e3]
  have hab : (0 : ℤ) < 2 ^ (N X * K) * 2 ^ (N X * (e.length * K)) := by positivity
  have i1 := mul_lt_mul_of_pos_right (lt_of_le_of_lt hle hβlt) hab
  have i2 := mul_le_mul_of_nonneg_left swap
    (show (0 : ℤ) ≤ (e.length + 1) * 2 ^ (N Y * (l + sumL e)) * 2 ^ (N X * K) by positivity)
  linarith

/-- **Lemma 6.1, second bracket, at the start of a longest `Y`-run.** The cycle reads
`Y^L X^(k_1) Y^(l_2) ⋯ Y^(l_s) X^(k_s)` from `y`, with `L` at least every other `l_i`. Then
`M_w 3^(a' s L) < s 2^N 2^(n' (s-1) L)`. -/
theorem bracketY_core {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {k L : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) {e : List (ℕ × ℕ)} (hLe : ∀ p ∈ e, p.2 ≤ L)
    {y : ℤ} (hy : 0 < y) (h : IsCycle y (wpow Y L ++ (alt X Y e ++ wpow X k))) :
    M (wpow Y L ++ (alt X Y e ++ wpow X k)) * 3 ^ (r Y * (e.length + 1) * L) <
      (e.length + 1) * 2 ^ N (wpow Y L ++ (alt X Y e ++ wpow X k)) *
        2 ^ (N Y * e.length * L) := by
  have hrX := r_pos_of_M_neg hX
  have hNY : 0 < N Y := N_pos_of_M_ne_zero hY.ne'
  have key := stretch_exact h
  have hNw : 0 < N (wpow Y L ++ (alt X Y e ++ wpow X k)) := by
    rw [N_append, N_wpow]; have := Nat.mul_pos hNY hL; omega
  have hreq : r (wpow Y L ++ (alt X Y e ++ wpow X k)) =
      r Y * L + (r X * sumK e + r Y * sumL e) + r X * k := by
    rw [r_append, r_append, r_wpow, r_wpow, r_alt]; ring
  have hrw : 0 < r (wpow Y L ++ (alt X Y e ++ wpow X k)) := by
    rw [hreq]; have := Nat.mul_pos hrX hk; omega
  have hM := IsCycle.M_pos hy h hNw
  -- Lemma 7.1, exact form: `M_w (c_Y - M_Y y) = 2^(n'L) D(Y, ⋯ X^k) = 2^(n'L) α D(Y, X)`
  have hD : D Y (alt X Y e ++ wpow X k) =
      (3 ^ (r X * k) * altα X Y e + 2 ^ N (alt X Y e) * F X k) * D Y X := by
    rw [D_append, D_wpow, D_alt, D_self, r_wpow]; ring
  rw [hD] at key
  have hdvd : M (wpow Y L ++ (alt X Y e ++ wpow X k)) ∣
      3 ^ (r X * k) * altα X Y e + 2 ^ N (alt X Y e) * F X k := by
    have d1 : M (wpow Y L ++ (alt X Y e ++ wpow X k)) ∣
        D Y X * (2 ^ (N Y * L) * (3 ^ (r X * k) * altα X Y e + 2 ^ N (alt X Y e) * F X k)) :=
      ⟨c Y - M Y * y, by rw [key]; ring⟩
    exact (isCoprime_M_two_pow hNw _).dvd_of_dvd_mul_left (dvd_of_dvd_D_mul hU.symm hNw hrw d1)
  have hFX := F_pos X hk
  have hαpos : 0 < 3 ^ (r X * k) * altα X Y e + 2 ^ N (alt X Y e) * F X k :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (altα_nonneg X Y e))
      (mul_pos (by positivity) hFX)
  have hle := Int.le_of_dvd hαpos hdvd
  -- the weight, run by run
  have hαlt : 3 ^ (r X * k) * altα X Y e + 2 ^ N (alt X Y e) * F X k <
      (e.length + 1) * (2 ^ (N Y * sumL e) * (3 ^ (r X * sumK e) * 3 ^ (r X * k))) := by
    have hA := altα_le hX hY e
    have hFk := F_lt_of_M_neg hX hk
    have hd := two_pow_le_three_pow hX (sumK e)
    have e1 : (2 : ℤ) ^ N (alt X Y e) = 2 ^ (N X * sumK e) * 2 ^ (N Y * sumL e) := by
      rw [N_alt, pow_add]
    rw [e1]
    have t1 : (2 : ℤ) ^ (N X * sumK e) * 2 ^ (N Y * sumL e) * F X k <
        2 ^ (N X * sumK e) * 2 ^ (N Y * sumL e) * 3 ^ (r X * k) :=
      mul_lt_mul_of_pos_left hFk (by positivity)
    have t2 : (2 : ℤ) ^ (N X * sumK e) * 2 ^ (N Y * sumL e) * 3 ^ (r X * k) ≤
        3 ^ (r X * sumK e) * 2 ^ (N Y * sumL e) * 3 ^ (r X * k) := by
      have := mul_le_mul_of_nonneg_right hd
        (show (0 : ℤ) ≤ 2 ^ (N Y * sumL e) * 3 ^ (r X * k) by positivity)
      linarith
    have t3 := mul_le_mul_of_nonneg_left hA (show (0 : ℤ) ≤ 3 ^ (r X * k) by positivity)
    linarith
  -- the exponents
  have hT : sumL e ≤ e.length * L := sumL_le hLe
  have h32 : (3 : ℤ) ^ r Y ≤ 2 ^ N Y := by unfold M at hY; linarith
  have swap := pow_swap_le (p := (3 : ℤ) ^ r Y) (q := 2 ^ N Y) (by positivity) h32 hT
  simp only [← pow_mul] at swap
  have hRN : (3 : ℤ) ^ (r Y * L) * (3 ^ (r X * sumK e) * 3 ^ (r Y * sumL e)) * 3 ^ (r X * k) <
      2 ^ N (wpow Y L ++ (alt X Y e ++ wpow X k)) := by
    have := hM
    unfold M at this
    rw [hreq, pow_add, pow_add, pow_add] at this
    linarith
  have e1 : (3 : ℤ) ^ (r Y * (e.length + 1) * L) = 3 ^ (r Y * L) * 3 ^ (r Y * (e.length * L)) := by
    rw [← pow_add]; ring_nf
  have e2 : (2 : ℤ) ^ (N Y * e.length * L) = 2 ^ (N Y * (e.length * L)) := by rw [mul_assoc]
  rw [e1, e2]
  have hbc : (0 : ℤ) < 3 ^ (r Y * L) * 3 ^ (r Y * (e.length * L)) := by positivity
  have i1 := mul_lt_mul_of_pos_right (lt_of_le_of_lt hle hαlt) hbc
  have i2 := mul_le_mul_of_nonneg_left swap
    (show (0 : ℤ) ≤ (e.length + 1) * (3 ^ (r X * sumK e) * 3 ^ (r X * k)) * 3 ^ (r Y * L) by
      positivity)
  have i3 := mul_le_mul_of_nonneg_left hRN.le
    (show (0 : ℤ) ≤ (e.length + 1) * 2 ^ (N Y * (e.length * L)) by positivity)
  linarith

/-! ### Lemma 6.1 -/

theorem M_congr {u v : Word} (hN : N u = N v) (hr : r u = r v) : M u = M v := by
  unfold M; rw [hN, hr]

/-- **Lemma 6.1, first bracket (integer form).** Let `(X, Y)` be unimodular with `M_X < 0 < M_Y`,
and let an integer cycle read `X^(k_1) Y^(l_1) ⋯ X^(k_s) Y^(l_s)` from `x`, all exponents
at least 1. If `K` is its longest `X`-run, then `M_w 2^(n s K) < s 2^N 3^(a (s-1) K)`. -/
theorem bracket_X_int {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) {x : ℤ}
    (h : IsCycle x (alt X Y e)) {K l : ℕ} (hKl : (K, l) ∈ e) (hKmax : ∀ p ∈ e, p.1 ≤ K) :
    M (alt X Y e) * 2 ^ (N X * e.length * K) <
      e.length * 2 ^ N (alt X Y e) * 3 ^ (r X * (e.length - 1) * K) := by
  have hK : 1 ≤ K := (he (K, l) hKl).1
  have hl : 1 ≤ l := (he (K, l) hKl).2
  obtain ⟨e₁, e₂, rfl⟩ := List.append_of_mem hKl
  rw [alt_append, alt_cons] at h
  obtain ⟨hrot, -⟩ := h.rotate
  have hw : wpow X K ++ (wpow Y l ++ alt X Y e₂) ++ alt X Y e₁ =
      wpow X K ++ (wpow Y l ++ alt X Y (e₂ ++ e₁)) := by
    rw [alt_append]; simp only [List.append_assoc]
  rw [hw] at hrot
  have hKe : ∀ p ∈ e₂ ++ e₁, p.1 ≤ K := fun p hp =>
    hKmax p (by simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto)
  have hcore := bracketX_core hU hX hY hK hl hKe hrot
  have hN : N (alt X Y (e₁ ++ (K, l) :: e₂)) = N (wpow X K ++ (wpow Y l ++ alt X Y (e₂ ++ e₁))) := by
    simp only [alt_append, alt_cons, N_append, N_wpow, N_alt]; ring
  have hr : r (alt X Y (e₁ ++ (K, l) :: e₂)) = r (wpow X K ++ (wpow Y l ++ alt X Y (e₂ ++ e₁))) := by
    simp only [alt_append, alt_cons, r_append, r_wpow, r_alt]; ring
  have hlen : (e₁ ++ (K, l) :: e₂).length = (e₂ ++ e₁).length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  rw [M_congr hN hr, hN, hlen, Nat.add_sub_cancel]
  push_cast
  exact hcore

/-- **Lemma 6.1, second bracket (integer form).** In the setting of `bracket_X_int`, if `L` is the
longest `Y`-run, then `M_w 3^(a' s L) < s 2^N 2^(n' (s-1) L)`. -/
theorem bracket_Y_int {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) {x : ℤ} (hx : 0 < x)
    (h : IsCycle x (alt X Y e)) {k L : ℕ} (hkL : (k, L) ∈ e) (hLmax : ∀ p ∈ e, p.2 ≤ L) :
    M (alt X Y e) * 3 ^ (r Y * e.length * L) <
      e.length * 2 ^ N (alt X Y e) * 2 ^ (N Y * (e.length - 1) * L) := by
  have hk : 1 ≤ k := (he (k, L) hkL).1
  have hL : 1 ≤ L := (he (k, L) hkL).2
  obtain ⟨e₁, e₂, rfl⟩ := List.append_of_mem hkL
  rw [alt_append, alt_cons] at h
  have hsplit : alt X Y e₁ ++ (wpow X k ++ (wpow Y L ++ alt X Y e₂)) =
      (alt X Y e₁ ++ wpow X k) ++ (wpow Y L ++ alt X Y e₂) := by
    simp only [List.append_assoc]
  rw [hsplit] at h
  obtain ⟨hrot, -⟩ := h.rotate
  have hw : wpow Y L ++ alt X Y e₂ ++ (alt X Y e₁ ++ wpow X k) =
      wpow Y L ++ (alt X Y (e₂ ++ e₁) ++ wpow X k) := by
    rw [alt_append]; simp only [List.append_assoc]
  rw [hw] at hrot
  have hLe : ∀ p ∈ e₂ ++ e₁, p.2 ≤ L := fun p hp =>
    hLmax p (by simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto)
  have hcore := bracketY_core hU hX hY hk hL hLe (iterate_T_pos hx _) hrot
  have hN : N (alt X Y (e₁ ++ (k, L) :: e₂)) = N (wpow Y L ++ (alt X Y (e₂ ++ e₁) ++ wpow X k)) := by
    simp only [alt_append, alt_cons, N_append, N_wpow, N_alt]; ring
  have hr : r (alt X Y (e₁ ++ (k, L) :: e₂)) = r (wpow Y L ++ (alt X Y (e₂ ++ e₁) ++ wpow X k)) := by
    simp only [alt_append, alt_cons, r_append, r_wpow, r_alt]; ring
  have hlen : (e₁ ++ (k, L) :: e₂).length = (e₂ ++ e₁).length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  rw [M_congr hN hr, hN, hlen, Nat.add_sub_cancel]
  push_cast
  exact hcore

/-- From `m B < s P A` to `m / P < s (A / B)`. -/
theorem bracket_div_lt {m P s A B : ℝ} (hP : 0 < P) (hB : 0 < B) (h : m * B < s * P * A) :
    m / P < s * (A / B) := by
  rw [div_lt_iff₀ hP, show s * (A / B) * P = s * P * A / B by ring, lt_div_iff₀ hB]
  exact h

/-- **Lemma 6.1 (the two brackets), first bracket.** Let `(X, Y)` be unimodular with
`M_X < 0 < M_Y`, and let an integer cycle read `X^(k_1) Y^(l_1) ⋯ X^(k_s) Y^(l_s)` from `x`,
all exponents at least 1. If `K` is its longest `X`-run, then
`M_w / 2^N < s (3^(a(s-1)) / 2^(ns))^K`. -/
theorem bracket_X {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) {x : ℤ}
    (h : IsCycle x (alt X Y e)) {K l : ℕ} (hKl : (K, l) ∈ e) (hKmax : ∀ p ∈ e, p.1 ≤ K) :
    ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e) <
      e.length * ((3 : ℝ) ^ (r X * (e.length - 1)) / 2 ^ (N X * e.length)) ^ K := by
  have hI := bracket_X_int hU hX hY he h hKl hKmax
  have hI' : ((M (alt X Y e) : ℤ) : ℝ) * 2 ^ (N X * e.length * K) <
      e.length * 2 ^ N (alt X Y e) * 3 ^ (r X * (e.length - 1) * K) := by exact_mod_cast hI
  rw [div_pow, ← pow_mul, ← pow_mul]
  exact bracket_div_lt (by positivity) (by positivity) hI'

/-- **Lemma 6.1 (the two brackets), second bracket.** In the setting of `bracket_X`, if `L` is the
longest `Y`-run, then `M_w / 2^N < s (2^(n'(s-1)) / 3^(a's))^L`. -/
theorem bracket_Y {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) {x : ℤ} (hx : 0 < x)
    (h : IsCycle x (alt X Y e)) {k L : ℕ} (hkL : (k, L) ∈ e) (hLmax : ∀ p ∈ e, p.2 ≤ L) :
    ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e) <
      e.length * ((2 : ℝ) ^ (N Y * (e.length - 1)) / 3 ^ (r Y * e.length)) ^ L := by
  have hI := bracket_Y_int hU hX hY he hx h hkL hLmax
  have hI' : ((M (alt X Y e) : ℤ) : ℝ) * 3 ^ (r Y * e.length * L) <
      e.length * 2 ^ N (alt X Y e) * 2 ^ (N Y * (e.length - 1) * L) := by exact_mod_cast hI
  rw [div_pow, ← pow_mul, ← pow_mul]
  exact bracket_div_lt (by positivity) (by positivity) hI'

/-- **Lemma 6.1 (the two brackets).** Both bounds at once, with `K` and `L` the longest `X`-run and
`Y`-run. -/
theorem two_brackets {X Y : Word} (hU : Unimodular X Y) (hX : M X < 0) (hY : 0 < M Y)
    {e : List (ℕ × ℕ)} (he : ∀ p ∈ e, 1 ≤ p.1 ∧ 1 ≤ p.2) {x : ℤ} (hx : 0 < x)
    (h : IsCycle x (alt X Y e)) {K l k L : ℕ} (hKl : (K, l) ∈ e) (hKmax : ∀ p ∈ e, p.1 ≤ K)
    (hkL : (k, L) ∈ e) (hLmax : ∀ p ∈ e, p.2 ≤ L) :
    ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e) <
        e.length * ((3 : ℝ) ^ (r X * (e.length - 1)) / 2 ^ (N X * e.length)) ^ K ∧
      ((M (alt X Y e) : ℤ) : ℝ) / 2 ^ N (alt X Y e) <
        e.length * ((2 : ℝ) ^ (N Y * (e.length - 1)) / 3 ^ (r Y * e.length)) ^ L :=
  ⟨bracket_X hU hX hY he h hKl hKmax, bracket_Y hU hX hY he hx h hkL hLmax⟩

end TwoBlock
