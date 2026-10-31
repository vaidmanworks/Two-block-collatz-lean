import TwoBlock.Basic

/-!
# Powers of a word and the two-block cycle equation

Section 2 of the paper (Lemma 2.1) and Lemma 5.1 (words over a pair).
-/

namespace TwoBlock

/-- The geometric sum `Σ_{i<k} p^(k-1-i) q^i`, by its recursion in `k`. -/
def geom (p q : ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => q * geom p q k + p ^ k

@[simp] theorem geom_zero (p q : ℤ) : geom p q 0 = 0 := rfl

theorem geom_succ (p q : ℤ) (k : ℕ) : geom p q (k + 1) = q * geom p q k + p ^ k := rfl

theorem sub_mul_geom (p q : ℤ) (k : ℕ) : (p - q) * geom p q k = p ^ k - q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [geom_succ]; linear_combination q * ih

theorem geom_nonneg {p q : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) : 0 ≤ geom p q k := by
  induction k with
  | zero => simp
  | succ k ih => rw [geom_succ]; exact add_nonneg (mul_nonneg hq ih) (pow_nonneg hp k)

theorem geom_pos {p q : ℤ} (hp : 0 < p) (hq : 0 ≤ q) {k : ℕ} (hk : 1 ≤ k) : 0 < geom p q k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [geom_succ]
  exact add_pos_of_nonneg_of_pos (mul_nonneg hq (geom_nonneg hp.le hq j)) (pow_pos hp j)

/-- The word `X^k`. -/
def wpow (X : Word) : ℕ → Word
  | 0 => []
  | k + 1 => wpow X k ++ X

@[simp] theorem wpow_zero (X : Word) : wpow X 0 = [] := rfl

theorem wpow_succ (X : Word) (k : ℕ) : wpow X (k + 1) = wpow X k ++ X := rfl

@[simp] theorem N_wpow (X : Word) (k : ℕ) : N (wpow X k) = N X * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [wpow_succ, N_append, ih]; ring

@[simp] theorem r_wpow (X : Word) (k : ℕ) : r (wpow X k) = r X * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [wpow_succ, r_append, ih]; ring

/-- The geometric sum `F_k(X) = (2^(nk) - 3^(ak)) / (2^n - 3^a) = Σ_{i<k} 2^(n(k-1-i)) 3^(ai)`. -/
def F (X : Word) (k : ℕ) : ℤ := geom (2 ^ N X) (3 ^ r X) k

theorem F_pos (X : Word) {k : ℕ} (hk : 1 ≤ k) : 0 < F X k :=
  geom_pos (by positivity) (by positivity) hk

theorem M_mul_F (X : Word) (k : ℕ) : M X * F X k = 2 ^ (N X * k) - 3 ^ (r X * k) := by
  rw [M, F, sub_mul_geom, pow_mul, pow_mul]

/-- When `M_X > 0`, `F_k(X) < 2^(nk)`. -/
theorem F_lt_of_M_pos {X : Word} (h : 0 < M X) {k : ℕ} (hk : 1 ≤ k) : F X k < 2 ^ (N X * k) := by
  have h1 := M_mul_F X k
  have h2 := F_pos X hk
  have h3 : (0 : ℤ) < 3 ^ (r X * k) := by positivity
  have hM : 1 ≤ M X := by omega
  nlinarith [mul_le_mul_of_nonneg_right hM h2.le]

/-- When `M_X < 0`, `F_k(X) < 3^(ak)`. -/
theorem F_lt_of_M_neg {X : Word} (h : M X < 0) {k : ℕ} (hk : 1 ≤ k) : F X k < 3 ^ (r X * k) := by
  have h1 := M_mul_F X k
  have h2 := F_pos X hk
  have h3 : (0 : ℤ) < 2 ^ (N X * k) := by positivity
  have hM : 1 ≤ -M X := by omega
  nlinarith [mul_le_mul_of_nonneg_right hM h2.le]

theorem c_wpow (X : Word) (k : ℕ) : c (wpow X k) = c X * F X k := by
  induction k with
  | zero => simp [F]
  | succ k ih =>
    rw [wpow_succ, c_append, ih, N_wpow, F, F, geom_succ, pow_mul]; ring

theorem M_wpow (X : Word) (k : ℕ) : M (wpow X k) = M X * F X k := by
  rw [M_mul_F, M, N_wpow, r_wpow]

/-! ### Lemma 2.1 -/

theorem c_two_block (X Y : Word) (k l : ℕ) :
    c (wpow X k ++ wpow Y l) = 3 ^ (r Y * l) * c X * F X k + 2 ^ (N X * k) * c Y * F Y l := by
  rw [c_append, c_wpow, c_wpow, N_wpow, r_wpow]; ring

theorem M_two_block (X Y : Word) (k l : ℕ) :
    M (wpow X k ++ wpow Y l) = 3 ^ (r Y * l) * M X * F X k + 2 ^ (N X * k) * M Y * F Y l := by
  rw [M_append, M_wpow, M_wpow, N_wpow, r_wpow]; ring

/-- **Lemma 2.1.** For `w = X^k Y^l` and `x` with `x M_w = c_w`:
`M (c_X - M_X x) = D(X, Y) 2^(nk) F_l(Y)` and `M (M_Y x - c_Y) = D(X, Y) 3^(a'l) F_k(X)`. -/
theorem two_block_identities {X Y : Word} {k l : ℕ} {x : ℤ}
    (hx : x * M (wpow X k ++ wpow Y l) = c (wpow X k ++ wpow Y l)) :
    M (wpow X k ++ wpow Y l) * (c X - M X * x) = D X Y * (2 ^ (N X * k) * F Y l) ∧
      M (wpow X k ++ wpow Y l) * (M Y * x - c Y) = D X Y * (3 ^ (r Y * l) * F X k) := by
  rw [c_two_block, M_two_block] at hx
  rw [M_two_block]
  unfold D
  constructor
  · linear_combination (-(M X)) * hx
  · linear_combination (M Y) * hx

/-! ### Lemma 5.1: words over a pair -/

/-- The word spelled by a choice sequence over the pair `(X, Y)`: `true ↦ X`, `false ↦ Y`. -/
def spell (X Y : Word) : List Bool → Word
  | [] => []
  | true :: s => X ++ spell X Y s
  | false :: s => Y ++ spell X Y s

/-- **Lemma 5.1.** `(c_w, M_w) = α (c_X, M_X) + β (c_Y, M_Y)` with non-negative weights, `α > 0`
when `X` occurs and `β > 0` when `Y` occurs. -/
theorem spell_weights (X Y : Word) (s : List Bool) :
    ∃ α β : ℤ, c (spell X Y s) = α * c X + β * c Y ∧ M (spell X Y s) = α * M X + β * M Y ∧
      0 ≤ α ∧ 0 ≤ β ∧ (true ∈ s → 0 < α) ∧ (false ∈ s → 0 < β) := by
  induction s with
  | nil => exact ⟨0, 0, by simp [spell], by simp [spell, M], le_rfl, le_rfl, by simp, by simp⟩
  | cons b s ih =>
    obtain ⟨α, β, hc, hM, hα, hβ, hαp, hβp⟩ := ih
    have h2X : (0 : ℤ) < 2 ^ N X := by positivity
    have h2Y : (0 : ℤ) < 2 ^ N Y := by positivity
    have h3 : (0 : ℤ) < 3 ^ r (spell X Y s) := by positivity
    cases b
    · refine ⟨2 ^ N Y * α, 3 ^ r (spell X Y s) + 2 ^ N Y * β, ?_, ?_, mul_nonneg h2Y.le hα,
        add_nonneg h3.le (mul_nonneg h2Y.le hβ), ?_, fun _ => add_pos_of_pos_of_nonneg h3
        (mul_nonneg h2Y.le hβ)⟩
      · simp only [spell, c_append, hc]; ring
      · simp only [spell, M_append, hM]; ring
      · intro h; simp at h; exact mul_pos h2Y (hαp h)
    · refine ⟨3 ^ r (spell X Y s) + 2 ^ N X * α, 2 ^ N X * β, ?_, ?_,
        add_nonneg h3.le (mul_nonneg h2X.le hα), mul_nonneg h2X.le hβ,
        fun _ => add_pos_of_pos_of_nonneg h3 (mul_nonneg h2X.le hα), ?_⟩
      · simp only [spell, c_append, hc]; ring
      · simp only [spell, M_append, hM]; ring
      · intro h; simp at h; exact mul_pos h2X (hβp h)

/-- **Lemma 5.1, the minors.** If `x M_w = c_w` then `M_w (M_Y x - c_Y) = α D` and
`M_w (c_X - M_X x) = β D`. -/
theorem spell_minors {X Y : Word} {s : List Bool} {α β x : ℤ}
    (hc : c (spell X Y s) = α * c X + β * c Y) (hM : M (spell X Y s) = α * M X + β * M Y)
    (hx : x * M (spell X Y s) = c (spell X Y s)) :
    M (spell X Y s) * (M Y * x - c Y) = α * D X Y ∧
      M (spell X Y s) * (c X - M X * x) = β * D X Y := by
  rw [hc, hM] at hx
  rw [hM]
  unfold D
  constructor
  · linear_combination (M Y) * hx
  · linear_combination (-(M X)) * hx

theorem N_spell_of_mem {X Y : Word} {s : List Bool} :
    (true ∈ s → N X ≤ N (spell X Y s) ∧ r X ≤ r (spell X Y s)) ∧
      (false ∈ s → N Y ≤ N (spell X Y s) ∧ r Y ≤ r (spell X Y s)) := by
  induction s with
  | nil => simp
  | cons b s ih =>
    cases b
    · refine ⟨fun h => ?_, fun _ => ?_⟩
      · simp at h; have := ih.1 h; simp only [spell, N_append, r_append]; omega
      · simp only [spell, N_append, r_append]; omega
    · refine ⟨fun _ => ?_, fun h => ?_⟩
      · simp only [spell, N_append, r_append]; omega
      · simp at h; have := ih.2 h; simp only [spell, N_append, r_append]; omega

end TwoBlock
