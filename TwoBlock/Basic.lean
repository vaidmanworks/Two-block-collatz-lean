import Mathlib

/-!
# Parity words and the Collatz map

Section 1 of the paper.

`T(x) = x/2` for even `x` and `(3x + 1)/2` for odd `x`, on all of `ℤ` (the original map, target 1).
A parity word is a list of booleans: `true` is the letter 1 (an odd step), `false` is the letter 0.
For a word `w`:
* `N w` is its length and `r w` its number of ones;
* `c w = Σ_j 3^(r-1-j) 2^(i_j)` over the positions `i_0 < … < i_(r-1)` of its ones, defined here by the
  recursion for prepending a letter;
* `M w = 2^N - 3^r` is its modulus;
* `D X Y = c_X M_Y - c_Y M_X` is the minor of a pair.
-/

namespace TwoBlock

/-- The Collatz map `T`. -/
def T (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

theorem two_mul_T_of_even {x : ℤ} (h : x % 2 = 0) : 2 * T x = x := by
  unfold T; rw [if_pos h]; omega

theorem two_mul_T_of_odd {x : ℤ} (h : x % 2 = 1) : 2 * T x = 3 * x + 1 := by
  unfold T; rw [if_neg (by omega)]; omega

/-- A parity word: `true` is the letter 1, `false` the letter 0. -/
abbrev Word := List Bool

/-- The length `N(w)`. -/
def N (w : Word) : ℕ := w.length

/-- The number of ones `r(w)`. -/
def r (w : Word) : ℕ := w.count true

/-- The constant `c_w` of the affine map `f_w(x) = (3^r x + c_w) / 2^N`. -/
def c : Word → ℤ
  | [] => 0
  | false :: w => 2 * c w
  | true :: w => 3 ^ r w + 2 * c w

/-- The modulus `M_w = 2^N - 3^r`. -/
def M (w : Word) : ℤ := 2 ^ N w - 3 ^ r w

/-- The minor `D(X, Y) = c_X M_Y - c_Y M_X`. -/
def D (X Y : Word) : ℤ := c X * M Y - c Y * M X

@[simp] theorem N_nil : N [] = 0 := rfl
@[simp] theorem N_cons (b : Bool) (w : Word) : N (b :: w) = N w + 1 := rfl
@[simp] theorem N_append (u v : Word) : N (u ++ v) = N u + N v := by simp [N]

@[simp] theorem r_nil : r [] = 0 := rfl
@[simp] theorem r_cons_true (w : Word) : r (true :: w) = r w + 1 := by simp [r]
@[simp] theorem r_cons_false (w : Word) : r (false :: w) = r w := by simp [r]
@[simp] theorem r_append (u v : Word) : r (u ++ v) = r u + r v := by simp [r]

theorem r_le_N (w : Word) : r w ≤ N w := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp only [r_cons_false, r_cons_true, N_cons] <;> omega

@[simp] theorem c_nil : c [] = 0 := rfl
@[simp] theorem c_cons_false (w : Word) : c (false :: w) = 2 * c w := rfl
@[simp] theorem c_cons_true (w : Word) : c (true :: w) = 3 ^ r w + 2 * c w := rfl

/-- **Fact 1.2 (concatenation).** `c_(uv) = 3^r(v) c_u + 2^N(u) c_v`. -/
theorem c_append (u v : Word) : c (u ++ v) = 3 ^ r v * c u + 2 ^ N u * c v := by
  induction u with
  | nil => simp
  | cons b u ih =>
    cases b
    · rw [List.cons_append, c_cons_false, c_cons_false, ih, N_cons]; ring
    · rw [List.cons_append, c_cons_true, c_cons_true, ih, r_append, N_cons]; ring

/-- **Fact 1.2 (concatenation).** `M_(uv) = 3^r(v) M_u + 2^N(u) M_v`. -/
theorem M_append (u v : Word) : M (u ++ v) = 3 ^ r v * M u + 2 ^ N u * M v := by
  simp only [M, N_append, r_append]; ring

theorem c_nonneg (w : Word) : 0 ≤ c w := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have h3 : (0 : ℤ) < 3 ^ r w := by positivity
    cases b
    · rw [c_cons_false]; linarith
    · rw [c_cons_true]; linarith

theorem c_eq_zero_of_r_eq_zero {w : Word} (h : r w = 0) : c w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · rw [c_cons_false, ih (by simpa using h), mul_zero]
    · simp at h

/-- With the ones placed last `c_w` is largest; the bound used here is `2^r c_w < 2^N 3^r`. -/
theorem c_bound (w : Word) : 2 ^ r w * c w < 2 ^ N w * 3 ^ r w := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have hrN : (2 : ℤ) ^ r w ≤ 2 ^ N w := pow_le_pow_right₀ (by norm_num) (r_le_N w)
    have hc := c_nonneg w
    have h3 : (0 : ℤ) < 3 ^ r w := by positivity
    cases b
    · simp only [r_cons_false, c_cons_false, N_cons, pow_succ]; linarith
    · simp only [r_cons_true, c_cons_true, N_cons, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hrN h3.le]

theorem c_lt_three_pow (w : Word) : c w < 3 ^ N w := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have hrN : (3 : ℤ) ^ r w ≤ 3 ^ N w := pow_le_pow_right₀ (by norm_num) (r_le_N w)
    have p3 : (0 : ℤ) < 3 ^ N w := by positivity
    cases b
    · simp only [c_cons_false, N_cons, pow_succ]; linarith
    · simp only [c_cons_true, N_cons, pow_succ]; linarith

theorem abs_M_le (w : Word) : |M w| ≤ 3 ^ N w := by
  have h2 : (2 : ℤ) ^ N w ≤ 3 ^ N w := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h3 : (3 : ℤ) ^ r w ≤ 3 ^ N w := pow_le_pow_right₀ (by norm_num) (r_le_N w)
  have p2 : (0 : ℤ) < 2 ^ N w := by positivity
  have p3 : (0 : ℤ) < 3 ^ r w := by positivity
  rw [M, abs_sub_le_iff]; constructor <;> linarith

/-! ### Following a word, and cycles -/

/-- `Follows x w`: the next `N w` steps of `x` under `T` have the parities of `w`. -/
def Follows : ℤ → Word → Prop
  | _, [] => True
  | x, b :: w => (x % 2 = 1 ↔ b = true) ∧ Follows (T x) w

/-- The affine form of a stretch: `2^N T^N(x) = 3^r x + c_w`, i.e. `T^N(x) = f_w(x)`. -/
theorem follows_iterate {x : ℤ} {w : Word} (h : Follows x w) :
    2 ^ N w * T^[N w] x = 3 ^ r w * x + c w := by
  induction w generalizing x with
  | nil => simp
  | cons b w ih =>
    obtain ⟨hb, hw⟩ := h
    have hT := ih hw
    rw [N_cons, Function.iterate_succ_apply]
    cases b
    · have hx0 : x % 2 = 0 := by simp at hb; omega
      have h2 := two_mul_T_of_even hx0
      rw [r_cons_false, c_cons_false]
      linear_combination 2 * hT + 3 ^ r w * h2
    · have h2 := two_mul_T_of_odd (by simpa using hb)
      rw [r_cons_true, c_cons_true]
      linear_combination 2 * hT + 3 ^ r w * h2

theorem follows_append {x : ℤ} {u v : Word} :
    Follows x (u ++ v) ↔ Follows x u ∧ Follows (T^[N u] x) v := by
  induction u generalizing x with
  | nil => simp [Follows]
  | cons b u ih =>
    rw [List.cons_append, N_cons, Function.iterate_succ_apply]
    simp only [Follows, ih, and_assoc]

/-- `x` is a point of an integer cycle whose parity vector, read from `x`, is `w`. -/
def IsCycle (x : ℤ) (w : Word) : Prop := Follows x w ∧ T^[N w] x = x

/-- **Fact 1.1 (cycle points)**, the direction used: a cycle point at the start of `w` satisfies
`x · M_w = c_w`, i.e. `x = p_w`. -/
theorem IsCycle.eq {x : ℤ} {w : Word} (h : IsCycle x w) : x * M w = c w := by
  have := follows_iterate h.1
  rw [h.2] at this
  unfold M; linear_combination this

/-- Reading a cycle from a later point: if `x` runs through `u ++ v` and returns, then the point
after `u` runs through `v ++ u` and returns, and `v` leads it back to `x`. -/
theorem IsCycle.rotate {x : ℤ} {u v : Word} (h : IsCycle x (u ++ v)) :
    IsCycle (T^[N u] x) (v ++ u) ∧ T^[N v] (T^[N u] x) = x := by
  obtain ⟨hf, hc⟩ := h
  rw [follows_append] at hf
  obtain ⟨hu, hv⟩ := hf
  have hback : T^[N v] (T^[N u] x) = x := by
    rw [← Function.iterate_add_apply, show N v + N u = N (u ++ v) by rw [N_append]; omega]
    exact hc
  refine ⟨⟨follows_append.mpr ⟨hv, by rw [hback]; exact hu⟩, ?_⟩, hback⟩
  rw [N_append, Nat.add_comm, Function.iterate_add_apply, hback]

/-! ### Positivity and the trivial cycle -/

theorem T_pos {x : ℤ} (hx : 0 < x) : 0 < T x := by
  unfold T; split_ifs <;> omega

theorem iterate_T_pos {x : ℤ} (hx : 0 < x) (m : ℕ) : 0 < T^[m] x := by
  induction m generalizing x with
  | zero => simpa using hx
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih (T_pos hx)

theorem T_one : T 1 = 2 := by norm_num [T]

theorem T_two : T 2 = 1 := by norm_num [T]

theorem iterate_T_trivial {y : ℤ} (hy : y = 1 ∨ y = 2) (m : ℕ) : T^[m] y = 1 ∨ T^[m] y = 2 := by
  induction m generalizing y with
  | zero => simpa using hy
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    rcases hy with rfl | rfl
    · right; exact T_one
    · left; exact T_two

/-- A periodic point whose orbit reaches 1 lies on the trivial cycle `1 → 2 → 1`. -/
theorem eq_one_or_two_of_reaches {x : ℤ} {n : ℕ} (hn : 0 < n) (hc : T^[n] x = x) {m : ℕ}
    (hm : T^[m] x = 1) : x = 1 ∨ x = 2 := by
  have hper : ∀ j : ℕ, T^[n * j] x = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [mul_add_one, Function.iterate_add_apply, hc, ih]
  have hle : m ≤ n * m := Nat.le_mul_of_pos_left m hn
  have key : T^[n * m - m] 1 = x := by
    rw [← hm, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, hper]
  rw [← key]
  exact iterate_T_trivial (Or.inl rfl) _

end TwoBlock
