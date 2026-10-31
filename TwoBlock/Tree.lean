import TwoBlock.Integrality

/-!
# The Christoffel tree and the path of `log₂ 3`

Section 4 of the paper: Lemma 4.1 (minors along the tree), the determinant identity,
and the pairs on the path of `log₂ 3`.

The tree has root pair `(0, 1)`, and every pair `(u, v)` has the children `(u, uv)` and `(uv, v)`.
-/

namespace TwoBlock

/-- `TreePair d u v`: `(u, v)` is a pair of the Christoffel tree at depth `d`. -/
inductive TreePair : ℕ → Word → Word → Prop
  | root : TreePair 0 [false] [true]
  | left {d : ℕ} {u v : Word} : TreePair d u v → TreePair (d + 1) u (u ++ v)
  | right {d : ℕ} {u v : Word} : TreePair d u v → TreePair (d + 1) (u ++ v) v

/-- **Lemma 4.1.** `D(uv, v) = 3^r(v) D(u, v)`. -/
theorem D_append_left (u v : Word) : D (u ++ v) v = 3 ^ r v * D u v := by
  simp only [D, c_append, M_append]; ring

/-- **Lemma 4.1.** `D(u, uv) = 2^N(u) D(u, v)`. -/
theorem D_append_right (u v : Word) : D u (u ++ v) = 2 ^ N u * D u v := by
  simp only [D, c_append, M_append]; ring

/-- **Lemma 4.1.** `D(0, 1) = -1`. -/
theorem D_root : D [false] [true] = -1 := by simp [D, M]

/-- **Lemma 4.1.** Every pair of the tree has `D(u, v) = -2^i 3^j`; in particular it is unimodular. -/
theorem TreePair.D_eq {d : ℕ} {u v : Word} (h : TreePair d u v) :
    ∃ i j : ℕ, D u v = -(2 ^ i * 3 ^ j) := by
  induction h with
  | root => exact ⟨0, 0, by rw [D_root]; norm_num⟩
  | @left d u v _ ih =>
    obtain ⟨i, j, hij⟩ := ih
    exact ⟨N u + i, j, by rw [D_append_right, hij]; ring⟩
  | @right d u v _ ih =>
    obtain ⟨i, j, hij⟩ := ih
    exact ⟨i, r v + j, by rw [D_append_left, hij]; ring⟩

theorem TreePair.unimodular {d : ℕ} {u v : Word} (h : TreePair d u v) : Unimodular u v := by
  obtain ⟨i, j, hij⟩ := h.D_eq
  exact ⟨i, j, Or.inr hij⟩

/-- The types add along the tree with `N(u) r(v) - N(v) r(u) = 1`. -/
theorem TreePair.det {d : ℕ} {u v : Word} (h : TreePair d u v) : N u * r v = N v * r u + 1 := by
  induction h with
  | root => rfl
  | @left d u v _ ih => simp only [N_append, r_append]; nlinarith [ih]
  | @right d u v _ ih => simp only [N_append, r_append]; nlinarith [ih]

theorem TreePair.N_pos_left {d : ℕ} {u v : Word} (h : TreePair d u v) : 0 < N u := by
  induction h with
  | root => decide
  | @left d u v _ ih => exact ih
  | @right d u v _ ih => simp only [N_append]; omega

/-- `M_w > 0` exactly when the slope `N(w)/r(w)` lies above `log₂ 3`, i.e. `r log 3 < N log 2`. -/
theorem M_pos_iff (w : Word) : 0 < M w ↔ (r w : ℝ) * Real.log 3 < N w * Real.log 2 := by
  have h3 : (0 : ℝ) < 3 ^ r w := by positivity
  have h2 : (0 : ℝ) < 2 ^ N w := by positivity
  rw [← Real.log_pow, ← Real.log_pow, Real.log_lt_log_iff h3 h2, M, sub_pos]
  exact_mod_cast Iff.rfl

/-- `M_w < 0` exactly when the slope `N(w)/r(w)` lies below `log₂ 3`. -/
theorem M_neg_iff (w : Word) : M w < 0 ↔ (N w : ℝ) * Real.log 2 < r w * Real.log 3 := by
  have h3 : (0 : ℝ) < 3 ^ r w := by positivity
  have h2 : (0 : ℝ) < 2 ^ N w := by positivity
  rw [← Real.log_pow, ← Real.log_pow, Real.log_lt_log_iff h2 h3, M, sub_neg]
  exact_mod_cast Iff.rfl

/-- A pair on the path of `log₂ 3` at depth `d`: a tree pair with `N(u)/r(u) > log₂ 3 > N(v)/r(v)`,
i.e. `M_u > 0 > M_v` (`M_pos_iff`, `M_neg_iff`). -/
def OnPath (d : ℕ) (u v : Word) : Prop := TreePair d u v ∧ 0 < M u ∧ M v < 0

/-- The path of `log₂ 3` has a pair at every depth, so the families of Theorem 4.2 are infinitely
many. (Since `2^N ≠ 3^r` for `N ≥ 1`, exactly one child of a path pair is on the path.) -/
theorem exists_onPath (d : ℕ) : ∃ u v : Word, OnPath d u v := by
  induction d with
  | zero => exact ⟨[false], [true], TreePair.root, by simp [M], by simp [M]⟩
  | succ d ih =>
    obtain ⟨u, v, h, hu, hv⟩ := ih
    have hN : 0 < N (u ++ v) := by have := h.N_pos_left; simp only [N_append]; omega
    rcases lt_or_gt_of_ne (M_ne_zero hN) with hneg | hpos
    · exact ⟨u, u ++ v, h.left, hu, hneg⟩
    · exact ⟨u ++ v, v, h.right, hpos, hv⟩

end TwoBlock
