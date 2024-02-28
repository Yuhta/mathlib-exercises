import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (s : Set ℝ) (s_def : s = { x : ℝ | ∃ d : ℤ, d ≠ 0 ∧ x = (-1) ^ d / d }) : IsLUB s 1 := by
  rw [isLUB_iff_le_iff]
  intro b
  rw [mem_upperBounds, s_def]
  dsimp
  symm
  constructor
  . intro h
    apply h 1
    use -1
    norm_num
  rintro one_le_b x ⟨d, d_nonzero, rfl⟩
  apply le_trans _ one_le_b
  rcases d with d | d
  . simp
    simp at d_nonzero
    have d_pos : 0 < d := Nat.pos_of_ne_zero d_nonzero
    rw [div_le_one (Nat.cast_pos.mpr d_pos)]
    calc (-1 : ℝ) ^ d ≤ |(-1) ^ d| := le_abs_self _
      _ = 1 := abs_neg_one_pow _
      _ ≤ d := Nat.one_le_cast.mpr d_pos
  simp
  have : -1 + -d < (0 : ℝ) := by linarith
  apply (mul_le_mul_right_of_neg this).mp
  rw [div_mul_cancel ((-1) ^ (d + 1))⁻¹ (ne_of_lt this), one_mul]
  have : -1 + -d ≤ (-1 : ℝ) := by linarith
  apply le_trans this
  by_cases h : Even (d + 1)
  . have : (-1) ^ (d + 1) = (1 : ℝ) := h.neg_one_pow
    calc (-1 : ℝ) ≤ 1⁻¹ := by norm_num
      _ = ((-1) ^ (d + 1))⁻¹ := by nth_rw 1 [← this]
  have h : Odd (d + 1) := Nat.odd_iff_not_even.mpr h
  have : (-1) ^ (d + 1) = (-1 : ℝ) := h.neg_one_pow
  calc (-1 : ℝ) ≤ (-1)⁻¹ := by norm_num
    _ = ((-1) ^ (d + 1))⁻¹ := by nth_rw 1 [← this]
