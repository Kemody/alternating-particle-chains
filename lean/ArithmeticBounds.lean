import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Real exponential and moment bounds for the period-four Gaussian chain. -/

namespace AlternatingChain

noncomputable def weight : ℝ := Real.exp (-(1 / 16 : ℝ))

noncomputable def headPoly (t : ℝ) : ℝ :=
  5 * (t^4 + t^36) - 2 * (t + t^9 + t^16 + t^25 + t^49)

theorem weight_pos : 0 < weight := Real.exp_pos _

theorem weight_bounds : (480 : ℝ) / 512 ≤ weight ∧ weight ≤ (481 : ℝ) / 512 := by
  constructor
  · unfold weight
    linarith only [Real.add_one_le_exp (-(1 / 16 : ℝ))]
  · unfold weight
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith only [Real.quadratic_le_exp_of_nonneg (x := (1 / 16 : ℝ)) (by norm_num)]

private theorem lower_pow (n : ℕ) : (480 / 512 : ℝ)^n ≤ weight^n :=
  pow_le_pow_left₀ (by norm_num) weight_bounds.1 n

private theorem upper_pow (n : ℕ) : weight^n ≤ (481 / 512 : ℝ)^n :=
  pow_le_pow_left₀ weight_pos.le weight_bounds.2 n

theorem headPoly_lower : (1 : ℝ) / 12 < headPoly weight := by
  let a : ℝ := 480 / 512
  let b : ℝ := 481 / 512
  have hlow : (1 : ℝ) / 12 <
      5 * (a^4 + a^36) - 2 * (b + b^9 + b^16 + b^25 + b^49) := by
    norm_num [a, b]
  refine hlow.trans_le ?_
  unfold headPoly
  dsimp [a, b]
  linarith only [lower_pow 4, lower_pow 36, weight_bounds.2, upper_pow 9,
     upper_pow 16, upper_pow 25, upper_pow 49]

theorem weight_pow81 : weight^81 < (1 : ℝ) / 144 :=
  (upper_pow 81).trans_lt (by norm_num)

theorem weight_pow19 : weight^19 < (1 : ℝ) / 2 :=
  (upper_pow 19).trans_lt (by norm_num)

#print axioms weight_bounds
#print axioms headPoly_lower
#print axioms weight_pow81
#print axioms weight_pow19

end AlternatingChain
