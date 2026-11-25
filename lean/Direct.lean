import ArithmeticBounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# Gaussian energy gap on the half-integer grid
`shellCoeff` is the difference of signed pair counts (displaced minus uniform)
in both directions, with one entry for every distance modulo eight half-steps.
The model module obtains these counts by enumerating the labeled particle pairs.
The series below omits zero distance. The argument uses real-space distances only.
-/

namespace AlternatingGaussian.Direct

open AlternatingChain

def shellCoeff : Fin 8 → ℤ := ![0, -4, 10, -4, -4, -4, 10, -4]

def residue (n : ℕ) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

noncomputable def term (c : Fin 8 → ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  (c (residue (n+1)) : ℝ) * q ^ ((n + 1) ^ 2)

theorem summable_term {c : Fin 8 → ℤ} {B : ℤ}
    (hc : ∀ k, |c k| ≤ B) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (term c q) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg (c 0)) (hc 0)
  have hBR : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (B : ℝ)) ?_
  intro n
  have hmag : |(c (residue (n+1)) : ℝ)| ≤ (B : ℝ) := by
    exact_mod_cast hc (residue (n+1))
  have hexp : n ≤ (n + 1) ^ 2 := by nlinarith [Nat.le_mul_self n]
  rw [term, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
  exact mul_le_mul hmag (pow_le_pow_of_le_one hq0 hq1.le hexp)
    (pow_nonneg hq0 _) hBR

private theorem shell_floor : ∀ k, -4 ≤ shellCoeff k := by decide
private theorem shell_abs : ∀ k, |shellCoeff k| ≤ 10 := by decide

private theorem head_sum (q : ℝ) :
    ∑ n ∈ Finset.range 8, term shellCoeff q n = 2 * headPoly q := by
  norm_num [Finset.sum_range_succ, term, shellCoeff, residue, headPoly]
  ring

private theorem weight_nonnegative : 0 ≤ weight := by linarith [weight_bounds.1]

private theorem weight_lt_one : weight < 1 := by linarith [weight_bounds.2]

/-- The tail starts at half-grid distance 9. It admits a geometric minorant
whose ratio is one half, since (9+n)^2 ≥ 81+19n. -/
private theorem tail_pointwise (n : ℕ) :
    (-(1 : ℝ) / 36) * (1/2 : ℝ)^n ≤ term shellCoeff weight (n+8) := by
  have he : 81 + 19*n ≤ (n+8+1)^2 := by
    nlinarith only [Nat.le_mul_self n]
  have hpow : weight^((n+8+1)^2) ≤ (1/144 : ℝ)*(1/2 : ℝ)^n := by
    calc
      weight^((n+8+1)^2) ≤ weight^(81 + 19*n) :=
        pow_le_pow_of_le_one weight_nonnegative weight_lt_one.le he
      _ = weight^81 * (weight^19)^n := by rw [pow_add, pow_mul]
      _ ≤ (1/144 : ℝ)*(1/2 : ℝ)^n :=
        mul_le_mul weight_pow81.le
          (pow_le_pow_left₀ (pow_nonneg weight_nonnegative 19) weight_pow19.le n)
          (pow_nonneg (pow_nonneg weight_nonnegative 19) n) (by norm_num)
  have hc : (-4 : ℝ) ≤ (shellCoeff (residue (n+8+1)) : ℝ) := by
    exact_mod_cast shell_floor (residue (n+8+1))
  calc
    (-(1 : ℝ)/36)*(1/2 : ℝ)^n =
        (-4 : ℝ)*((1/144 : ℝ)*(1/2 : ℝ)^n) := by ring
    _ ≤ (-4 : ℝ)*weight^((n+8+1)^2) := mul_le_mul_of_nonpos_left hpow (by norm_num)
    _ ≤ term shellCoeff weight (n+8) :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg weight_nonnegative _)

/-- A rational lower bound for the full infinite difference of directed pair sums. -/
theorem shell_margin : (1/9 : ℝ) < ∑' n : ℕ, term shellCoeff weight n := by
  have hs := summable_term shell_abs weight weight_nonnegative weight_lt_one
  have hshift : Summable (fun n : ℕ => term shellCoeff weight (n+8)) :=
    (summable_nat_add_iff 8).2 hs
  have hg : HasSum (fun n : ℕ => (-(1 : ℝ)/36)*(1/2 : ℝ)^n) ((-(1 : ℝ)/36)*2) :=
    hasSum_geometric_two.mul_left (-(1 : ℝ)/36)
  have htail := Summable.tsum_le_tsum tail_pointwise hg.summable hshift
  rw [hg.tsum_eq] at htail
  have split := hs.sum_add_tsum_nat_add 8
  rw [head_sum] at split
  linarith [headPoly_lower]

theorem shell_positive : 0 < ∑' n : ℕ, term shellCoeff weight n :=
  lt_trans (by norm_num : (0 : ℝ) < 1/9) shell_margin

#print axioms shell_margin
#print axioms shell_positive

end AlternatingGaussian.Direct
