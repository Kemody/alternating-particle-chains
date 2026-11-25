import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Poisson summation for a Gaussian on the circle of length four

The infinite sum over period images of a pair interaction in the paper
equals its cosine series. The cosine spectrum and its absolute convergence
follow from the shifted Jacobi theta formula in Mathlib.
-/
noncomputable section

namespace AlternatingChains.Poisson
open Real

/-- The positive-frequency part of the paper's pair kernel at distance `d`. -/
def pairTerm (d : ℝ) (n : ℕ) : ℝ :=
  Real.cos (((n+1 : ℕ):ℝ) * Real.pi * d / 2) *
    (Real.exp (-(Real.pi ^ 2 / 4))) ^ ((n+1)^2)

private theorem pairTerm_hasSum (d : ℝ) :
    HasSum (pairTerm d) ((1/2:ℝ) *
      (HurwitzZeta.cosKernel (d / 4 : ℝ) (Real.pi / 4) - 1)) := by
  have h := (HurwitzZeta.hasSum_nat_cosKernel₀ (d/4)
    (show 0 < Real.pi / 4 by positivity)).mul_left (1/2 : ℝ)
  refine h.congr_fun fun n => ?_
  unfold pairTerm
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem pairTerm_summable (d : ℝ) : Summable (pairTerm d) :=
  (pairTerm_hasSum d).summable

/-- The sum over the copies of the period converges absolutely. -/
theorem period_images_summable (d : ℝ) :
    Summable (fun k : ℤ => Real.exp (-((d + 4*(k:ℝ))^2)/4)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ht : 0 < (4:ℝ) / Real.pi := by positivity
  apply (HurwitzZeta.hasSum_int_evenKernel (d/4) ht).summable.congr
  intro k
  congr 1
  field_simp
  ring

/-- Poisson summation at a general pair displacement, with period 4 and a=1/4. -/
theorem period_four_gaussian (d : ℝ) :
    (∑' k : ℤ, Real.exp (-((d + 4*(k:ℝ))^2)/4)) =
    (Real.sqrt Real.pi / 2) * (1 + 2 * ∑' n : ℕ, pairTerm d n) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ht : 0 < (4:ℝ) / Real.pi := by positivity
  have hreal := (HurwitzZeta.hasSum_int_evenKernel (d/4) ht).tsum_eq
  have harg (k : ℤ) : -((d + 4*(k:ℝ))^2)/4 =
      -Real.pi * ((k:ℝ) + d/4)^2 * (4/Real.pi) := by
    field_simp
    ring
  simp_rw [harg]
  rw [hreal, HurwitzZeta.evenKernel_functional_equation]
  have hinv : 1 / ((4:ℝ) / Real.pi) = Real.pi / 4 := by field_simp
  have hcoeff : 1 / ((4:ℝ) / Real.pi) ^ (1 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 4)]
    rw [show Real.sqrt (4:ℝ) = 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
    norm_num
  rw [hinv, hcoeff, (pairTerm_hasSum d).tsum_eq]
  ring

end AlternatingChains.Poisson
