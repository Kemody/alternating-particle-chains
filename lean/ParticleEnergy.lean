import Direct
import PhysicalCellCore

/-! Directed, per-particle Gaussian energy of the two explicitly labeled cells.
The spatial cutoff here is by increasing distance. PhysicalCellCore proves
that a shell match is precisely one periodic particle-image interaction. -/
namespace AlternatingGaussian.PhysicalCell

open AlternatingChain AlternatingGaussian.Direct

/-- At nonzero half-grid distance n+1, sum the signed interactions of each
reference particle with each image, in both spatial directions. Divide the
full sum by four and negate it according to the pair-potential convention. -/
noncomputable def energy (p : Cell) (q : ℝ) : ℝ :=
  -(1/4 : ℝ) * ∑' n : ℕ, term (pairShell p) q n

set_option maxRecDepth 30000 in
theorem actual_pair_difference :
    ∀ k : Fin 8, pairShell shifted k - pairShell uniform k = shellCoeff k := by decide

private theorem abs_uniform : ∀ k : Fin 8, |pairShell uniform k| ≤ 8 := by
  intro k
  rw [counts_uniform]
  exact (by decide : ∀ k : Fin 8, |expectedUniform k| ≤ 8) k

private theorem abs_shifted : ∀ k : Fin 8, |pairShell shifted k| ≤ 8 := by
  intro k
  rw [counts_shifted]
  exact (by decide : ∀ k : Fin 8, |expectedShifted k| ≤ 8) k

theorem energy_difference (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    4 * (energy uniform q - energy shifted q) = ∑' n : ℕ, term shellCoeff q n := by
  have hu := summable_term abs_uniform q hq0 hq1
  have hx := summable_term abs_shifted q hq0 hq1
  have h (n : ℕ) : term shellCoeff q n =
      term (pairShell shifted) q n - term (pairShell uniform) q n := by
    simp only [term, ← actual_pair_difference, Int.cast_sub, sub_mul]
  simp_rw [h]
  rw [hx.tsum_sub hu]
  unfold energy
  ring

theorem gaussian_counterexample : energy shifted weight < energy uniform weight := by
  have hq0 : 0 ≤ weight := by linarith [weight_bounds.1]
  have hq1 : weight < 1 := by linarith [weight_bounds.2]
  linarith [energy_difference weight hq0 hq1, shell_positive]

#print axioms actual_pair_difference
#print axioms energy_difference
#print axioms gaussian_counterexample

end AlternatingGaussian.PhysicalCell
