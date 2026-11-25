import PeriodicGaussian

/-! Quantitative form of the strict Gaussian counterexample, in the original
distance and energy units. The definition of `gaussianEnergy` uses the actual
real-valued sites and exp(−r²/4) and removes exactly the pair i=j, m=0. -/
namespace AlternatingGaussian.PhysicalCell

open AlternatingChain AlternatingGaussian.Direct

theorem gaussian_energy_gap :
    (1/36 : ℝ) < gaussianEnergy uniform - gaussianEnergy shifted := by
  have h0 : 0 ≤ weight := weight_pos.le
  have h1 : weight < 1 := by linarith [weight_bounds.2]
  rw [gaussianEnergy_eq uniform uniform_admissible.1,
      gaussianEnergy_eq shifted shifted_admissible.1,
      periodEnergy_eq_energy uniform weight h0 h1,
      periodEnergy_eq_energy shifted weight h0 h1]
  linarith only [energy_difference weight h0 h1, shell_margin]

#print axioms gaussian_energy_gap

end AlternatingGaussian.PhysicalCell
