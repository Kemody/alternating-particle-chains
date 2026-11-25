import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
In the terminology of Conjecture 2.7 the potential is f(r) = F(r²).
This file verifies the alternating signs of all derivatives of F. The result
is independent of the energy comparison for the two periodic configurations.
-/
namespace AlternatingParticleChains

/-- The potential as a function of squared distance. -/
noncomputable def squaredDistanceProfile (s : ℝ) : ℝ := Real.exp ((-1 / 4 : ℝ) * s)

/-- The defining derivative inequalities for complete monotonicity, with
strict signs at every real argument, in particular for positive arguments. -/
theorem gaussian_profile_completely_monotone (n : ℕ) (s : ℝ) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredDistanceProfile s := by
  change 0 < (-1 : ℝ) ^ n * (iteratedDeriv n (fun x : ℝ => Real.exp ((-1 / 4 : ℝ) * x))) s
  rw [iteratedDeriv_exp_const_mul]
  change 0 < (-1 : ℝ) ^ n * ((-1 / 4 : ℝ) ^ n * Real.exp ((-1 / 4 : ℝ) * s))
  rw [← mul_assoc, ← mul_pow]
  exact mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)

/-- A profile for the specific Gaussian, in the distance convention of the paper. -/
theorem gaussian_has_admissible_profile :
    ∃ F : ℝ → ℝ, (∀ r : ℝ, Real.exp (-(r ^ 2) / 4) = F (r ^ 2)) ∧
      ∀ (n : ℕ) (s : ℝ), 0 ≤ s → 0 < (-1 : ℝ)^n * iteratedDeriv n F s := by
  refine ⟨squaredDistanceProfile, ?_, fun n s _ => gaussian_profile_completely_monotone n s⟩
  intro r
  unfold squaredDistanceProfile
  congr 1
  ring

#print axioms gaussian_profile_completely_monotone
#print axioms gaussian_has_admissible_profile

end AlternatingParticleChains
