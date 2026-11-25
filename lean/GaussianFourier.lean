import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# The period-four Gaussian counterexample in Fourier coordinates

For the cell (0, 2-t, 2, 2+t), recenter at 2. The positive sites are
then at 0 and -2, the negative sites at ±t. The real Fourier amplitude
is 1 + cos(mπ) - 2 cos(mθ), where θ = πt/2. Squaring this gives `weight`.

The object compared below is explicitly a Fourier series. Identifying it
with the periodized real-space Gaussian energy uses Poisson summation and
is outside this file. The two first-mode calculations, absolute convergence,
tail estimates, and scale bound are proved in the file.
-/

namespace AlternatingChains.Fourier

noncomputable section

open Real

def weight (θ : ℝ) (m : ℕ) : ℝ :=
  (1 + Real.cos ((m : ℝ) * Real.pi) - 2 * Real.cos ((m : ℝ) * θ)) ^ 2

/-- Evaluation against the signed point measure of the cell recentered at 2. -/
def signedSites (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  f (-2) - f (-t) + f 0 - f t

/-- All sixteen signed pair interactions, including the four self terms. -/
def cellPairs (t : ℝ) (kernel : ℝ → ℝ) : ℝ :=
  signedSites t (fun x => signedSites t (fun y => kernel (x - y)))

theorem cellPairs_cos (t : ℝ) (m : ℕ) :
    cellPairs t (fun r => Real.cos (((m : ℝ) * Real.pi / 2) * r)) =
      weight (Real.pi * t / 2) m := by
  have h₂ : (m : ℝ) * Real.pi / 2 * 2 = (m : ℝ) * Real.pi := by ring
  have ht : (m : ℝ) * Real.pi / 2 * t = (m : ℝ) * (Real.pi * t / 2) := by ring
  simp only [cellPairs, signedSites, weight, mul_sub, Real.cos_sub, mul_neg, mul_zero,
    h₂, ht, Real.cos_neg, Real.sin_neg, Real.cos_zero, Real.sin_zero, Real.sin_nat_mul_pi]
  ring

private theorem weight_nonneg (θ : ℝ) (m : ℕ) : 0 ≤ weight θ m :=
  sq_nonneg _

private theorem weight_le (θ : ℝ) (m : ℕ) : weight θ m ≤ 16 := by
  let v := 1 + Real.cos ((m : ℝ) * Real.pi) - 2 * Real.cos ((m : ℝ) * θ)
  have h₁ := Real.neg_one_le_cos ((m : ℝ) * Real.pi)
  have h₂ := Real.cos_le_one ((m : ℝ) * Real.pi)
  have h₃ := Real.neg_one_le_cos ((m : ℝ) * θ)
  have h₄ := Real.cos_le_one ((m : ℝ) * θ)
  have hmin : 0 ≤ 4 + v := by dsimp [v]; linarith
  have hmax : 0 ≤ 4 - v := by dsimp [v]; linarith
  change v ^ 2 ≤ 16
  nlinarith only [mul_nonneg hmin hmax]

theorem uniform_first_mode : weight (Real.pi / 2) 1 = 0 := by
  simp [weight, Real.cos_pi, Real.cos_pi_div_two]

theorem displaced_first_mode : weight (Real.pi / 4) 1 = 2 := by
  simp only [weight, Nat.cast_one, one_mul, Real.cos_pi, Real.cos_pi_div_four]
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def tailTerm (θ q : ℝ) (n : ℕ) : ℝ :=
  weight θ (n + 2) * q ^ ((n + 2) ^ 2)

private theorem tail_compare (θ q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/4) (n : ℕ) :
    tailTerm θ q n ≤ (16 * q ^ 4) * (1/2 : ℝ) ^ n := by
  have hn : 4 + n ≤ (n + 2)^2 := by nlinarith [Nat.zero_le (n ^ 2)]
  have h₁ : q ^ ((n + 2)^2) ≤ q ^ (4 + n) := by
    exact pow_le_pow_of_le_one hq (by linarith) hn
  have h₂ : q ^ n ≤ (1/2 : ℝ) ^ n := by
    gcongr
    linarith
  calc
    tailTerm θ q n ≤ 16 * q ^ ((n + 2)^2) :=
      mul_le_mul_of_nonneg_right (weight_le θ _) (pow_nonneg hq _)
    _ ≤ 16 * q ^ (4 + n) := by gcongr
    _ = (16 * q ^ 4) * q ^ n := by rw [pow_add]; ring
    _ ≤ (16 * q ^ 4) * (1/2 : ℝ) ^ n := by gcongr

private theorem majorant_sum (q : ℝ) :
    HasSum (fun n : ℕ => (16 * q ^ 4) * (1/2 : ℝ) ^ n) (32 * q ^ 4) := by
  convert hasSum_geometric_two.mul_left (16 * q ^ 4) using 1
  ring

theorem tail_summable (θ q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/4) :
    Summable (tailTerm θ q) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (weight_nonneg θ (n + 2)) (pow_nonneg hq _))
    (tail_compare θ q hq hq') (majorant_sum q).summable

theorem tail_upper (θ q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/4) :
    (∑' n : ℕ, tailTerm θ q n) ≤ 32 * q ^ 4 := by
  calc
    _ ≤ ∑' n : ℕ, (16 * q ^ 4) * (1/2 : ℝ) ^ n :=
      (tail_summable θ q hq hq').tsum_le_tsum
        (tail_compare θ q hq hq') (majorant_sum q).summable
    _ = _ := (majorant_sum q).tsum_eq

/-- The zero mode vanishes. The factor two counts both signs of each
nonzero frequency, and the first harmonic is displayed separately. -/
def fourierMass (θ q : ℝ) : ℝ :=
  2 * (weight θ 1 * q + ∑' n : ℕ, tailTerm θ q n)

theorem fourierMass_eq_tsum (θ q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/4) :
    fourierMass θ q = 2 * ∑' n : ℕ, weight θ (n+1) * q^((n+1)^2) := by
  let f : ℕ → ℝ := fun n => weight θ (n+1) * q^((n+1)^2)
  have hs : Summable f := (summable_nat_add_iff 1).mp (tail_summable θ q hq hq')
  change 2 * (weight θ 1 * q + ∑' n : ℕ, tailTerm θ q n) = 2 * ∑' n : ℕ, f n
  rw [hs.tsum_eq_zero_add]
  simp [f, tailTerm, Nat.add_assoc]

theorem mass_strict (q : ℝ) (hq : 0 < q) (hq' : q ≤ 1/4) :
    fourierMass (Real.pi / 2) q < fourierMass (Real.pi / 4) q := by
  have hU := tail_upper (Real.pi / 2) q hq.le hq'
  have hX : 0 ≤ ∑' n : ℕ, tailTerm (Real.pi / 4) q n :=
    tsum_nonneg (fun n => mul_nonneg (weight_nonneg _ _) (pow_nonneg hq.le _))
  have h₃ : q ^ 3 ≤ (1/4 : ℝ) ^ 3 := by gcongr
  have hsmall := mul_le_mul_of_nonneg_left h₃ hq.le
  unfold fourierMass
  rw [uniform_first_mode, displaced_first_mode]
  nlinarith

theorem gaussian_scale : 0 < Real.exp (-(Real.pi ^ 2 / 4)) ∧
    Real.exp (-(Real.pi ^ 2 / 4)) ≤ 1/4 := by
  refine ⟨Real.exp_pos _, ?_⟩
  have hπ : (2 : ℝ) < Real.pi ^ 2 / 4 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he₂ : (4 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have heπ : 4 < Real.exp (Real.pi ^ 2 / 4) :=
    he₂.trans (Real.exp_lt_exp.mpr hπ)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) heπ.le

/-- The physically normalized energies *in Fourier representation* at a=1/4. -/
def fourierEnergy (θ : ℝ) : ℝ :=
  1 - (Real.sqrt (4 * Real.pi) / 16) * fourierMass θ (Real.exp (-(Real.pi ^ 2 / 4)))

theorem displaced_fourier_energy_lt_uniform :
    fourierEnergy (Real.pi / 4) < fourierEnergy (Real.pi / 2) := by
  have h := mass_strict _ gaussian_scale.1 gaussian_scale.2
  have hc : 0 < Real.sqrt (4 * Real.pi) / 16 := by positivity
  unfold fourierEnergy
  linarith only [mul_lt_mul_of_pos_left h hc]

end

end AlternatingChains.Fourier
