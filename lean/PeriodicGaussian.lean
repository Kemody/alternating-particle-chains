import ParticleEnergy
import ImageReindex
import Mathlib.Algebra.BigOperators.Fin

/-! Direct ordered-pair energy on the infinite periodic chain. The outer
sums range over the four labeled particles in one cell; m translates the
second particle by a whole period. Only the zero separation is removed.
The coefficient comparison uses increasing positive half-grid distances. -/
namespace AlternatingGaussian.PhysicalCell

open AlternatingGaussian.Direct AlternatingChain

/-- Charge-weighted interaction in half-grid distance units, with zero
separation omitted. -/
noncomputable def pairWeight (i j : Fin 4) (q : ℝ) (d : ℤ) : ℝ :=
  if d = 0 then 0 else (sign i * sign j : ℤ) * q ^ (d.natAbs ^ 2)

noncomputable def periodEnergy (p : Cell) (q : ℝ) : ℝ :=
  -(1/4 : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4,
    ∑' m : ℤ, pairWeight i j q (displacement p i j m)

/-- Coefficient for one specified directed displacement of a labeled pair. -/
def hit (a b : Fin 8) (i j : Fin 4) (k : Fin 8) : ℤ :=
  if step a k.val = b then sign i * sign j else 0

private theorem hit_bound (a b : Fin 8) (i j : Fin 4) (k : Fin 8) :
    |hit a b i j k| ≤ 1 := by
  unfold hit
  split
  · exact (by decide : ∀ i j : Fin 4, |sign i * sign j| ≤ 1) i j
  · decide

private theorem positive_restriction (p : Cell) (i j : Fin 4) (q : ℝ) (n : ℕ) :
    restrictResidue p i j (pairWeight i j q) (↑(n+1 : ℕ)) =
    term (hit (p i) (p j) i j) q n := by
  simp only [restrictResidue, pairWeight, term, hit, residue, step_periodic,
    matches_pos, Nat.cast_eq_zero, Nat.add_one_ne_zero, if_false, Int.natAbs_natCast]
  split <;> simp

private theorem negative_restriction (p : Cell) (i j : Fin 4) (q : ℝ) (n : ℕ) :
    restrictResidue p i j (pairWeight i j q) (-↑(n+1 : ℕ)) =
    term (hit (p j) (p i) i j) q n := by
  simp only [restrictResidue, pairWeight, term, hit, residue, step_periodic,
    matches_neg, neg_eq_zero, Nat.cast_eq_zero, Nat.add_one_ne_zero, if_false,
    Int.natAbs_neg, Int.natAbs_natCast]
  split <;> simp

private noncomputable def paired (p : Cell) (i j : Fin 4) (q : ℝ) (n : ℕ) : ℝ :=
  term (hit (p i) (p j) i j) q n + term (hit (p j) (p i) i j) q n

private theorem pair_summable (p : Cell) (i j : Fin 4) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable (paired p i j q) :=
  (summable_term (hit_bound (p i) (p j) i j) q hq0 hq1).add
    (summable_term (hit_bound (p j) (p i) i j) q hq0 hq1)

/-- The period-image series of each pair converges absolutely. -/
theorem summable_particle_images (p : Cell) (i j : Fin 4) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℤ => pairWeight i j q (displacement p i j m)) := by
  let g := restrictResidue p i j (pairWeight i j q)
  have hp : Summable fun n : ℕ => g (↑(n+1 : ℕ)) := by
    dsimp only [g]; simp_rw [positive_restriction]
    exact summable_term (hit_bound (p i) (p j) i j) q hq0 hq1
  have hn : Summable fun n : ℕ => g (-↑(n+1 : ℕ)) := by
    dsimp only [g]; simp_rw [negative_restriction]
    exact summable_term (hit_bound (p j) (p i) i j) q hq0 hq1
  have hp0 := (summable_nat_add_iff (f := fun n : ℕ => g (n : ℤ)) 1).1 hp
  have hg : Summable g := Summable.of_nat_of_neg_add_one hp0 (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
  have hi : Function.Injective (displacement p i j) :=
    fun _ _ h => displacement_injective p i j _ _ h
  have h (m : ℤ) : g (displacement p i j m) = pairWeight i j q (displacement p i j m) :=
    if_pos ((matches_iff_image p i j _).2 ⟨m, rfl⟩)
  simpa only [Function.comp_def, h] using hg.comp_injective hi

theorem tsum_translates_to_shells (p : Cell) (i j : Fin 4) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' m : ℤ, pairWeight i j q (displacement p i j m)) = ∑' n, paired p i j q n := by
  rw [tsum_period_images]
  have h0 : restrictResidue p i j (pairWeight i j q) 0 = 0 := by simp [restrictResidue, pairWeight]
  have hp : Summable fun n : ℕ => restrictResidue p i j (pairWeight i j q) (↑(n+1 : ℕ)) := by
    simp_rw [positive_restriction]
    exact summable_term (hit_bound (p i) (p j) i j) q hq0 hq1
  have hn : Summable fun n : ℕ => restrictResidue p i j (pairWeight i j q) (-↑(n+1 : ℕ)) := by
    simp_rw [negative_restriction]
    exact summable_term (hit_bound (p j) (p i) i j) q hq0 hq1
  rw [tsum_signed_shells _ h0 hp hn]
  simp_rw [positive_restriction, negative_restriction, paired]

private theorem signed_counts (p : Cell) (k : Fin 8) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      (hit (p i) (p j) i j k + hit (p j) (p i) i j k)) = pairShell p k := by
  simp only [Fin.sum_univ_four, pairShell, sumFour, hit]

private theorem sum_paired (p : Cell) (q : ℝ) (n : ℕ) :
    (∑ i : Fin 4, ∑ j : Fin 4, paired p i j q n) = term (pairShell p) q n := by
  unfold paired term
  rw [← signed_counts]
  push_cast
  simp only [Finset.sum_mul, add_mul]

/-- The textbook particle-by-particle and period-by-period sum equals its
increasing-distance shell expansion. -/
theorem periodEnergy_eq_energy (p : Cell) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    periodEnergy p q = energy p q := by
  unfold periodEnergy energy
  congr 1
  simp_rw [tsum_translates_to_shells p _ _ q hq0 hq1]
  have hs (i j : Fin 4) := pair_summable p i j q hq0 hq1
  have h' (i : Fin 4) :
      (∑ j : Fin 4, ∑' n, paired p i j q n) =
      ∑' n, ∑ j : Fin 4, paired p i j q n :=
    (Summable.tsum_finsetSum (fun j _ => hs i j)).symm
  simp_rw [h']
  rw [← Summable.tsum_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    summable_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => hs i j))]
  simp_rw [sum_paired]

theorem period_energy_counterexample : periodEnergy shifted weight < periodEnergy uniform weight := by
  have hq0 : 0 ≤ weight := by linarith [weight_bounds.1]
  have hq1 : weight < 1 := by linarith [weight_bounds.2]
  rw [periodEnergy_eq_energy shifted _ hq0 hq1, periodEnergy_eq_energy uniform _ hq0 hq1]
  exact gaussian_counterexample

/-- The power appearing in the actual integer-period model is the physical
Gaussian exp(-r²/4) at separation r=|d|/2. -/
theorem gaussian_weight (d : ℤ) :
    weight ^ (d.natAbs ^ 2) = Real.exp (-((d.natAbs : ℝ)/2)^2/4) := by
  unfold weight
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Original distance units, with a length-four period. -/
noncomputable def coordinate (p : Cell) (i : Fin 4) : ℝ := (p i).val / 2

/-- The physical Gaussian energy, summing over all period images of each
ordered pair and deleting only the direct interaction of a label with itself. -/
noncomputable def gaussianEnergy (p : Cell) : ℝ :=
  -(1/4 : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ∑' m : ℤ,
    if i = j ∧ m = 0 then 0 else
      (sign i * sign j : ℤ) *
      Real.exp (-(coordinate p j + 4*(m : ℝ) - coordinate p i)^2/4)

private theorem square_distance (p : Cell) (i j : Fin 4) (m : ℤ) :
    (((displacement p i j m).natAbs : ℝ)/2)^2 =
    (coordinate p j + 4*(m : ℝ) - coordinate p i)^2 := by
  have h (d : ℤ) : (d.natAbs : ℝ) = |(d : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs d)
  rw [h, div_pow, sq_abs]
  unfold coordinate displacement image
  push_cast
  ring

theorem gaussianEnergy_eq (p : Cell) (hp : ordered p) :
    gaussianEnergy p = periodEnergy p weight := by
  unfold gaussianEnergy periodEnergy
  simp only [pairWeight, displacement_eq_zero_iff p hp, gaussian_weight, square_distance]

/-- A strict counterexample for the original Gaussian interaction and the
literal ordered-pair sum over every integer period image. -/
theorem literal_gaussian_counterexample : gaussianEnergy shifted < gaussianEnergy uniform := by
  rw [gaussianEnergy_eq shifted shifted_admissible.1, gaussianEnergy_eq uniform uniform_admissible.1]
  exact period_energy_counterexample

#print axioms literal_gaussian_counterexample
#print axioms periodEnergy_eq_energy
#print axioms period_energy_counterexample
#print axioms gaussian_weight
end AlternatingGaussian.PhysicalCell
