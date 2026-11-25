import PhysicalCellCore
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.Real.Lemmas

/-! Sum over the integer translates of a single labeled pair. A signed
displacement in half-units has an integer periodic image exactly when
the source and target labels satisfy the corresponding residue condition. -/
namespace AlternatingGaussian.PhysicalCell

noncomputable def restrictResidue (p : Cell) (i j : Fin 4) (f : ℤ → ℝ) (d : ℤ) : ℝ :=
  if inResidue (p i) (p j) d then f d else 0

theorem tsum_period_images (p : Cell) (i j : Fin 4) (f : ℤ → ℝ) :
    (∑' m : ℤ, f (displacement p i j m)) =
    ∑' d : ℤ, restrictResidue p i j f d := by
  have h (m : ℤ) : restrictResidue p i j f (displacement p i j m) =
      f (displacement p i j m) := by
    exact if_pos ((matches_iff_image p i j _).2 ⟨m, rfl⟩)
  have hi : Function.Injective (displacement p i j) :=
    fun _ _ h' => displacement_injective p i j _ _ h'
  have hs : Function.support (restrictResidue p i j f) ⊆ Set.range (displacement p i j) := by
    intro d hd
    by_contra h'
    have hn : ¬ inResidue (p i) (p j) d := fun hm => h' ((matches_iff_image p i j d).1 hm)
    exact hd (if_neg hn)
  simpa only [h] using hi.tsum_eq hs

/-- For any absolutely summable profile which vanishes at zero, the full
integer sum is the sum over strictly positive distances in both directions. -/
theorem tsum_signed_shells (f : ℤ → ℝ) (hf0 : f 0 = 0)
    (hp : Summable (fun n : ℕ => f ((n+1 : ℕ) : ℤ)))
    (hn : Summable (fun n : ℕ => f (-((n+1 : ℕ) : ℤ)))) :
    (∑' d : ℤ, f d) =
    ∑' n : ℕ, (f ((n+1 : ℕ) : ℤ) + f (-((n+1 : ℕ) : ℤ))) := by
  have hp0 := (summable_nat_add_iff (f := fun n : ℕ => f (n : ℤ)) 1).1 hp
  have hn' : Summable fun n : ℕ => f (-(↑n + 1)) := by simpa using hn
  rw [tsum_of_nat_of_neg_add_one hp0 hn', hp.tsum_add hn]
  have hs := hp0.sum_add_tsum_nat_add 1
  simp [hf0] at hs
  rw [← hs]
  simp

#print axioms tsum_period_images
#print axioms tsum_signed_shells
end AlternatingGaussian.PhysicalCell
