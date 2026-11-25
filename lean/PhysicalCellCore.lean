import Lean

/-! Labeled particles and their periodic images, independently of real analysis.
The coordinates below count half-units. A complete period is eight half-units.
Every offset counts a particular image of a labeled particle on the real line. -/

namespace AlternatingGaussian.PhysicalCell

abbrev Cell := Fin 4 → Fin 8

def uniform : Cell := fun i => match i.val with
  | 0 => 0 | 1 => 2 | 2 => 4 | _ => 6

def shifted : Cell := fun i => match i.val with
  | 0 => 0 | 1 => 3 | 2 => 4 | _ => 5

def sign (i : Fin 4) : Int :=
  if i.val % 2 = 0 then 1 else -1

/-- Each labeled cell occupies four different sites in increasing order. -/
def ordered (p : Cell) : Prop :=
  ∀ i j : Fin 4, i.val < j.val → (p i).val < (p j).val

theorem uniform_admissible : ordered uniform ∧ uniform 0 = 0 := by unfold ordered; decide
theorem shifted_admissible : ordered shifted ∧ shifted 0 = 0 := by unfold ordered; decide

/-- Image of particle j in period m, in half-units. -/
def image (p : Cell) (j : Fin 4) (m : Int) : Int := (p j).val + 8*m

def step (i : Fin 8) (n : Nat) : Fin 8 :=
  ⟨(i.val + n) % 8, Nat.mod_lt _ (by decide)⟩

/-- A positive half-grid displacement selects exactly one image of j if and only
if its residue inResidue. The same lemma with i and j reversed treats the other direction. -/
theorem step_iff_unique_image (p : Cell) (i j : Fin 4) (n : Nat) :
    step (p i) n = p j ↔
    ∃ m : Int, image p j m - image p i 0 = (n : Int) ∧
      ∀ k : Int, image p j k - image p i 0 = (n : Int) → k = m := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    change ((p i).val + n) % 8 = (p j).val at hval
    refine ⟨(((p i).val + n) / 8 : Nat), ?_, ?_⟩
    · simp only [image, Int.mul_zero, Int.add_zero]
      omega
    · intro k hk
      simp only [image, Int.mul_zero, Int.add_zero] at hk
      omega
  · rintro ⟨m, hm, _⟩
    apply Fin.ext
    change ((p i).val + n) % 8 = (p j).val
    have hj := (p j).isLt
    simp only [image, Int.mul_zero, Int.add_zero] at hm
    omega

def sumFour (f : Fin 4 → Int) : Int := f 0 + f 1 + f 2 + f 3

/-- The sum of the signed directed interactions over all four reference labels
and all four image labels, for both displacements ±k. Signs of the interaction
potential and division by four are applied when taking the physical energy. -/
def pairShell (p : Cell) (k : Fin 8) : Int :=
  sumFour fun i => sumFour fun j =>
    (if step (p i) k.val = p j then sign i * sign j else 0) +
    (if step (p j) k.val = p i then sign i * sign j else 0)

theorem step_periodic (a : Fin 8) (n : Nat) : step a (n % 8) = step a n := by
  apply Fin.ext
  change (a.val + n % 8) % 8 = (a.val+n)%8
  omega

/-- These explicit signed pair counts include translates of the reference
particle at nonzero distances that are multiples of a period. -/
def expectedUniform (r : Fin 8) : Int :=
  match r.val with
  | 0 => 8 | 2 => -8 | 4 => 8 | 6 => -8 | _ => 0

def expectedShifted (r : Fin 8) : Int :=
  match r.val with
  | 0 => 8 | 1 => -4 | 2 => 2 | 3 => -4
  | 4 => 4 | 5 => -4 | 6 => 2 | _ => -4

set_option maxRecDepth 30000 in
theorem counts_uniform : ∀ k : Fin 8, pairShell uniform k = expectedUniform k := by decide
set_option maxRecDepth 30000 in
theorem counts_shifted : ∀ k : Fin 8, pairShell shifted k = expectedShifted k := by decide

#print axioms uniform_admissible
#print axioms shifted_admissible
#print axioms step_iff_unique_image
#print axioms step_periodic
#print axioms counts_uniform
#print axioms counts_shifted
end AlternatingGaussian.PhysicalCell

namespace AlternatingGaussian.PhysicalCell

/-- Signed displacement from a reference label to an arbitrary period image. -/
def displacement (p : Cell) (i j : Fin 4) (m : Int) : Int :=
  image p j m - image p i 0

def inResidue (a b : Fin 8) (d : Int) : Prop :=
  (d + (a.val : Int) - (b.val : Int)) % 8 = 0

instance (a b : Fin 8) (d : Int) : Decidable (inResidue a b d) :=
  inferInstanceAs (Decidable ((_ : Int) % 8 = 0))

theorem displacement_injective (p : Cell) (i j : Fin 4) (m k : Int)
    (h : displacement p i j m = displacement p i j k) : m = k := by
  simp only [displacement, image, Int.mul_zero, Int.add_zero] at h
  omega

theorem matches_iff_image (p : Cell) (i j : Fin 4) (d : Int) :
    inResidue (p i) (p j) d ↔ ∃ m, displacement p i j m = d := by
  unfold inResidue displacement image
  simp only [Int.mul_zero, Int.add_zero]
  constructor
  · intro h
    refine ⟨(d + ((p i).val : Int) - ((p j).val : Int)) / 8, ?_⟩
    omega
  · rintro ⟨m, rfl⟩
    omega

theorem matches_pos (a b : Fin 8) (n : Nat) :
    inResidue a b (n : Int) ↔ step a n = b := by
  unfold inResidue
  rw [Fin.ext_iff]
  change _ ↔ (a.val+n)%8 = b.val
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem matches_neg (a b : Fin 8) (n : Nat) :
    inResidue a b (-(n : Int)) ↔ step b n = a := by
  unfold inResidue
  rw [Fin.ext_iff]
  change _ ↔ (b.val+n)%8 = a.val
  have ha := a.isLt
  have hb := b.isLt
  omega

#print axioms matches_iff_image
#print axioms matches_neg
end AlternatingGaussian.PhysicalCell

namespace AlternatingGaussian.PhysicalCell
/-- In an admissible cell the only omitted zero-distance pair is an actual
self-interaction, with equal labels and no period translation. -/
theorem displacement_eq_zero_iff (p : Cell) (hp : ordered p) (i j : Fin 4) (m : Int) :
    displacement p i j m = 0 ↔ i = j ∧ m = 0 := by
  unfold displacement image
  simp only [Int.mul_zero, Int.add_zero]
  constructor
  · intro h
    have hi := (p i).isLt
    have hj := (p j).isLt
    have hm : m = 0 := by omega
    refine ⟨?_, hm⟩
    by_cases hl : i.val < j.val
    · have := hp i j hl
      omega
    by_cases hr : j.val < i.val
    · have := hp j i hr
      omega
    exact Fin.ext (by omega)
  · rintro ⟨rfl, rfl⟩
    omega

#print axioms displacement_eq_zero_iff
end AlternatingGaussian.PhysicalCell
