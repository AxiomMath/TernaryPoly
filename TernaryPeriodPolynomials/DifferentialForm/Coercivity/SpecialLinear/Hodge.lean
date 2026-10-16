module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Frame
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Metric

@[expose] public section


/-! Exterior-degree-two algebraic Hodge operator in the orthogonal tangent frame.
The weights are the inverse trace-metric lengths; thus all exterior slots are retained.
This file does not assert strict positivity or the global analytic comparison. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

abbrev OneCoordinates := Fin 5 → Poly
abbrev TwoCoordinates := Fin 5 → Fin 5 → Poly
abbrev ThreeCoordinates := Fin 5 → Fin 5 → Fin 5 → Poly

def IsAlternatingTwo (a : TwoCoordinates) : Prop := ∀ i j, a i j = -a j i

/-- Algebraic exterior multiplication by the coefficient action, degree one to two. -/
def exteriorOne (a : OneCoordinates) : TwoCoordinates := fun i j =>
  infinitesimal (tangentFrame i) (a j) - infinitesimal (tangentFrame j) (a i)

/-- Algebraic exterior multiplication by the coefficient action, degree two to three. -/
def exteriorTwo (a : TwoCoordinates) : ThreeCoordinates := fun i j k =>
  infinitesimal (tangentFrame i) (a j k) - infinitesimal (tangentFrame j) (a i k) +
    infinitesimal (tangentFrame k) (a i j)

/-- Metric contraction by the self-adjoint coefficient action, degree two to one. -/
def contractionTwo (a : TwoCoordinates) : OneCoordinates := fun i =>
  ∑ j : Fin 5, tangentWeight j • infinitesimal (tangentFrame j) (a j i)

/-- Metric contraction by the self-adjoint coefficient action, degree three to two. -/
def contractionThree (a : ThreeCoordinates) : TwoCoordinates := fun i j =>
  ∑ k : Fin 5, tangentWeight k • infinitesimal (tangentFrame k) (a k i j)

/-- `T T* + T* T` in exterior degree two, for the trace metric. -/
def algebraicHodgeTwo (a : TwoCoordinates) : TwoCoordinates :=
  exteriorOne (contractionTwo a) + contractionThree (exteriorTwo a)

theorem algebraicHodgeTwo_expansion (a : TwoCoordinates) (i j : Fin 5) :
    algebraicHodgeTwo a i j = ∑ k : Fin 5, tangentWeight k •
      (infinitesimal (tangentFrame k) (infinitesimal (tangentFrame k) (a i j)) +
        infinitesimal (tangentFrame i * tangentFrame k - tangentFrame k * tangentFrame i)
          (a k j) -
        infinitesimal (tangentFrame j * tangentFrame k - tangentFrame k * tangentFrame j)
          (a k i)) := by
  simp only [algebraicHodgeTwo, exteriorOne, contractionTwo, contractionThree, exteriorTwo,
    Pi.add_apply, map_sum, Derivation.map_smul, infinitesimal_commutator, Derivation.commutator_apply,
    map_add, map_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  module

theorem exteriorOne_alternating (a : OneCoordinates) : IsAlternatingTwo (exteriorOne a) := by
  intro i j
  simp [exteriorOne, neg_sub]

theorem algebraicHodgeTwo_alternating (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    IsAlternatingTwo (algebraicHodgeTwo a) := by
  intro i j
  simp only [algebraicHodgeTwo_expansion, ← Finset.sum_neg_distrib, ← smul_neg]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ha j i, map_neg, map_neg]
  congr 1
  abel

/-- The actual exterior-coordinate submodule in homogeneous degree `n`. -/
def homogeneousTwoForms (n : ℕ) : Submodule ℝ TwoCoordinates where
  carrier := {a | IsAlternatingTwo a ∧ ∀ i j, (a i j).IsHomogeneous n}
  zero_mem' := by constructor <;> intros <;> simp [IsAlternatingTwo, isHomogeneous_zero]
  add_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    constructor
    · intro i j; change a i j + b i j = -(a j i + b j i); rw [ha i j, hb i j, neg_add]
    · intro i j; exact (hda i j).add (hdb i j)
  smul_mem' := by
    rintro c a ⟨ha, hda⟩
    constructor
    · intro i j; change c • a i j = -(c • a j i); rw [ha i j, smul_neg]
    · intro i j; exact (homogeneousSubmodule (Fin 3) ℝ n).smul_mem c (hda i j)

theorem algebraicHodgeTwo_preserves_degree {n : ℕ} (a : TwoCoordinates)
    (ha : ∀ i j, (a i j).IsHomogeneous n) :
    ∀ i j, (algebraicHodgeTwo a i j).IsHomogeneous n := by
  intro i j
  rw [algebraicHodgeTwo_expansion]
  apply IsHomogeneous.sum
  intro k hk
  apply (homogeneousSubmodule (Fin 3) ℝ n).smul_mem
  exact ((infinitesimal_preserves_degree _ (infinitesimal_preserves_degree _ (ha i j))).add
    (infinitesimal_preserves_degree _ (ha k j))).sub
    (infinitesimal_preserves_degree _ (ha k i))

theorem algebraicHodgeTwo_mem {n : ℕ} (a : TwoCoordinates) (ha : a ∈ homogeneousTwoForms n) :
    algebraicHodgeTwo a ∈ homogeneousTwoForms n :=
  ⟨algebraicHodgeTwo_alternating a ha.1, algebraicHodgeTwo_preserves_degree a ha.2⟩

end TernaryPoly.SL3PolynomialCoercivity
