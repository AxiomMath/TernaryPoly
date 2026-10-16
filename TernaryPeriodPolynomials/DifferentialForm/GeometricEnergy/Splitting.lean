module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.IntegratedAlgebra
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Adjoint

@[expose] public section


/-! Exact compact differential splitting, with the remaining mixed energy recorded explicitly. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormCoordinates PolynomialFormHilbert
open SmoothCoveringDeRham Set
open scoped SymmetricSpaceRiemannian

/-- The actual compact covariant exterior derivative in the flat trivialization. -/
def compactCovariantExterior (n k : ℕ) : Core n k →ₗ[ℝ] Core n (k + 1) :=
  compactDifferential (deckRepresentation n) isOpen_univ k - compactSymmetricExterior n k

/-- The actual compact formal adjoint of the covariant exterior derivative. -/
def compactCovariantAdjoint (n k : ℕ) : Core n (k + 1) →ₗ[ℝ] Core n k :=
  compactAdjoint n k - compactSymmetricContraction n k

theorem inclusion_covariantExterior (n k : ℕ) (a : Core n k) :
    inclusion n (k + 1) (compactCovariantExterior n k a) =
      inclusion n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k a) -
        inclusion n (k + 1) (compactSymmetricExterior n k a) :=
  (inclusion n (k + 1)).map_sub _ _

theorem inclusion_covariantAdjoint (n k : ℕ) (a : Core n (k + 1)) :
    inclusion n k (compactCovariantAdjoint n k a) = inclusion n k (compactAdjoint n k a) -
      inclusion n k (compactSymmetricContraction n k a) :=
  (inclusion n k).map_sub _ _

theorem inner_covariantExterior_one (n : ℕ) (a : Core n 1) (b : Core n 2) :
    inner ℝ (inclusion n 2 (compactCovariantExterior n 1 a)) (inclusion n 2 b) =
      inner ℝ (inclusion n 1 a) (inclusion n 1 (compactCovariantAdjoint n 1 b)) := by
  calc
    _ = inner ℝ (inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)) (inclusion n 2 b) -
        inner ℝ (inclusion n 2 (compactSymmetricExterior n 1 a)) (inclusion n 2 b) :=
      (congrArg (fun w => inner ℝ w (inclusion n 2 b)) (inclusion_covariantExterior n 1 a)).trans
        (inner_sub_left _ _ _)
    _ = inner ℝ (inclusion n 1 a) (inclusion n 1 (compactAdjoint n 1 b)) -
        inner ℝ (inclusion n 1 a) (inclusion n 1 (compactSymmetricContraction n 1 b)) :=
      congrArg₂ (· - ·) (inner_compactDifferential_compactAdjoint n 1 a b) (inner_symmetricExterior_one n a b)
    _ = _ := (inner_sub_right _ _ _).symm.trans
      (congrArg (inner ℝ (inclusion n 1 a)) (inclusion_covariantAdjoint n 1 b).symm)

theorem inner_covariantExterior_two (n : ℕ) (a : Core n 2) (b : Core n 3) :
    inner ℝ (inclusion n 3 (compactCovariantExterior n 2 a)) (inclusion n 3 b) =
      inner ℝ (inclusion n 2 a) (inclusion n 2 (compactCovariantAdjoint n 2 b)) := by
  calc
    _ = inner ℝ (inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)) (inclusion n 3 b) -
        inner ℝ (inclusion n 3 (compactSymmetricExterior n 2 a)) (inclusion n 3 b) :=
      (congrArg (fun w => inner ℝ w (inclusion n 3 b)) (inclusion_covariantExterior n 2 a)).trans
        (inner_sub_left _ _ _)
    _ = inner ℝ (inclusion n 2 a) (inclusion n 2 (compactAdjoint n 2 b)) -
        inner ℝ (inclusion n 2 a) (inclusion n 2 (compactSymmetricContraction n 2 b)) :=
      congrArg₂ (· - ·) (inner_compactDifferential_compactAdjoint n 2 a b) (inner_symmetricExterior_two n a b)
    _ = _ := (inner_sub_right _ _ _).symm.trans
      (congrArg (inner ℝ (inclusion n 2 a)) (inclusion_covariantAdjoint n 2 b).symm)

/-- The exact two mixed pairings; no vanishing is assumed in the energy expansion. -/
def mixedEnergy (n : ℕ) (a : Core n 2) : ℝ :=
  inner ℝ (inclusion n 3 (compactCovariantExterior n 2 a)) (inclusion n 3 (compactSymmetricExterior n 2 a)) +
  inner ℝ (inclusion n 1 (compactCovariantAdjoint n 1 a)) (inclusion n 1 (compactSymmetricContraction n 1 a))

theorem inclusion_flat_sum (n k : ℕ) (a : Core n k) :
    inclusion n (k + 1) (compactDifferential (deckRepresentation n) isOpen_univ k a) =
      inclusion n (k + 1) (compactCovariantExterior n k a) + inclusion n (k + 1) (compactSymmetricExterior n k a) :=
  ((congrArg (· + inclusion n (k + 1) (compactSymmetricExterior n k a))
    (inclusion_covariantExterior n k a)).trans (sub_add_cancel _ _)).symm

theorem inclusion_adjoint_sum (n k : ℕ) (a : Core n (k + 1)) :
    inclusion n k (compactAdjoint n k a) =
      inclusion n k (compactCovariantAdjoint n k a) + inclusion n k (compactSymmetricContraction n k a) :=
  ((congrArg (· + inclusion n k (compactSymmetricContraction n k a))
    (inclusion_covariantAdjoint n k a)).trans (sub_add_cancel _ _)).symm

theorem norm_pair_add_expansion {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a b : E) (c d : F) :
    ‖a + b‖ ^ 2 + ‖c + d‖ ^ 2 = (‖a‖ ^ 2 + ‖c‖ ^ 2) + (‖b‖ ^ 2 + ‖d‖ ^ 2) +
      2 * (inner ℝ a b + inner ℝ c d) := by
  rw [norm_add_sq_real, norm_add_sq_real]
  ring

theorem compact_energy_expansion (n : ℕ) (a : Core n 2) :
    ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 =
    (‖inclusion n 3 (compactCovariantExterior n 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactCovariantAdjoint n 1 a)‖ ^ 2) +
    (‖inclusion n 3 (compactSymmetricExterior n 2 a)‖ ^ 2 +
      ‖inclusion n 1 (compactSymmetricContraction n 1 a)‖ ^ 2) + 2 * mixedEnergy n a :=
  (congrArg₂ (fun u v => ‖u‖ ^ 2 + ‖v‖ ^ 2) (inclusion_flat_sum n 2 a) (inclusion_adjoint_sum n 1 a)).trans
    (norm_pair_add_expansion _ _ _ _)

end TernaryPoly.PolynomialFormGeometricEnergy
