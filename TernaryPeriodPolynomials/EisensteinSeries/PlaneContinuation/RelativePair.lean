module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RelativeCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLieAction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RelativePair

theorem matrix_decomposition (matrix : BinaryMatrix) :
    matrix = ((matrix 0 0 + matrix 1 1) / 2) • (1 : BinaryMatrix) +
      ((matrix 1 0 - matrix 0 1) / 2) • rotationMatrix +
      ((matrix 0 0 - matrix 1 1) / 2) • diagonalMatrix +
      ((matrix 1 0 + matrix 0 1) / 2) • symmetricMatrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [rotationMatrix, diagonalMatrix, symmetricMatrix] <;> ring

theorem linearMap_ext {Target : Type*} [AddCommGroup Target] [Module ℝ Target]
    (first second : BinaryMatrix →ₗ[ℝ] Target)
    (central : first 1 = second 1) (rotation : first rotationMatrix = second rotationMatrix)
    (diagonal : first diagonalMatrix = second diagonalMatrix) (symmetric : first symmetricMatrix = second symmetricMatrix) :
    first = second := by
  apply LinearMap.ext
  intro matrix
  rw [matrix_decomposition matrix]
  simp only [map_add, map_smul, central, rotation, diagonal, symmetric]

theorem components_determine (data : CuspidalRepresentation) (degree : ℕ)
    (first second third fourth : Vectors data degree)
    (minus : first - Complex.I • second = third - Complex.I • fourth)
    (plus : first + Complex.I • second = third + Complex.I • fourth) : first = third ∧ second = fourth := by
  constructor
  · apply (smul_right_inj (M := Vectors data degree) (r := (2 : ℂ)) (by norm_num)).mp
    calc
      (2 : ℂ) • first = (first - Complex.I • second) + (first + Complex.I • second) := by module
      _ = (third - Complex.I • fourth) + (third + Complex.I • fourth) := congrArg₂ (· + ·) minus plus
      _ = (2 : ℂ) • third := by module
  · apply (smul_right_inj (M := Vectors data degree) (r := 2 * Complex.I) (by norm_num)).mp
    calc
      (2 * Complex.I) • second = (first + Complex.I • second) - (first - Complex.I • second) := by module
      _ = (third + Complex.I • fourth) - (third - Complex.I • fourth) := congrArg₂ (· - ·) plus minus
      _ = (2 * Complex.I) • fourth := by module

theorem coboundary_of_relative_pair {degree : ℕ} (data : InducingData degree)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data.cusp degree)
    (central : differential 1 = 0) (relative : differential rotationMatrix = 0)
    (vectors : Vectors data.cusp degree) (invariant : operator data.cusp degree rotationMatrix vectors = 0)
    (raising : differential diagonalMatrix - Complex.I • differential symmetricMatrix = CoefficientLadder.raising data.cusp degree vectors)
    (lowering : differential diagonalMatrix + Complex.I • differential symmetricMatrix = CoefficientLadder.lowering data.cusp degree vectors) :
    ∀ direction, differential direction = operator data.cusp degree direction vectors := by
  obtain ⟨diagonal, symmetric⟩ := components_determine data.cusp degree
    (differential diagonalMatrix) (differential symmetricMatrix)
    (operator data.cusp degree diagonalMatrix vectors) (operator data.cusp degree symmetricMatrix vectors) raising lowering
  have equality : differential = infinitesimalCoboundary data.cusp degree vectors := by
    apply linearMap_ext
    · change differential 1 = operator data.cusp degree 1 vectors
      rw [central, CoefficientCenter.operator_identity, LinearMap.zero_apply]
    · exact relative.trans invariant.symm
    · exact diagonal
    · exact symmetric
  intro direction
  exact congrArg (fun linear : BinaryMatrix →ₗ[ℝ] Vectors data.cusp degree => linear direction) equality

/-- The actual cohomological hypothesis yields a non-exact pair in the relative two-term complex. -/
theorem exists_nontrivial_relative_pair {degree : ℕ} (data : InducingData degree) :
    ∃ first second : Vectors data.cusp degree,
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ index,
          (first index).val ∈ fixedSubspace data.cusp level ∧ (second index).val ∈ fixedSubspace data.cusp level) ∧
      CoefficientRotation.shifted data.cusp degree 2 first = 0 ∧
      CoefficientRotation.shifted data.cusp degree (-2) second = 0 ∧
      CoefficientLadder.lowering data.cusp degree first = CoefficientLadder.raising data.cusp degree second ∧
      ¬ ∃ vectors : Vectors data.cusp degree, operator data.cusp degree rotationMatrix vectors = 0 ∧
        first = CoefficientLadder.raising data.cusp degree vectors ∧ second = CoefficientLadder.lowering data.cusp degree vectors := by
  obtain ⟨differential, ⟨level, openness, compactness, fixed⟩, equation, central, relative, nontrivialClass⟩ :=
    RelativeCocycle.exists_relative_cocycle data
  refine ⟨differential diagonalMatrix - Complex.I • differential symmetricMatrix,
    differential diagonalMatrix + Complex.I • differential symmetricMatrix,
    ⟨level, openness, compactness, ?_⟩,
    RelativeCocycle.raising_value_eigen data.cusp degree differential equation relative,
    RelativeCocycle.lowering_value_eigen data.cusp degree differential equation relative,
    RelativeCocycle.ladder_relation data.cusp degree differential equation relative, ?_⟩
  · intro index
    exact ⟨(fixedSubspace data.cusp level).sub_mem (fixed diagonalMatrix index)
        ((fixedSubspace data.cusp level).smul_mem Complex.I (fixed symmetricMatrix index)),
      (fixedSubspace data.cusp level).add_mem (fixed diagonalMatrix index)
        ((fixedSubspace data.cusp level).smul_mem Complex.I (fixed symmetricMatrix index))⟩
  · rintro ⟨vectors, invariant, raising, lowering⟩
    exact nontrivialClass ⟨vectors, coboundary_of_relative_pair data differential central relative vectors invariant raising lowering⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RelativePair
