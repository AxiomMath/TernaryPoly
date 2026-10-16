module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.ModelComparisonNeg
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageFace
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.Modularity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.RealizeFields

@[expose] public section


/-!
# CMP-8 (3a, 3b): the scalar functions of the entry at an integral base are the classical form

For an Eichler input `I` and the classical level-one form `f` of its vector (`hform`): at an integral base `atFinite B` of `GL₂(Ẑ)` the scalar functions
`F(1 · b)` and `F(J · b)` of `g5_levelOne_cusp` are both `f` on the upper half plane (`scalarF_one_eq_form`, `scalarF_J_eq_form`).  The first is the right invariance
of the spherical vector (`scalarF_integral`); the second uses H4's negative-determinant comparison (`vhModel_realize_eq_integral` with `γ = ε`) and `ε J = -1`,
the weight `-2 * halfWeight` being even (`realize_J`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The scalar function at a point of the upper half plane, through the symmetric section. -/
theorem scalarF_apply (hw : ℤ) (v : σ.smooth) (base : BinaryAdelicGL) (point : UpperHalfPlane) :
    cuspScalarWeightedRealization σ hw v base (point : ℂ) =
      point.im ^ hw • σ.realize v (base * atInfinity (binarySymmetricSection point)) := by
  rw [cuspScalarWeightedRealization, cuspScalarAffineRealization, binaryUpperSectionMatrix_coe,
    invertibleMatrix_coe]
  rfl

/-- **Right translation of the base by an integral matrix does not change the scalar function** (spherical vector). -/
theorem scalarF_integral (I : EichlerInput σ n) (B : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (x : BinaryAdelicGL) (z : ℂ) :
    cuspScalarWeightedRealization σ I.halfWeight I.vector
        (x * atFinite (GeneralLinearGroup.map integralEmbedding B)) z =
      cuspScalarWeightedRealization σ I.halfWeight I.vector x z := by
  unfold cuspScalarWeightedRealization cuspScalarAffineRealization
  rw [mul_assoc, TernaryPeriodPolynomials.HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity,
    ← mul_assoc, realize_mul_integral I]

theorem reflectionGL_mul_J_mul (A : BinaryRealGL) :
    reflectionGL ℝ * (UpperHalfPlane.J * A) = A * scalGL (-1) (by norm_num) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionGL, scalGL, UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- **The reflected base gives the same realization at a symmetric section**: `realize (J · A) = realize (A)`
(the model value at the negative component is `F_h(ε J A) = F_h(A)` since `εJ = -1` and the weight is even). -/
theorem realize_J (I : EichlerInput σ n)
    (f : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑f : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (point : UpperHalfPlane) :
    σ.realize I.vector (atInfinity UpperHalfPlane.J * atInfinity (binarySymmetricSection point)) =
      σ.realize I.vector (atInfinity (binarySymmetricSection point)) := by
  set A := binarySymmetricSection point with hA
  have hdetA : (GeneralLinearGroup.det A).val = 1 := by
    simp [hA, binarySymmetricSection]
  have hdetJ : (GeneralLinearGroup.det (UpperHalfPlane.J * A)).val < 0 := by
    rw [map_mul, Units.val_mul, hdetA]
    simp [UpperHalfPlane.J, GeneralLinearGroup.val_det_apply]
  have hdetε : 0 < (GeneralLinearGroup.det (binaryRationalReal reflectionQ * (UpperHalfPlane.J * A))).val := by
    rw [map_mul, Units.val_mul, det_reflectionQ_real]
    nlinarith
  have hint : binaryRationalFinite reflectionQ * (1 : BinaryFiniteGL) ∈ binaryIntegralFinite := by
    rw [mul_one]; exact reflectionQ_finite_mem
  have h1 := vhModel_realize_eq_integral I f hform (UpperHalfPlane.J * A) 1 reflectionQ hint hdetε
  have h2 := realize_atInfinity_eq_Fh I f hform A (by rw [hdetA]; exact one_pos)
  have hs : ∀ g : BinaryRealGL, smoothReal σ (σ.π (atFinite (1 : BinaryFiniteGL)) I.vector.val) (atInfinity g) =
      σ.realize I.vector (atInfinity g) := fun g => by
    rw [TernaryPeriodPolynomials.Argument.FormSeedBridge.atFinite_one_bin, map_one]
    simp only [Module.End.one_apply]
    exact congrFun (smoothReal_eq_realize σ _ I.vector.2) _
  rw [← TernaryPeriodPolynomials.Regularity.atInfinity_mul_binary, ← hs, h1, binaryRationalReal_reflectionQ, reflectionGL_mul_J_mul,
    Fh_scalGL (-2 * I.halfWeight) (-I.halfWeight) (by ring), h2]

/-- The scalar function at the integral base is the classical form. -/
theorem scalarF_one_eq_form (I : EichlerInput σ n)
    (f : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑f : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (B : GeneralLinearGroup (Fin 2) IntegralAdeles) (point : UpperHalfPlane) :
    cuspScalarWeightedRealization σ I.halfWeight I.vector
        (1 * atFinite (GeneralLinearGroup.map integralEmbedding B)) (point : ℂ) = f point := by
  rw [scalarF_integral]
  exact (congrFun hform point).symm

/-- **The reflected scalar function at the integral base is the same classical form.** -/
theorem scalarF_J_eq_form (I : EichlerInput σ n)
    (f : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne (-2 * I.halfWeight))
    (hform : (⇑f : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (B : GeneralLinearGroup (Fin 2) IntegralAdeles) (point : UpperHalfPlane) :
    cuspScalarWeightedRealization σ I.halfWeight I.vector
        (atInfinity UpperHalfPlane.J * atFinite (GeneralLinearGroup.map integralEmbedding B)) (point : ℂ) = f point := by
  rw [scalarF_integral, scalarF_apply, realize_J I f hform point]
  have h1 := scalarF_apply I.halfWeight I.vector 1 point
  rw [one_mul] at h1
  rw [← h1]
  exact (congrFun hform point).symm

end TernaryPeriodPolynomials.Argument.KDaggerComparison
