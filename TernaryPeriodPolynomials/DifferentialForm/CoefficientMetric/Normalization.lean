module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Fischer
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsBasic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.GDelta.MetrizableSpace

@[expose] public section

/-! Determinant normalization removes the radial factor in the actual trace-one action. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpacePositive SymmetricSpaceArithmeticProper SymmetricSpaceCovering
open scoped ContDiff Matrix.Norms.Elementwise

def determinantNormalize (S : Mat) : Mat := S.det ^ (-(1/3 : ℝ)) • S

theorem determinantNormalize_positive (S : Mat) (hS : S.PosDef) : (determinantNormalize S).PosDef :=
  hS.smul (Real.rpow_pos_of_pos hS.det_pos _)

theorem determinantNormalize_smul (r : ℝ) (hr : 0 < r) (S : Mat) (hS : S.PosDef) :
    determinantNormalize (r • S) = determinantNormalize S := by
  unfold determinantNormalize
  rw [Matrix.det_smul, Fintype.card_fin, Real.mul_rpow (pow_nonneg hr.le 3) hS.det_pos.le,
    ← Real.rpow_natCast_mul hr.le 3 (-(1/3 : ℝ))]
  norm_num only [Nat.cast_ofNat, show (3 : ℝ)*(-(1/3 : ℝ)) = -1 by norm_num,
    Real.rpow_neg_one]
  rw [smul_smul]
  congr 1
  field_simp [hr.ne']

theorem determinantNormalize_det (S : Mat) (hS : S.PosDef) : (determinantNormalize S).det = 1 := by
  rw [determinantNormalize, Matrix.det_smul, Fintype.card_fin,
    ← Real.rpow_mul_natCast hS.det_pos.le (-(1/3 : ℝ)) 3]
  norm_num only [Nat.cast_ofNat, show (-(1/3 : ℝ))*3 = -1 by norm_num, Real.rpow_neg_one]
  exact inv_mul_cancel₀ hS.det_pos.ne'

theorem determinantNormalize_integral_conjugate (g : IntegralGL) (S : Mat) :
    determinantNormalize (conjugate (realIntegral g) S) =
      conjugate (realIntegral g) (determinantNormalize S) := by
  rw [determinantNormalize, integral_conjugate_det, determinantNormalize, conjugate_smul]

def normalizedForm (S : Space) : Mat := determinantNormalize S.val

theorem normalizedForm_deck (g : DeckGroup) (S : Space) :
    normalizedForm (g • S) = conjugate (deckMatrix g) (normalizedForm S) := by
  change determinantNormalize ((conjugate (deckMatrix g) S.val).trace⁻¹ •
    conjugate (deckMatrix g) S.val) = _
  rw [determinantNormalize_smul _ (inv_pos.mpr (conjugate_positive (deckMatrix g) S.val S.property.1).trace_pos)
    _ (conjugate_positive (deckMatrix g) S.val S.property.1)]
  exact determinantNormalize_integral_conjugate (deckInclusion g) S.val

def basepoint : Space := ⟨normalize 1, normalize_mem 1 Matrix.PosDef.one⟩

theorem normalizedForm_basepoint : normalizedForm basepoint = 1 := by
  change determinantNormalize ((1 : Mat).trace⁻¹ • (1 : Mat)) = 1
  rw [determinantNormalize_smul _ (inv_pos.mpr Matrix.PosDef.one.trace_pos) _ Matrix.PosDef.one]
  simp [determinantNormalize]

end TernaryPoly.PolynomialCoefficientMetric
