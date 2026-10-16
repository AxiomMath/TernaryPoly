module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GramCutoff

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryProductHaar TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ConstantRealMass

def orbitalMass (cutoff : Rectangular ℝ → ℝ) (value : Rectangular ℝ) : ℂ :=
  ∫ binary : BinaryRealGL, (cutoff (value * binary.val) : ℂ) ∂realMeasure

def baseMass (cutoff : Rectangular ℝ → ℝ) : ℂ := orbitalMass cutoff (columns (1 : Matrix (Fin 3) (Fin 3) ℝ))

theorem orbitalMass_right (cutoff : Rectangular ℝ → ℝ) (value : Rectangular ℝ) (matrix : BinaryRealGL) :
    orbitalMass cutoff (value * matrix.val) = orbitalMass cutoff value := by
  have equality := integral_mul_left_eq_self (μ := realMeasure)
    (fun binary : BinaryRealGL => (cutoff (value * binary.val) : ℂ)) matrix
  simpa only [orbitalMass, Units.val_mul, Matrix.mul_assoc] using equality

theorem orbitalMass_orthogonal (cutoff : Rectangular ℝ → ℝ)
    (invariant : ∀ orthogonal : RealGL3, orthogonal.val.transpose * orthogonal.val = 1 →
      ∀ value : Rectangular ℝ, cutoff (orthogonal.val * value) = cutoff value)
    (orthogonal : RealGL3) (orthogonality : orthogonal.val.transpose * orthogonal.val = 1)
    (value : Rectangular ℝ) : orbitalMass cutoff (orthogonal.val * value) = orbitalMass cutoff value := by
  unfold orbitalMass
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun binary => by
    dsimp only
    rw [Matrix.mul_assoc, invariant orthogonal orthogonality])

theorem inverse_orthogonal (orthogonal : RealGL3)
    (orthogonality : orthogonal.val.transpose * orthogonal.val = 1) :
    orthogonal⁻¹.val.transpose * orthogonal⁻¹.val = 1 := by
  have inverse : orthogonal.val * orthogonal⁻¹.val = 1 := orthogonal.val_inv
  have transpose : orthogonal.val.transpose = orthogonal⁻¹.val := by
    calc
      orthogonal.val.transpose = orthogonal.val.transpose * (orthogonal.val * orthogonal⁻¹.val) := by rw [inverse, Matrix.mul_one]
      _ = orthogonal⁻¹.val := by rw [← Matrix.mul_assoc, orthogonality, Matrix.one_mul]
  rw [← transpose, Matrix.transpose_transpose, transpose, inverse]

theorem mass_eq_base (cutoff : Rectangular ℝ → ℝ)
    (invariant : ∀ orthogonal : RealGL3, orthogonal.val.transpose * orthogonal.val = 1 →
      ∀ value : Rectangular ℝ, cutoff (orthogonal.val * value) = cutoff value)
    (point : AdelicGL) : RealOrbitalMass.mass cutoff point = baseMass cutoff := by
  obtain ⟨parabolic, orthogonal, factorization, orthogonality, _⟩ :=
    RealDecomposition.exists_plane_orthogonal (realGroup point)
  have frame : realFrame point = columns orthogonal⁻¹.val * (planeBinaryBlock parabolic⁻¹).val := by
    unfold realFrame
    rw [factorization, _root_.mul_inv_rev]
    exact FrameFlags.columns_mul_parabolic orthogonal⁻¹ parabolic⁻¹
  change orbitalMass cutoff (realFrame point) = baseMass cutoff
  rw [frame, orbitalMass_right, ← mul_standard orthogonal⁻¹.val]
  exact orbitalMass_orthogonal cutoff invariant orthogonal⁻¹ (inverse_orthogonal orthogonal orthogonality) _

theorem exists_cutoff :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value} ∧
      baseMass cutoff ≠ 0 ∧ ∀ point : AdelicGL, RealOrbitalMass.mass cutoff point = baseMass cutoff := by
  obtain ⟨cutoff, smooth, compact, supported, range, value, invariant⟩ := GramCutoff.exists_cutoff
  refine ⟨cutoff, smooth, compact, supported, ?_, mass_eq_base cutoff invariant⟩
  have nonzero := RealOrbitalMass.nonzero cutoff smooth.continuous compact supported
    (fun value => (range ⟨value, rfl⟩).1) 1 (by
      simpa only [realFrame, map_one, inv_one, Units.val_one, value] using (one_ne_zero : (1 : ℝ) ≠ 0))
  rw [mass_eq_base cutoff invariant] at nonzero
  exact nonzero

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ConstantRealMass
