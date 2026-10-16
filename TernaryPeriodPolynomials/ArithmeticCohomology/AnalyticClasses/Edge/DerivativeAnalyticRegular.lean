module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticBounds

@[expose] public section


/-!
# Regularity of the real good-line transfer of the Eichler normal form

For a scalar form `F` with `EichlerData n F` and `n ≥ 5`, the inhomogeneous real good-line transfer
`t` of the pointwise Eichler normal form is regular along the real radical at the identity: its
values are linear in the test, and `Y ↦ t(a, e^Y)` and `Y ↦ t(e^Y, b)` are differentiable at
`Y = 0`. Linearity is the exchange of the integral with the finite expansion of the test in the
dual basis; differentiability is differentiation under the integral for the smooth families
`Y ↦ (a, a e^Y)` and `Y ↦ (e^Y, e^Y b)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {F : BinaryAdelicGL → ℂ → ℂ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-! ### Smooth families of stabilizer elements -/

theorem SmoothLineFamily.const (q : LineGroup) : SmoothLineFamily (fun _ : P => q) :=
  contDiff_const

theorem SmoothLineFamily.mul {a b : P → LineGroup} (ha : SmoothLineFamily a)
    (hb : SmoothLineFamily b) : SmoothLineFamily (fun p => a p * b p) := by
  unfold SmoothLineFamily
  simp only [lineMatrix_mul_val]
  exact contDiff_matrix_mul ha hb

theorem SmoothLineFamily.comp {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {a : Q → LineGroup} (ha : SmoothLineFamily a) {φ : P → Q} (hφ : ContDiff ℝ 2 φ) :
    SmoothLineFamily (fun p => a (φ p)) :=
  ContDiff.comp (g := fun q => (lineMatrix (a q)).val) (f := φ) (show ContDiff ℝ 2
    (fun q => (lineMatrix (a q)).val) from ha) hφ

theorem smoothLineFamily_radical : SmoothLineFamily lineRadicalElement :=
  contDiff_lineMatrix_radical

theorem smoothLineFamily_diagonal :
    SmoothLineFamily (fun s : ℝ => lineLeviElement (diagonalFlow s)) :=
  contDiff_lineMatrix_diagonal

theorem smoothLineFamily_axis (i : Fin 2) :
    SmoothLineFamily (fun r : ℝ => lineRadicalElement (r • Pi.single i 1)) :=
  smoothLineFamily_radical.comp (contDiff_id.smul contDiff_const)

/-! ### Linearity in the test -/

theorem lineTransferCochain_linear (large : 5 ≤ n) (hF : EichlerData n F) (a b : LineGroup) :
    LinearTests (lineTransferCochain (eichlerNormal n F) a b) := by
  intro h functional
  set V := fun u => relativeIntegrand (eichlerNormal n F) u a (a * b) h
  have integrable (j : Fin (Module.finrank ℂ (HomogeneousPoly n))) :
      Integrable (fun u => (homogeneousBasis n).coord j (V u) * functional (homogeneousBasis n j))
        ((volume : Measure ℝ).prod volume) :=
    (integrable_functional_relativeIntegrand large hF a (a * b) h _).mul_const _
  rw [functional_lineVector, lineTransferCochain_apply]
  simp only [lineTransferCochain_apply]
  rw [show (fun u => functional (V u)) = fun u => ∑ j, (homogeneousBasis n).coord j (V u) *
    functional (homogeneousBasis n j) from funext fun u => functional_eq_basis_sum _ _,
    integral_finsetSum _ fun j _ => integrable j]
  exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _

/-! ### Differentiability along the radical -/

theorem lineTransferCochain_eq_integral (a b : LineGroup)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    lineTransferCochain (eichlerNormal n F) a b p =
      ∫ u, p.2 (relativeIntegrand (eichlerNormal n F) u a (a * b) p.1)
        ∂((volume : Measure ℝ).prod volume) :=
  lineTransferCochain_apply _ a b p.1 p.2

theorem lineTransferCochain_second (large : 5 ≤ n) (hF : EichlerData n F) (a : LineGroup)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    DifferentiableAt ℝ
      (fun Y => lineTransferCochain (eichlerNormal n F) a (lineRadicalElement Y) p) 0 := by
  simp only [lineTransferCochain_eq_integral]
  exact (hasFDerivAt_transfer_family large hF (SmoothLineFamily.const a)
    ((SmoothLineFamily.const a).mul smoothLineFamily_radical) p.1 p.2 0).differentiableAt

theorem lineTransferCochain_first (large : 5 ≤ n) (hF : EichlerData n F) (b : LineGroup)
    (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    DifferentiableAt ℝ
      (fun Y => lineTransferCochain (eichlerNormal n F) (lineRadicalElement Y) b p) 0 := by
  simp only [lineTransferCochain_eq_integral]
  exact (hasFDerivAt_transfer_family large hF smoothLineFamily_radical
    (smoothLineFamily_radical.mul (SmoothLineFamily.const b)) p.1 p.2 0).differentiableAt

/-- **The real good-line transfer of the Eichler normal form is regular along the radical.** -/
theorem edgeRegular_eichlerNormal (large : 5 ≤ n) (hF : EichlerData n F) :
    EdgeRegular (lineTransferCochain (eichlerNormal n F)) where
  linear := lineTransferCochain_linear large hF
  second := lineTransferCochain_second large hF
  first := lineTransferCochain_first large hF

end TernaryPeriodPolynomials.AnalyticClasses
