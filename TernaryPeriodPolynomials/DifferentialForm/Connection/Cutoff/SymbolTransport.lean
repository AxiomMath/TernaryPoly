module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.SymbolBase

@[expose] public section

/-! The fixed scalar-symbol bound transports through the actual determinant-normalized real action. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Matrix SmoothDeRhamGluing SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  PolynomialFormGeometricEnergy SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
  SymmetricSpaceTraceMetric SymmetricSpaceRiemannian ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem scalarWedge_apply (n k : ℕ) (α : Coordinates →L[ℝ] ℝ) (a : FormValue n k)
    (v : Fin (k + 1) → Coordinates) :
    scalarWedge α a v = ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) • (α (v i) • a (Fin.removeNth i v)) :=
  alternatizeUncurryFin_apply (α.smulRight a) v

/-- Naturality uses the literal scalar exterior symbol and the actual tangent derivative. -/
theorem scalarWedge_real (n k : ℕ) (g : RealGL) (x : Coordinates)
    (α : Coordinates →L[ℝ] ℝ) (a b : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k b) :
    (scalarWedge α a).compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) (k + 1)
        (scalarWedge (α.comp (fderiv ℝ (coordinateAction g) x)) b) := by
  have hval (z : Fin k → Coordinates) :
      a (fun r => fderiv ℝ (coordinateAction g) x (z r)) = realCoefficientMap n g (b z) :=
    congrArg (fun F : FormValue n k => F z) ha
  apply ContinuousAlternatingMap.ext
  intro v
  change scalarWedge α a (fun r => fderiv ℝ (coordinateAction g) x (v r)) =
    realCoefficientMap n g (scalarWedge (α.comp (fderiv ℝ (coordinateAction g) x)) b v)
  rw [scalarWedge_apply, scalarWedge_apply, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.map_zsmul, _root_.map_smul]
  congr 1
  change α (fderiv ℝ (coordinateAction g) x (v i)) •
    a (fun r => fderiv ℝ (coordinateAction g) x (Fin.removeNth i v r)) = _
  rw [hval]
  rfl

/-- One point-independent constant controls the scalar exterior symbol in the original metrics. -/
theorem exists_scalarWedge_metric_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ (x : Coordinates), x ∈ positiveCoordinates →
      ∀ (α : Coordinates →L[ℝ] ℝ),
      (∀ v, |α v| ≤ B * Real.sqrt (coordinatePair x v v)) → ∀ a : FormValue n k,
        formPairing n (k + 1) x (scalarWedge α a) (scalarWedge α a) ≤
          C * B ^ 2 * formPairing n k x a a := by
  obtain ⟨C, hC, h⟩ := exists_base_scalarWedge_bound n k
  refine ⟨C, hC, fun B hB x hx α hα a => ?_⟩
  obtain ⟨g, hg, he⟩ := exists_normalized_real_frame x hx
  rw [← he] at hα ⊢
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let b := realFormPullback n k g y a
  let β := α.comp (fderiv ℝ (coordinateAction g) y)
  have hb := realFormPullback_spec n k g y a
  have hw := scalarWedge_real n k g y α a b hb
  have hβ (v : Coordinates) : |β v| ≤ B * Real.sqrt (coordinatePair y v v) := by
    have hv := hα (fderiv ℝ (coordinateAction g) y v)
    rw [coordinatePair_fderiv_invariant g y hy] at hv
    exact hv
  rw [formPairing_real n (k + 1) g hg y hy _ _ _ _ hw hw,
    formPairing_real n k g hg y hy a a b b hb hb]
  exact h B hB β hβ b

end TernaryPoly.PolynomialFormConnection
