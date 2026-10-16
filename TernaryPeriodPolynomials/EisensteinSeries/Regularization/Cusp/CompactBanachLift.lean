module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.BanachLift
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ContinuousL1Sum

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem cusp_continuousL1Sum_centeredOrbit (cusp : CuspidalRepresentation)
    (family : C(X, cusp.H)) (coefficients : lp (fun _ : X => ℂ) 1)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    cuspCenteredMatrixOrbit cusp (continuousL1Sum family coefficients) direction =
      ∑' point, coefficients point • cuspCenteredMatrixOrbit cusp (family point) direction := by
  let action := (cuspUnitaryAction cusp (atInfinity (invertibleMatrix (1 + direction)))).toContinuousLinearMap
  change action (continuousL1Sum family coefficients) = _
  rw [continuousL1Sum_apply, action.map_tsum (continuousL1Sum_summable family coefficients)]
  simp only [map_smul]
  rfl

theorem cusp_continuousL1Sum_principal_fixed (cusp : CuspidalRepresentation)
    (family : C(X, cusp.H))
    (fixed : ∀ point, family point ∈ cuspHilbertFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (coefficients : lp (fun _ : X => ℂ) 1) :
    continuousL1Sum family coefficients ∈ cuspHilbertFiniteFixedSubmodule cusp binaryPrincipalLevel := by
  intro element
  let action := (cuspUnitaryAction cusp (atFinite element.val)).toContinuousLinearMap
  change action (continuousL1Sum family coefficients) = continuousL1Sum family coefficients
  rw [continuousL1Sum_apply, action.map_tsum (continuousL1Sum_summable family coefficients)]
  apply tsum_congr
  intro point
  rw [map_smul]
  change coefficients point • cusp.π (atFinite element.val) (family point) = _
  rw [fixed point element]

theorem cusp_continuousL1Sum_mem_smooth (cusp : CuspidalRepresentation)
    (family : C(X, cusp.H))
    (fixed : ∀ point, family point ∈ cuspHilbertFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (orbit : Matrix (Fin 2) (Fin 2) ℝ → C(X, cusp.H))
    (analytic : AnalyticAt ℝ orbit 0)
    (orbit_spec : ∀ᶠ direction in nhds 0, ∀ point,
      orbit direction point = cuspCenteredMatrixOrbit cusp (family point) direction)
    (coefficients : lp (fun _ : X => ℂ) 1) :
    continuousL1Sum family coefficients ∈ cusp.smooth := by
  have sum_analytic := ((continuousL1SumFunction coefficients).restrictScalars ℝ).analyticAt (orbit 0) |>.comp analytic
  have centered_analytic : AnalyticAt ℝ
      (cuspCenteredMatrixOrbit cusp (continuousL1Sum family coefficients)) 0 := by
    apply sum_analytic.congr
    filter_upwards [orbit_spec] with direction identity
    change continuousL1Sum (orbit direction) coefficients = _
    rw [cusp_continuousL1Sum_centeredOrbit, continuousL1Sum_apply]
    exact tsum_congr (fun point => by rw [identity point])
  apply (cusp.smooth_exact _).mpr
  refine ⟨cuspRealOrbit_smooth_of_centered cusp _ centered_analytic,
    binaryPrincipalLevel, binaryPrincipalLevel_isOpen, binaryPrincipalLevel_isCompact, ?_⟩
  exact cusp_continuousL1Sum_principal_fixed cusp family fixed coefficients

noncomputable def cuspCompactBanachLift (cusp : CuspidalRepresentation)
    (family : C(X, cusp.H))
    (fixed : ∀ point, family point ∈ cuspHilbertFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (orbit : Matrix (Fin 2) (Fin 2) ℝ → C(X, cusp.H))
    (analytic : AnalyticAt ℝ orbit 0)
    (orbit_spec : ∀ᶠ direction in nhds 0, ∀ point,
      orbit direction point = cuspCenteredMatrixOrbit cusp (family point) direction) :
    lp (fun _ : X => ℂ) 1 →L[ℂ] cuspFiniteFixedSubmodule cusp binaryPrincipalLevel := by
  let linear : lp (fun _ : X => ℂ) 1 →ₗ[ℂ] cuspFiniteFixedSubmodule cusp binaryPrincipalLevel :=
    { toFun := fun coefficients =>
        ⟨⟨continuousL1Sum family coefficients,
          cusp_continuousL1Sum_mem_smooth cusp family fixed orbit analytic orbit_spec coefficients⟩,
          cusp_continuousL1Sum_principal_fixed cusp family fixed coefficients⟩
      map_add' := fun _ _ => Subtype.ext (Subtype.ext (map_add (continuousL1Sum family) _ _))
      map_smul' := fun _ _ => Subtype.ext (Subtype.ext (map_smul (continuousL1Sum family) _ _)) }
  exact linear.mkContinuous ‖family‖ (continuousL1Sum_bound family)

theorem cusp_compact_family_scalar_bound
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (family : X → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (continuous : Continuous (fun point => (family point).val.val))
    (orbit : Matrix (Fin 2) (Fin 2) ℝ → C(X, cusp.H))
    (analytic : AnalyticAt ℝ orbit 0)
    (orbit_spec : ∀ᶠ direction in nhds 0, ∀ point,
      orbit direction point = cuspCenteredMatrixOrbit cusp (family point).val.val direction) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ point, ‖cuspBoundedRealization cusp (family point).val‖ ≤ constant := by
  classical
  let lift := cuspCompactBanachLift cusp ⟨fun point => (family point).val.val, continuous⟩
    (fun point => (family point).property) orbit analytic orbit_spec
  obtain ⟨constant, nonnegative, bound⟩ := cuspPrincipalRealization_complete_lift_bound cohomological lift
  refine ⟨constant, nonnegative, ?_⟩
  intro point
  have lift_single : lift (lp.single 1 point 1) = family point := by
    apply Subtype.ext
    apply Subtype.ext
    change continuousL1Sum _ (lp.single 1 point 1) = _
    rw [continuousL1Sum_single, one_smul]
    rfl
  have estimate := bound (lp.single 1 point 1)
  rw [lift_single, lp.norm_single (by norm_num : (0 : ENNReal) < 1), norm_one, mul_one] at estimate
  exact estimate

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
