module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Coercive
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

@[expose] public section

/-! The actual tensor connection on polynomial-coefficient alternating forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

theorem formHessian_add_right (x u v w : Coordinates) :
    formHessian x u (v + w) = formHessian x u v + formHessian x u w :=
  (fderiv ℝ (fderiv ℝ coordinateForm) x u).map_add v w

theorem formHessian_smul_right (x u v : Coordinates) (c : ℝ) :
    formHessian x u (c • v) = c • formHessian x u v :=
  (fderiv ℝ (fderiv ℝ coordinateForm) x u).map_smul c v

theorem tangentCorrection_add_right (x u v w : Coordinates) :
    tangentCorrection x u (v + w) = tangentCorrection x u v + tangentCorrection x u w := by
  simp only [tangentCorrection, formHessian_add_right, formDerivative_add, add_mul, mul_add, smul_add]
  module

theorem tangentCorrection_smul_right (x u v : Coordinates) (c : ℝ) :
    tangentCorrection x u (c • v) = c • tangentCorrection x u v := by
  simp only [tangentCorrection, formHessian_smul_right, formDerivative_smul, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, smul_sub, smul_smul]
  module

/-- The actual tangent-connection endomorphism in a fixed direction. -/
def tangentEndomorphism (x u : Coordinates) : Coordinates →L[ℝ] Coordinates :=
  (show Coordinates →ₗ[ℝ] Coordinates from
    { toFun := tangentConnection x u
      map_add' v w := by
        rw [tangentConnection, tangentCorrection_add_right, map_add, extract_add]
        rfl
      map_smul' c v := by
        rw [tangentConnection, tangentCorrection_smul_right, map_smul, extract_smul]
        rfl }).toContinuousLinearMap

@[simp] theorem tangentEndomorphism_apply (x u v : Coordinates) :
    tangentEndomorphism x u v = tangentConnection x u v := rfl

/-- Infinitesimal pullback on tangent slots, using Mathlib's genuine derivative of composition. -/
def tangentFormAction (n k : ℕ) (x u : Coordinates) (a : FormValue n k) : FormValue n k :=
  a.fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ Coordinates) (tangentEndomorphism x u)

theorem tangentFormAction_apply (n k : ℕ) (x u : Coordinates) (a : FormValue n k)
    (v : Fin k → Coordinates) :
    tangentFormAction n k x u a v = ∑ i : Fin k, a (Function.update v i (tangentConnection x u (v i))) := by
  rw [tangentFormAction, fderivCompContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, tangentEndomorphism_apply]
  · simp only [Function.update_of_ne h, ContinuousLinearMap.id_apply]

/-- Full tensor covariant derivative: actual coefficient connection minus the tangent-slot action. -/
def covariantFormDerivative (n k : ℕ) (w : Coordinates → FormValue n k) (x u : Coordinates) : FormValue n k :=
  fderiv ℝ w x u + coefficientFormMap (connectionMatrix n x u) k (w x) - tangentFormAction n k x u (w x)

theorem covariantFormDerivative_apply (n k : ℕ) (w : Coordinates → FormValue n k)
    (x u : Coordinates) (v : Fin k → Coordinates) :
    covariantFormDerivative n k w x u v = fderiv ℝ w x u v + connectionMatrix n x u (w x v) -
      ∑ i : Fin k, w x (Function.update v i (tangentConnection x u (v i))) := by
  simp only [covariantFormDerivative, ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
    tangentFormAction_apply]
  rfl

end TernaryPoly.PolynomialFormConnection
