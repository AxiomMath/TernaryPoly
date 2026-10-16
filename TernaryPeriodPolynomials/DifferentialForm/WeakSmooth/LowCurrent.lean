module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Form.Differential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.LowSymbol

@[expose] public section


/-! Actual low-degree form-current values, with no basis-dependent identification. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts
open SmoothLocalDeRham
open scoped Distributions

/-- Encode an actual coefficient-valued scalar current as a zero-form current. -/
def zeroFormWeak (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (T : ValuedWeak (V := Coefficients n) Ω) : FormWeak n 0 Ω :=
  zeroEquiv.toLinearMap.comp T

@[simp] theorem zeroFormWeak_apply (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (T : ValuedWeak (V := Coefficients n) Ω) (φ : 𝓓(Ω, ℝ)) :
    zeroFormWeak n Ω T φ = zeroEquiv (T φ) := rfl

/-- Read the actual coefficient value of a zero-form current. -/
def formWeakZeroValue (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n 0 Ω) : ValuedWeak (V := Coefficients n) Ω :=
  zeroEquiv.symm.toLinearMap.comp W

/-- Encoding the actual coefficient value of a zero-form current recovers that current. -/
theorem zeroFormWeak_zeroValue (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n 0 Ω) : zeroFormWeak n Ω (formWeakZeroValue n Ω W) = W := by
  apply LinearMap.ext
  intro φ
  exact zeroEquiv.apply_symm_apply (W φ)

/-- Evaluate a genuine one-form on an actual tangent vector. -/
def oneFormEvaluation (n : ℕ) (v : Coordinates) : FormValue n 1 →ₗ[ℝ] Coefficients n :=
  (ContinuousLinearMap.apply ℝ (Coefficients n) v).toLinearMap.comp oneEquiv.symm.toLinearMap

/-- Read an actual one-form current as a coefficient-valued weak directional one-form. -/
def formWeakOneValue (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates) (W : FormWeak n 1 Ω) :
    Coordinates →ₗ[ℝ] ValuedWeak (V := Coefficients n) Ω where
  toFun v := (oneFormEvaluation n v).comp W
  map_add' u v := by
    apply LinearMap.ext
    intro φ
    exact map_add (oneEquiv.symm (W φ)) u v
  map_smul' c v := by
    apply LinearMap.ext
    intro φ
    exact map_smul (oneEquiv.symm (W φ)) c v

@[simp] theorem formWeakOneValue_apply (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (W : FormWeak n 1 Ω) (v : Coordinates) (φ : 𝓓(Ω, ℝ)) :
    formWeakOneValue n Ω W v φ = oneEquiv.symm (W φ) v := rfl

/-- Actual tangent evaluations determine an actual one-form-valued compact-test current. -/
theorem formWeakOneValue_injective (n : ℕ) (Ω : TopologicalSpace.Opens Coordinates) :
    Function.Injective (formWeakOneValue n Ω) := by
  intro W Z h
  apply LinearMap.ext
  intro φ
  apply oneEquiv.symm.injective
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun w : Coordinates →ₗ[ℝ] ValuedWeak (V := Coefficients n) Ω => w v φ) h

end TernaryPoly.PolynomialFormWeakSmooth
