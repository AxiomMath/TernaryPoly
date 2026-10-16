module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.CuspidalBoundary

@[expose] public section


/-! The literal local standard-intertwiner entry at three. No local coefficient
or nonvanishing assertion is assumed in the definition of the integral. -/

noncomputable section
namespace GeneralEisenstein
open Matrix MeasureTheory Adelic

abbrev LocalThreeGL := GeneralLinearGroup (Fin 3) ℚ_[3]
abbrev LocalThreeIntegralGL := GeneralLinearGroup (Fin 3) ℤ_[3]

instance localThreeMeasurableSpace : MeasurableSpace ℚ_[3] := borel ℚ_[3]
instance localThreeBorelSpace : BorelSpace ℚ_[3] := ⟨rfl⟩

/-- The actual last-row congruence subgroup, embedded in GL₃(Q₃). -/
def InLocalThreeLevel (g : LocalThreeGL) : Prop :=
  ∃ k : LocalThreeIntegralGL,
    lastRow ᵥ* (GeneralLinearGroup.map PadicInt.toZMod k).val = lastRow ∧
    GeneralLinearGroup.map PadicInt.Coe.ringHom k = g

def localGoodLine : LocalThreeGL :=
  ⟨!![0,0,1;0,1,0;1,0,0], !![0,0,1;0,1,0;1,0,0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- Support on the actual P(Q₃)K₁ double coset. -/
def LocalBadPlaneSupport (φ : LocalThreeGL → ℂ) : Prop :=
  ∀ g, (¬ ∃ p : planeParabolic ℚ_[3], ∃ k : LocalThreeGL,
    InLocalThreeLevel k ∧ g = p.val*k) → φ g = 0

def LocalRightInvariant (φ : LocalThreeGL → ℂ) : Prop :=
  ∀ g k, InLocalThreeLevel k → φ (g*k) = φ g

def localBadPlaneIntegrand (φ : LocalThreeGL → ℂ) (u : ℚ_[3] × ℚ_[3]) : ℂ :=
  φ (weyl⁻¹ * lineUnipotent u.1 u.2 * localGoodLine)

/-- The precise 1/9 entry, for additive Haar measure giving Z₃ volume one.
Both integrability and the equality are conclusions, for arbitrary scalar
sections satisfying only the displayed support and invariance conditions. -/
def LocalBadPlaneEntry : Prop :=
  ∀ μ : Measure ℚ_[3], μ.IsAddHaarMeasure → μ {x | ‖x‖ ≤ 1} = 1 →
    ∀ φ, LocalBadPlaneSupport φ → LocalRightInvariant φ →
      Integrable (localBadPlaneIntegrand φ) (μ.prod μ) ∧
      (∫ u, localBadPlaneIntegrand φ u ∂(μ.prod μ)) = (1/9 : ℂ) * φ 1

end GeneralEisenstein
end
