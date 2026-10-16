module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsComplexNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory Limits
variable (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (V : ModuleCat.{0} ℚ)

/-- Actual scalar homology vanishing implies actual V-valued Hom cohomology vanishing. -/
theorem homCochains_homology_isZero (a : ℕ) (h : IsZero (K.homology a)) :
    IsZero ((homCochains K V).homology a) := by
  let := ModuleCat.subsingleton_of_isZero h
  let : Subsingleton ((homCochains K V).homology a) :=
    (homologyEvaluationEquiv K V a).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- If a fixed actual scalar homology coordinate sends a fixed generator to one,
then literal evaluation on that generator is an isomorphism for arbitrary V. -/
def generatorEvaluationEquiv (a : ℕ) (e : K.homology a ≃ₗ[ℚ] ℚ) :
    (homCochains K V).homology a ≃ₗ[ℚ] V :=
  homologyEvaluationEquiv K V a ≪≫ₗ
    LinearEquiv.arrowCongr e (LinearEquiv.refl ℚ V) ≪≫ₗ
      LinearMap.ringLmapEquivSelf ℚ ℚ V

/-- The one-dimensional coordinate is the actual evaluation on its inverse image of one. -/
theorem generatorEvaluationEquiv_apply (a : ℕ) (e : K.homology a ≃ₗ[ℚ] ℚ)
    (h : (homCochains K V).homology a) :
    generatorEvaluationEquiv K V a e h = homologyEvaluationEquiv K V a h (e.symm 1) := rfl

end TernaryPoly.RationalHomologyCoefficients
