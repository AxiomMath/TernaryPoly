module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory HomologicalComplex
open SingularLocalCap SingularLocalCap.Homology
variable (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (V : ModuleCat.{0} ℚ)

/-- The full-complex universal coefficient isomorphism evaluates the literal cochain
on the literal chain, with the actual canonical homology classes on both sides. -/
theorem homologyEvaluationEquiv_classes (a : ℕ)
    (φ : Cycles ((homCochains K V).sc' (a-1) a (a+1)))
    (c : Cycles (K.sc' (a+1) a (a-1))) :
    homologyEvaluationEquiv K V a (Descent.cochainClass (homCochains K V) a φ)
      (Descent.chainClass K a c) = (show K.X a →ₗ[ℚ] V from φ.val) c.val := by
  have hφ := congrArg (fun f => f (cycleClass _ φ))
    ((homCochains K V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv_hom_id
  have hc := congrArg (fun f => f (cycleClass _ c))
    (K.homologyIsoSc' (a+1) a (a-1) (down_prev _) (down_next _)).inv_hom_id
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hφ hc
  change evaluationEquiv (K.sc' (a+1) a (a-1)) V
    (ShortComplex.homologyMap (shortDualIso K V a).hom
      (((homCochains K V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).hom
        (((homCochains K V).homologyIsoSc' (a-1) a (a+1) (up_prev _) (up_next _)).inv
          (cycleClass _ φ))))
    ((K.homologyIsoSc' (a+1) a (a-1) (down_prev _) (down_next _)).hom
      ((K.homologyIsoSc' (a+1) a (a-1) (down_prev _) (down_next _)).inv
        (cycleClass _ c))) = _
  erw [hφ, hc, cycleClass_natural, evaluationEquiv_cycleClasses]
  rfl

end TernaryPoly.RationalHomologyCoefficients
