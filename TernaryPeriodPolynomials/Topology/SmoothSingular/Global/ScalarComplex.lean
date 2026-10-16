module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarFunctions

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory
open FreeActionLinearization
variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
  (V : Rep.{0} ℝ G)

/-- Scalar comparison commutes with the genuine singular differential, since the literal
alternating integer face sums coincide on every actual singular generator. -/
theorem scalarCochainEquiv_d (n : ℕ)
    (f : EquivariantSingularResolution.chainRep G X n ⟶ rationalRep V) :
    scalarCochainEquiv G X V (n+1)
      ((EquivariantSingularCohomology.cochains G X (rationalRep V)).d n (n+1) f) =
        (cochains G X V).d n (n+1) (scalarCochainEquiv G X V n f) := by
  apply (cochainFunctionEquiv G X V (n+1)).injective
  apply Subtype.ext
  funext σ
  erw [scalarCochainEquiv_evaluate, EquivariantSingularCohomology.evaluate_d, evaluate_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarCochainEquiv_evaluate]
  rfl

/-- Actual rational singular Hom cochains with restricted real coefficients are isomorphic to
scalar restriction of the actual real singular Hom complex, preserving all simplex values. -/
def scalarCochainIso :
    EquivariantSingularCohomology.cochains G X (rationalRep V) ≅
      (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (cochains G X V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (scalarCochainEquiv G X V n).toModuleIso) (by
      intro i j hij
      have h : i+1=j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (scalarCochainEquiv_d G X V i f).symm)

/-- The chain comparison remains the literal generator-preserving scalar equivalence. -/
theorem scalarCochainIso_hom_apply (n : ℕ)
    (f : EquivariantSingularResolution.chainRep G X n ⟶ rationalRep V) :
    (scalarCochainIso G X V).hom.f n f = scalarCochainEquiv G X V n f := rfl

end TernaryPoly.SmoothSingularGlobal
