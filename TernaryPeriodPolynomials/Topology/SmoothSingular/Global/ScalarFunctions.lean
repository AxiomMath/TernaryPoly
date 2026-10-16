module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.RealCoefficients
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Cochains
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyComplex

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory
open FreeActionLinearization
variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
  (V : Rep.{0} ℝ G) (n : ℕ)

/-- Rational scalar restriction keeps the actual equivariant simplex function and its deck law. -/
def scalarFunctionEquiv :
    EquivariantSingularCohomology.equivariantFunctions G X (rationalRep V) n ≃ₗ[ℚ]
      forgetReal.obj (ModuleCat.of ℝ (equivariantFunctions G X V n)) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal rational/real singular-cochain comparison is induced by the same actual
singular generator functions, with scalars explicitly restricted on the real target. -/
def scalarCochainEquiv :
    (EquivariantSingularResolution.chainRep G X n ⟶ rationalRep V) ≃ₗ[ℚ]
      forgetReal.obj (ModuleCat.of ℝ (chainRep G X n ⟶ V)) :=
  ((EquivariantSingularCohomology.cochainFunctionEquiv G X (rationalRep V) n).trans
    (scalarFunctionEquiv G X V n)).trans (forgetReal.mapIso (cochainFunctionEquiv G X V n).toModuleIso).toLinearEquiv.symm

/-- The scalar-comparison map preserves literal values on every actual singular generator. -/
theorem scalarCochainEquiv_evaluate (f : EquivariantSingularResolution.chainRep G X n ⟶ rationalRep V)
    (σ : SingularSimplex X n) :
    cochainFunctionEquiv G X V n (scalarCochainEquiv G X V n f) σ =
      EquivariantSingularCohomology.cochainFunctionEquiv G X (rationalRep V) n f σ := by
  let q := EquivariantSingularCohomology.cochainFunctionEquiv G X (rationalRep V) n f
  let r : equivariantFunctions G X V n := ⟨q.val, q.property⟩
  exact congrArg (fun h : equivariantFunctions G X V n => h σ)
    ((cochainFunctionEquiv G X V n).apply_symm_apply r)

end TernaryPoly.SmoothSingularGlobal
