module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarComplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularNaturality
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory FreeActionLinearization
open scoped Simplicial
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] [MulAction G Y] [ContinuousConstSMul G Y]
  (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (V : Rep.{0} ℝ G)

/-- Scalar comparison preserves actual pullback values in each degree. -/
theorem scalarCochainEquiv_pullback (n : ℕ)
    (c : EquivariantSingularResolution.chainRep G Y n ⟶ rationalRep V) :
    scalarCochainEquiv G X V n ((SingularCoverNaturality.cochainPullback f hf (rationalRep V)).f n c) =
      (cochainPullback f hf V).f n (scalarCochainEquiv G Y V n c) := by
  apply (cochainFunctionEquiv G X V n).injective
  apply Subtype.ext
  funext σ
  exact (scalarCochainEquiv_evaluate G X V n _ σ).trans
    ((congrArg (fun m => c.hom (m.hom 1)) (SingularCoverNaturality.generator_map f n σ)).trans
      ((scalarCochainEquiv_evaluate G Y V n c ((TopCat.toSSet.map f).app (.op ⦋n⦌) σ)).symm.trans
        (cochainPullback_evaluate f hf V n (scalarCochainEquiv G Y V n c) σ).symm))

/-- The scalar comparison preserves pullback by every actual equivariant continuous map. -/
theorem scalarCochainIso_pullback :
    SingularCoverNaturality.cochainPullback f hf (rationalRep V) ≫ (scalarCochainIso G X V).hom =
      (scalarCochainIso G Y V).hom ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (cochainPullback f hf V) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact scalarCochainEquiv_pullback f hf V n c

variable {V} {W : Rep.{0} ℝ G}

/-- Restricting a real coefficient morphism gives its literal rational equivariant morphism. -/
def rationalCoefficientMap (u : V ⟶ W) : rationalRep V ⟶ rationalRep W :=
  Rep.ofHom ⟨(forgetReal.map (ModuleCat.ofHom u.hom.toLinearMap)).hom, fun g => by
    exact congrArg (fun k => (forgetReal.map (ModuleCat.ofHom k)).hom) (u.hom.isIntertwining' g)⟩

/-- Scalar comparison is natural in the actual coefficient representation. -/
theorem scalarCochainIso_coefficient (u : V ⟶ W) :
    EquivariantSingularCohomology.cochainMap G X (rationalCoefficientMap u) ≫ (scalarCochainIso G X W).hom =
      (scalarCochainIso G X V).hom ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (cochainMap G X u) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply (cochainFunctionEquiv G X W n).injective
  apply Subtype.ext
  funext σ
  change cochainFunctionEquiv G X W n
      (scalarCochainEquiv G X W n ((EquivariantSingularCohomology.cochainMap G X (rationalCoefficientMap u)).f n c)) σ =
    cochainFunctionEquiv G X W n ((cochainMap G X u).f n (scalarCochainEquiv G X V n c)) σ
  erw [scalarCochainEquiv_evaluate]
  change u.hom (EquivariantSingularCohomology.cochainFunctionEquiv G X (rationalRep V) n c σ) =
    u.hom (cochainFunctionEquiv G X V n (scalarCochainEquiv G X V n c) σ)
  exact congrArg u.hom (scalarCochainEquiv_evaluate G X V n c σ).symm

end TernaryPoly.SmoothSingularGlobal
