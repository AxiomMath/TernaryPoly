module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarNaturality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarSplit

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] [MulAction G Y] [ContinuousConstSMul G Y]
  (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Coefficient postcomposition commutes with actual rational singular pullback. -/
theorem rationalPullback_coefficient {A B : Rep.{0} ℚ G} (u : A ⟶ B) :
    SingularCoverNaturality.cochainPullback f hf A ≫ EquivariantSingularCohomology.cochainMap G X u =
      EquivariantSingularCohomology.cochainMap G Y u ≫ SingularCoverNaturality.cochainPullback f hf B := by
  ext n c
  rfl

/-- The actual cochain scalar inclusion commutes with every equivariant continuous pullback. -/
theorem realCochainInclusion_pullback (A : Rep.{0} ℚ G) :
    SingularCoverNaturality.cochainPullback f hf A ≫ realCochainInclusion G X A =
      realCochainInclusion G Y A ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (cochainPullback f hf (realRep A)) := by
  unfold realCochainInclusion
  rw [← Category.assoc, rationalPullback_coefficient, Category.assoc, scalarCochainIso_pullback]
  exact (Category.assoc _ _ _).symm

/-- The actual rational cochain retraction commutes with geometric pullback as well. -/
theorem realCochainRetraction_pullback (A : Rep.{0} ℚ G) :
    (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (cochainPullback f hf (realRep A)) ≫
        realCochainRetraction G X A =
      realCochainRetraction G Y A ≫ SingularCoverNaturality.cochainPullback f hf A := by
  have hi := scalarCochainIso_pullback f hf (realRep A)
  have hv : (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (cochainPullback f hf (realRep A)) ≫
      (scalarCochainIso G X (realRep A)).inv =
    (scalarCochainIso G Y (realRep A)).inv ≫ SingularCoverNaturality.cochainPullback f hf (rationalRep (realRep A)) := by
    apply (cancel_mono (scalarCochainIso G X (realRep A)).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using
      congrArg (fun k => (scalarCochainIso G Y (realRep A)).inv ≫ k) hi.symm
  unfold realCochainRetraction
  rw [← Category.assoc, hv, Category.assoc, rationalPullback_coefficient]
  exact (Category.assoc _ _ _).symm

/-- Exact scalar restriction's homology isomorphism is natural for actual cochain maps. -/
theorem realHomologyForgetIso_naturality {K L : CochainComplex (ModuleCat ℝ) ℕ}
    (u : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap ((forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map u) n ≫
        (realHomologyForgetIso L n).hom =
      (realHomologyForgetIso K n).hom ≫ forgetReal.map (HomologicalComplex.homologyMap u n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map u) forgetReal

/-- Actual real extension commutes with genuine pullback on singular cohomology. -/
theorem realSingularCohomologyInclusion_pullback (A : Rep.{0} ℚ G) (n : ℕ) :
    HomologicalComplex.homologyMap (SingularCoverNaturality.cochainPullback f hf A) n ≫
        realSingularCohomologyInclusion G X A n =
      realSingularCohomologyInclusion G Y A n ≫
        forgetReal.map (HomologicalComplex.homologyMap (cochainPullback f hf (realRep A)) n) := by
  unfold realSingularCohomologyInclusion
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, realCochainInclusion_pullback,
    HomologicalComplex.homologyMap_comp, Category.assoc, realHomologyForgetIso_naturality]
  exact (Category.assoc _ _ _).symm

end TernaryPoly.SmoothSingularGlobal
