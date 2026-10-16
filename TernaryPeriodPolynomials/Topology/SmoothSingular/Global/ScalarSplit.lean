module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarComplex

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory
variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
  (A : Rep.{0} ℚ G)

/-- Extension of actual rational singular cochains into real singular cochains is coefficient
inclusion followed by the literal generator comparison. -/
def realCochainInclusion : EquivariantSingularCohomology.cochains G X A ⟶
    (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (cochains G X (realRep A)) :=
  EquivariantSingularCohomology.cochainMap G X (coefficientInclusion A) ≫
    (scalarCochainIso G X (realRep A)).hom

/-- A rational linear retraction on the actual real singular complex. -/
def realCochainRetraction :
    (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (cochains G X (realRep A)) ⟶
      EquivariantSingularCohomology.cochains G X A :=
  (scalarCochainIso G X (realRep A)).inv ≫
    EquivariantSingularCohomology.cochainMap G X (coefficientRetraction A)

/-- Scalar extension of actual singular cochains is split before taking cohomology. -/
theorem realCochain_split : realCochainInclusion G X A ≫ realCochainRetraction G X A = 𝟙 _ := by
  simp only [realCochainInclusion, realCochainRetraction, Category.assoc, Iso.hom_inv_id_assoc,
    ← EquivariantSingularCohomology.cochainMap_comp, coefficient_split,
    EquivariantSingularCohomology.cochainMap_id]

/-- Exact rational scalar restriction commutes with homology of an actual real complex. -/
def realHomologyForgetIso (K : CochainComplex (ModuleCat ℝ) ℕ) (n : ℕ) :
    ((forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      forgetReal.obj (K.homology n) := (K.sc n).mapHomologyIso forgetReal

/-- Genuine scalar extension into the underlying rational module of real singular cohomology. -/
def realSingularCohomologyInclusion (n : ℕ) :
    (EquivariantSingularCohomology.cochains G X A).homology n ⟶
      forgetReal.obj ((cochains G X (realRep A)).homology n) :=
  HomologicalComplex.homologyMap (realCochainInclusion G X A) n ≫
    (realHomologyForgetIso (cochains G X (realRep A)) n).hom

/-- The actual cohomological rational retraction. -/
def realSingularCohomologyRetraction (n : ℕ) :
    forgetReal.obj ((cochains G X (realRep A)).homology n) ⟶
      (EquivariantSingularCohomology.cochains G X A).homology n :=
  (realHomologyForgetIso (cochains G X (realRep A)) n).inv ≫
    HomologicalComplex.homologyMap (realCochainRetraction G X A) n

/-- Rational-to-real singular cohomology extension is split in every degree for every real space
with a continuous group action, without finiteness assumptions. -/
theorem realSingularCohomology_split (n : ℕ) :
    realSingularCohomologyInclusion G X A n ≫ realSingularCohomologyRetraction G X A n = 𝟙 _ := by
  simp only [realSingularCohomologyInclusion, realSingularCohomologyRetraction,
    Category.assoc, Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp,
    realCochain_split, HomologicalComplex.homologyMap_id]

/-- Actual real singular cohomology detects every rational class. -/
theorem realSingularCohomology_injective (n : ℕ) :
    Function.Injective (realSingularCohomologyInclusion G X A n) := by
  have h : Function.LeftInverse (realSingularCohomologyRetraction G X A n)
      (realSingularCohomologyInclusion G X A n) := by
    intro x
    exact congrArg (fun u => u x) (realSingularCohomology_split G X A n)
  exact h.injective

end TernaryPoly.SmoothSingularGlobal
