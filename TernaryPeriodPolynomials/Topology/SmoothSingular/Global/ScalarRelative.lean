module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarSplitNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits
variable {G : Type} [Group G] {X Y : TopCat.{0}}
  [MulAction G X] [ContinuousConstSMul G X] [MulAction G Y] [ContinuousConstSMul G Y]
  (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The actual real relative singular cochain complex is the kernel of geometric restriction. -/
abbrev realRelativeCochains (V : Rep.{0} ℝ G) := kernel (cochainPullback f hf V)

/-- Scalar restriction identifies the actual rational and real relative singular kernels. -/
def scalarRelativeIso (V : Rep.{0} ℝ G) :
    kernel (SingularCoverNaturality.cochainPullback f hf (rationalRep V)) ≅
      (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (realRelativeCochains f hf V) :=
  kernel.mapIso _ _ (scalarCochainIso G Y V) (scalarCochainIso G X V)
    (scalarCochainIso_pullback f hf V) ≪≫
      (PreservesKernel.iso (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)) (cochainPullback f hf V)).symm

/-- The genuine relative scalar comparison retains the literal forget-relative map. -/
theorem scalarRelativeIso_forget (V : Rep.{0} ℝ G) :
    (scalarRelativeIso f hf V).hom ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (kernel.ι (cochainPullback f hf V)) =
      kernel.ι (SingularCoverNaturality.cochainPullback f hf (rationalRep V)) ≫ (scalarCochainIso G Y V).hom := by
  simp [scalarRelativeIso, Category.assoc]

/-- Scalar extension into actual real relative cochains. -/
def realRelativeInclusion (A : Rep.{0} ℚ G) :
    kernel (SingularCoverNaturality.cochainPullback f hf A) ⟶
      (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (realRelativeCochains f hf (realRep A)) :=
  kernel.map _ _ (EquivariantSingularCohomology.cochainMap G Y (coefficientInclusion A))
      (EquivariantSingularCohomology.cochainMap G X (coefficientInclusion A))
      (rationalPullback_coefficient f hf (coefficientInclusion A)) ≫ (scalarRelativeIso f hf (realRep A)).hom

/-- The genuine relative scalar-extension map commutes with forgetting relative support. -/
theorem realRelativeInclusion_forget (A : Rep.{0} ℚ G) :
    realRelativeInclusion f hf A ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (kernel.ι (cochainPullback f hf (realRep A))) =
      kernel.ι (SingularCoverNaturality.cochainPullback f hf A) ≫ realCochainInclusion G Y A := by
  simp only [realRelativeInclusion, Category.assoc, scalarRelativeIso_forget,
    kernel.map, kernel.lift_ι_assoc, realCochainInclusion]

/-- Actual rational retraction on the real relative singular complex. -/
def realRelativeRetraction (A : Rep.{0} ℚ G) :
    (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (realRelativeCochains f hf (realRep A)) ⟶
      kernel (SingularCoverNaturality.cochainPullback f hf A) :=
  (scalarRelativeIso f hf (realRep A)).inv ≫
    kernel.map _ _ (EquivariantSingularCohomology.cochainMap G Y (coefficientRetraction A))
      (EquivariantSingularCohomology.cochainMap G X (coefficientRetraction A))
      (rationalPullback_coefficient f hf (coefficientRetraction A))

/-- Real extension is split also on the actual relative cochain complexes. -/
theorem realRelative_split (A : Rep.{0} ℚ G) :
    realRelativeInclusion f hf A ≫ realRelativeRetraction f hf A = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (SingularCoverNaturality.cochainPullback f hf A))).mp
  simp only [realRelativeInclusion, realRelativeRetraction, Category.assoc, Iso.hom_inv_id_assoc,
    kernel.map, kernel.lift_ι, kernel.lift_ι_assoc, Category.id_comp,
    ← EquivariantSingularCohomology.cochainMap_comp, coefficient_split,
    EquivariantSingularCohomology.cochainMap_id, Category.comp_id]

end TernaryPoly.SmoothSingularGlobal
