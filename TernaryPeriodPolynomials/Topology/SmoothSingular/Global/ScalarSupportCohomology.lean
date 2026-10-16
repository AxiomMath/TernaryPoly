module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarSupportDiagrams

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set SymmetricSpaceCovering TopologicalSpace

/-- An actual cochain square transports through homology and exact scalar restriction. -/
theorem realHomologySquare {Q Q' : CochainComplex (ModuleCat ℚ) ℕ}
    {R R' : CochainComplex (ModuleCat ℝ) ℕ} (q : Q ⟶ Q') (r : R ⟶ R')
    (i : Q ⟶ (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj R)
    (i' : Q' ⟶ (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj R')
    (h : q ≫ i' = i ≫ (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map r) (n : ℕ) :
    HomologicalComplex.homologyMap q n ≫
        (HomologicalComplex.homologyMap i' n ≫ (realHomologyForgetIso R' n).hom) =
      (HomologicalComplex.homologyMap i n ≫ (realHomologyForgetIso R n).hom) ≫
        forgetReal.map (HomologicalComplex.homologyMap r n) := by
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, h,
    HomologicalComplex.homologyMap_comp, Category.assoc, realHomologyForgetIso_naturality]
  exact (Category.assoc _ _ _).symm

/-- A genuine cochain splitting remains split after homology and scalar restriction. -/
theorem realHomologySplit {Q : CochainComplex (ModuleCat ℚ) ℕ}
    {R : CochainComplex (ModuleCat ℝ) ℕ}
    (i : Q ⟶ (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj R)
    (r : (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj R ⟶ Q)
    (h : i ≫ r = 𝟙 _) (n : ℕ) :
    (HomologicalComplex.homologyMap i n ≫ (realHomologyForgetIso R n).hom) ≫
      ((realHomologyForgetIso R n).inv ≫ HomologicalComplex.homologyMap r n) = 𝟙 _ := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← HomologicalComplex.homologyMap_comp,
    h, HomologicalComplex.homologyMap_id]

variable (A : Rep.{0} ℚ DeckGroup)

/-- Actual rational-to-real extension on fixed-support singular cohomology. -/
def realCoverSupportCohomologyInclusion (K : Set OrbitSpace) (n : ℕ) :
    (rationalCoverSupport A K).homology n ⟶ forgetReal.obj ((realCoverSupport A K).homology n) :=
  HomologicalComplex.homologyMap (realCoverSupportInclusion A K) n ≫
    (realHomologyForgetIso (realCoverSupport A K) n).hom

/-- Scalar extension respects actual support enlargement on cohomology. -/
theorem realCoverSupportCohomologyInclusion_natural (K L : Set OrbitSpace) (hKL : K ⊆ L) (n : ℕ) :
    HomologicalComplex.homologyMap (rationalCoverSupportMap A K L hKL) n ≫
        realCoverSupportCohomologyInclusion A L n =
      realCoverSupportCohomologyInclusion A K n ≫
        forgetReal.map (HomologicalComplex.homologyMap (realCoverSupportMap A K L hKL) n) :=
  realHomologySquare _ _ _ _ (realCoverSupportInclusion_natural A K L hKL) n

/-- Fixed-support rational-to-real extension commutes with the actual map to ordinary cohomology. -/
theorem realCoverSupportCohomologyInclusion_forget (K : Set OrbitSpace) (n : ℕ) :
    HomologicalComplex.homologyMap (kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ))) n ≫
        realSingularCohomologyInclusion DeckGroup (TopCat.of (CoverOpen univ)) A n =
      realCoverSupportCohomologyInclusion A K n ≫ forgetReal.map
        (HomologicalComplex.homologyMap (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Kᶜ))) n) :=
  realHomologySquare _ _ _ _ (realCoverSupportInclusion_forget A K).symm n

/-- Scalar extension is a genuine natural transformation on the actual compact-support diagram. -/
def realCoverCompactExtension (n : ℕ) :
    rationalCoverCompactDiagram A n ⟶ realCoverCompactDiagram A n ⋙ forgetReal where
  app K := realCoverSupportCohomologyInclusion A K n
  naturality K L f := realCoverSupportCohomologyInclusion_natural A K L (leOfHom f) n

/-- The real relative map retains a rational splitting on each fixed-support cohomology group. -/
theorem realCoverSupportCohomologyInclusion_split (K : Set OrbitSpace) (n : ℕ) :
    realCoverSupportCohomologyInclusion A K n ≫
      ((realHomologyForgetIso (realCoverSupport A K) n).inv ≫ HomologicalComplex.homologyMap
        (realRelativeRetraction (coverInclusion (subset_univ Kᶜ)) (coverInclusion_equivariant (subset_univ Kᶜ)) A) n) = 𝟙 _ :=
  realHomologySplit _ _ (realRelative_split (coverInclusion (subset_univ Kᶜ))
    (coverInclusion_equivariant (subset_univ Kᶜ)) A) n

end TernaryPoly.SmoothSingularGlobal
