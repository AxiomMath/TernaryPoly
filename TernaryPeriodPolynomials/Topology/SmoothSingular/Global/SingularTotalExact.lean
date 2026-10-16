module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularSmallAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree Module
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)

/-- Every actual singular Čech row, including the actual small-cochain augmentation, is exact
by the genuine equivariant simplex-flag contraction. -/
theorem singularCechTotalAugmentation_exactRows : (singularCechTotalAugmentation ρ U hU hcover).ExactRows where
  injective n := by
    intro x y h
    apply smallCochainToFlags_injective ρ U hU hcover n
    apply (smallSimplexIndexCover U hU hcover n).flagD_zero_injective ρ
    exact (smallCechAugmentation_toFlags ρ U hU hcover n x).symm.trans
      ((congrArg (singularCechToFlags ρ U hU hcover n 0) h).trans
        (smallCechAugmentation_toFlags ρ U hU hcover n y))
  augmentation_exact n x hx := by
    let a := singularCechToFlags ρ U hU hcover n 0 x
    have ha : (smallSimplexIndexCover U hU hcover n).flagD ρ 1 a = 0 :=
      (singularCechToFlags_d ρ U hU hcover n 0 x).symm.trans
        ((congrArg (singularCechToFlags ρ U hU hcover n 1) hx).trans (map_zero _))
    let b := (smallSimplexIndexCover U hU hcover n).flagH ρ 0 a
    refine ⟨(smallCochainFlagEquiv ρ U hU hcover n).symm b, ?_⟩
    apply (singularCechFlagEquiv ρ U hU hcover n 0).injective
    change singularCechToFlags ρ U hU hcover n 0 (smallCechAugmentationDegree ρ U hU hcover n _) = a
    rw [smallCechAugmentation_toFlags]
    change (smallSimplexIndexCover U hU hcover n).flagD ρ 0
      ((smallCochainFlagEquiv ρ U hU hcover n) ((smallCochainFlagEquiv ρ U hU hcover n).symm b)) = a
    rw [LinearEquiv.apply_symm_apply]
    exact (smallSimplexIndexCover U hU hcover n).flag_primitive ρ 0 a ha
  horizontal_exact p n x hx := singularCech_horizontal_primitive ρ U hU hcover n p x hx

/-- The genuine small-singular augmentation into the actual degree-two Čech–singular total
window is a quasi-isomorphism, with every row hypothesis discharged. -/
theorem singularCechTotalAugmentation_quasiIso :
    ShortComplex.QuasiIso (singularCechTotalAugmentation ρ U hU hcover).totalAugmentationMap :=
  (singularCechTotalAugmentation ρ U hU hcover).totalAugmentationMap_quasiIso
    (singularCechTotalAugmentation_exactRows ρ U hU hcover)

/-- Actual global singular H² is computed by the genuine Čech–singular total window for every
actual quotient open cover, using the actual subdivision restriction and actual Čech augmentation. -/
def globalSingularCechTotalIso :
    (coveringCochains ρ Set.univ).homology 2 ≅ (totalWindow (singularCechBicomplex ρ U)).homology := by
  have := coveringSmallRestriction_quasiIso ρ U hU Set.univ hcover
  exact isoOfQuasiIsoAt (coveringSmallRestriction ρ U hU Set.univ hcover) 2 ≪≫
    (coveringSmallCochains ρ U hU Set.univ hcover).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
      (singularCechTotalAugmentation ρ U hU hcover).totalAugmentationHomologyIso
        (singularCechTotalAugmentation_exactRows ρ U hU hcover)

/-- The actual global singular total isomorphism retains both literal descent maps. -/
theorem globalSingularCechTotalIso_hom : (globalSingularCechTotalIso ρ U hU hcover).hom =
    HomologicalComplex.homologyMap (coveringSmallRestriction ρ U hU Set.univ hcover) 2 ≫
      ((coveringSmallCochains ρ U hU Set.univ hcover).homologyIsoSc' 1 2 3 (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap (singularCechTotalAugmentation ρ U hU hcover).totalAugmentationMap := rfl

end TernaryPoly.SmoothSingularGlobal
