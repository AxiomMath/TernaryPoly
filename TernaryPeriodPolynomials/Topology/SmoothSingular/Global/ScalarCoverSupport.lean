module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarRelative
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarSquares

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set SymmetricSpaceCovering

variable (A : Rep.{0} ℚ DeckGroup)

/-- Actual rational equivariant singular cochains on each genuine lifted quotient domain. -/
abbrev rationalCoverCochains (U : Set OrbitSpace) :=
  EquivariantSingularCohomology.cochains DeckGroup (TopCat.of (CoverOpen U)) A

/-- The genuine rational geometric covering restriction. -/
abbrev rationalCoverRestriction {U V : Set OrbitSpace} (hVU : V ⊆ U) :
    rationalCoverCochains A U ⟶ rationalCoverCochains A V :=
  SingularCoverNaturality.cochainPullback (coverInclusion hVU) (coverInclusion_equivariant hVU) A

/-- Actual covering restriction of rational singular cochains composes. -/
theorem rationalCoverRestriction_comp {U V W : Set OrbitSpace} (hVU : V ⊆ U) (hWV : W ⊆ V) :
    rationalCoverRestriction A hVU ≫ rationalCoverRestriction A hWV = rationalCoverRestriction A (hWV.trans hVU) := by
  have h := (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map_comp (coverInclusion hWV) (coverInclusion hVU))
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (congrArg (fun k => c.hom ((k.f n).hom x)) h).symm

/-- Actual covering restriction of real singular cochains composes. -/
theorem realCoverRestriction_comp (V : Rep.{0} ℝ DeckGroup) {U D W : Set OrbitSpace}
    (hDU : D ⊆ U) (hWD : W ⊆ D) :
    coveringCochainRestriction V.ρ hDU ≫ coveringCochainRestriction V.ρ hWD =
      coveringCochainRestriction V.ρ (hWD.trans hDU) :=
  (cochainPullback_comp (coverInclusion hWD) (coverInclusion_equivariant hWD)
    (coverInclusion hDU) (coverInclusion_equivariant hDU) V).symm

/-- Rational cochains with actual complement-relative support. -/
abbrev rationalCoverSupport (K : Set OrbitSpace) :=
  kernel (rationalCoverRestriction A (subset_univ Kᶜ))

/-- Real cochains with actual complement-relative support. -/
abbrev realCoverSupport (K : Set OrbitSpace) :=
  kernel (coveringCochainRestriction (realRep A).ρ (subset_univ Kᶜ))

/-- Actual rational support enlargement preserves the same ambient cochain. -/
def rationalCoverSupportMap (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    rationalCoverSupport A K ⟶ rationalCoverSupport A L :=
  kernel.lift _ (kernel.ι _) (by
    rw [← rationalCoverRestriction_comp A (subset_univ Kᶜ) (compl_subset_compl.mpr hKL),
      ← Category.assoc, kernel.condition, zero_comp])

/-- Actual real support enlargement preserves the same ambient cochain. -/
def realCoverSupportMap (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    realCoverSupport A K ⟶ realCoverSupport A L :=
  kernel.lift _ (kernel.ι _) (by
    rw [← realCoverRestriction_comp (realRep A) (subset_univ Kᶜ) (compl_subset_compl.mpr hKL),
      ← Category.assoc, kernel.condition, zero_comp])

/-- Actual scalar extension on complement-relative covering cochains. -/
abbrev realCoverSupportInclusion (K : Set OrbitSpace) :
    rationalCoverSupport A K ⟶
      (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).obj (realCoverSupport A K) :=
  realRelativeInclusion (coverInclusion (subset_univ Kᶜ)) (coverInclusion_equivariant (subset_univ Kᶜ)) A

/-- Literal fixed-support scalar extension followed by support forgetting. -/
theorem realCoverSupportInclusion_forget (K : Set OrbitSpace) :
    realCoverSupportInclusion A K ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Kᶜ))) =
      kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ)) ≫
        realCochainInclusion DeckGroup (TopCat.of (CoverOpen univ)) A :=
  realRelativeInclusion_forget (coverInclusion (subset_univ Kᶜ))
    (coverInclusion_equivariant (subset_univ Kᶜ)) A

/-- Scalar extension commutes with every genuine support enlargement. -/
theorem realCoverSupportInclusion_natural (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    rationalCoverSupportMap A K L hKL ≫ realCoverSupportInclusion A L =
      realCoverSupportInclusion A K ≫
        (forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)).map (realCoverSupportMap A K L hKL) := by
  let F := forgetReal.mapHomologicalComplex (ComplexShape.up ℕ)
  exact supportSquare_of_mono
    (kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ)))
    (kernel.ι (rationalCoverRestriction A (subset_univ Lᶜ)))
    (F.map (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Kᶜ))))
    (F.map (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ Lᶜ))))
    (rationalCoverSupportMap A K L hKL) (F.map (realCoverSupportMap A K L hKL))
    (realCoverSupportInclusion A K) (realCoverSupportInclusion A L)
    (realCochainInclusion DeckGroup (TopCat.of (CoverOpen univ)) A)
    (kernel.lift_ι _ _ _)
    ((F.map_comp _ _).symm.trans (congrArg F.map (kernel.lift_ι _ _ _)))
    (realCoverSupportInclusion_forget A K) (realCoverSupportInclusion_forget A L)

end TernaryPoly.SmoothSingularGlobal
