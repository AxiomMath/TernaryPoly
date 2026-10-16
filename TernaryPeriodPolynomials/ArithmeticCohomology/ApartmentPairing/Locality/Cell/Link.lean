module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.CarriedRange
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SupportTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.DegreeHomotopy
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0

@[expose] public section


/-!
# Lemma 3.3, G3: the cellular class in the symmetric space and in the bordification

`cellCoinvMapS_upstairs`: the cellular chain map into the symmetric space followed by the upstairs inclusion is
the cellular chain map into the bordification.  `chainClass_eq_homologyπ`: the class of a chain cycle in the
`sc'` model is the class of the corresponding cycle of the complex.  `cell_class_link`: the local-chain map of
the covering square `(upstairs, interior ⊆ bordification)` sends the geometric class of a cellular cycle of the
symmetric space to the bordified class `homologyMap (cellToBordified W)` of the cellular class.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceBordifiedCohomology
  TernaryPoly.SingularLocalCap.Descent
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- The cellular chain map into the symmetric space followed by the upstairs inclusion is the cellular
chain map into the bordification. -/
theorem cellCoinvMapS_upstairs (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) :
    (coinvariantSpaceMap upstairs upstairs_equivariant W).f 3 ((cellCoinvMapS W).f 3 z) =
      (cellCoinvMap W).f 3 z := by
  obtain ⟨𝒞, h𝒞⟩ := exists_cellSpan W z
  induction h𝒞 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, hC, w, rfl⟩ := hx
    rw [cellCoinvMapS_mk, cellCoinvMap_mk, coinvariantSpaceMap_mk]
    congr 1
    exact (cellAt_eq_embedding_map 3 C.1).symm
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, map_smul, hx]

/-- A chain cycle given in the `sc'` model represents the same class as the corresponding cycle of the
complex. -/
theorem chainClass_eq_homologyπ (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (x : Cycles (K.sc' (n + 1) n (n - 1))) (x' : K.cycles n)
    (h : K.iCycles n x' = x.val) :
    chainClass K n x = K.homologyπ n x' := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  have h1 := TernaryPoly.SingularLocalCompactCap.Algebra.represented_opcycles K (n + 1) n (n - 1)
    (down_prev _) (down_next _) x
  have h2 := congrArg (fun f => f x') (K.homology_π_ι n)
  change K.homologyι n (chainClass K n x) = K.pOpcycles n x.val at h1
  change K.homologyι n (K.homologyπ n x') = K.pOpcycles n (K.iCycles n x') at h2
  rw [h1, h2, h]

theorem cell_class_link (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
    (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (hzS : (coinvariantChains principalSix SpaceTop W).d 3 2 ((cellCoinvMapS W).f 3 z) = 0) :
    homologyMap (spaceChainMap W) 3
      (chainClass (localChains pS pS_isQuotientCovering W) 3
        (⟨degreeEquiv pS pS_isQuotientCovering W 3 ((cellCoinvMapS W).f 3 z),
          degreeEquiv_cycle pS W _ hzS⟩ :
          Cycles ((localChains pS pS_isQuotientCovering W).sc' (3 + 1) 3 (3 - 1)))) =
      homologyMap (cellToBordified W) 3 (cellClass W z hz) := by
  have hcyc' : (bordifiedLocalChains W).d 3 2 ((cellToBordified W).f 3 z) = 0 := by
    have h := ConcreteCategory.congr_hom ((cellToBordified W).comm 3 2) z
    refine h.trans ?_
    change (cellToBordified W).f 2 (((cellCoinv W).d 3 2) z) = 0
    rw [hz, map_zero]
  have hval : (spaceChainMap W).f 3 (degreeEquiv pS pS_isQuotientCovering W 3
      ((cellCoinvMapS W).f 3 z)) = (cellToBordified W).f 3 z := by
    have hnat := ConcreteCategory.congr_hom (congrArg (fun m => m.f 3)
      (chainIso_space_natural upstairs upstairs_equivariant W pS wholeProjection pS_isQuotientCovering
        wholeQuotientCovering)) ((cellCoinvMapS W).f 3 z)
    refine hnat.trans ?_
    change (chainIso wholeProjection wholeQuotientCovering W).hom.f 3
      ((coinvariantSpaceMap upstairs upstairs_equivariant W).f 3 ((cellCoinvMapS W).f 3 z)) = _
    rw [cellCoinvMapS_upstairs]
    rfl
  let x : Cycles ((localChains pS pS_isQuotientCovering W).sc' (3 + 1) 3 (3 - 1)) :=
    ⟨degreeEquiv pS pS_isQuotientCovering W 3 ((cellCoinvMapS W).f 3 z),
      degreeEquiv_cycle pS W _ hzS⟩
  let xc : Cycles ((cellCoinv W).sc' (3 + 1) 3 (3 - 1)) := ⟨z, hz⟩
  have hcell : cellClass W z hz = chainClass (cellCoinv W) 3 xc := by
    symm
    exact chainClass_eq_homologyπ (cellCoinv W) 3 xc
      ((cellCoinv W).cyclesMk z 2 next_three hz)
      ((cellCoinv W).i_cyclesMk z 2 next_three hz)
  rw [hcell, TernaryPoly.SingularLocalOpenUnion.chainClass_map,
    TernaryPoly.SingularLocalOpenUnion.chainClass_map]
  congr 1
  exact Subtype.ext hval

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
