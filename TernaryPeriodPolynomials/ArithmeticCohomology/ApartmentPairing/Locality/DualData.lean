module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Link
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.RestrictCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.FrameFor
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.EvaluationLink
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SupportTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.CarriedRange
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Span

@[expose] public section


/-!
# Lemma 3.3, G3: compatible duals of a cellular cycle

`dual_data`: for the frame of a finite set of top cells and a cellular cycle `z` in the span of those cells, there
are a compact `K` inside the image of the neighbourhood `D` of the retract, a class `y₁` supported in `K` whose
cap is the class of the cycle `z` (support lemma `dual_of_carried`), and compatible cocycle representatives upstairs
and on the compact bordification (`exists_transport`), whose relative cap class is the bordified class of the
cellular cycle (`cell_class_link`).

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
  TernaryPoly.SingularLocalCap.Descent TernaryPoly.SymmetricSpaceRelativeFundamental
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

theorem hpS_open (F : FrameOut) : IsOpen (F.D1 pS) :=
  pS_isQuotientCovering.isOpenQuotientMap.isOpenMap _ F.hDo

/-- Compatible duals of a cellular cycle carried by finitely many cells whose translates lie in a
open set `D` of the symmetric space. -/
theorem dual_data_open (D : Set Space) (hDo : IsOpen D) (𝒞 : Finset (Graded 3))
    (hFD : ∀ C ∈ 𝒞, ∀ g : principalSix, g • cellSet 3 C.1 ⊆ D)
    (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (hz𝒞 : z ∈ cellSpan W 𝒞)
    (hzS : (coinvariantChains principalSix SpaceTop W).d 3 2 ((cellCoinvMapS W).f 3 z) = 0) :
    ∃ (K : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
      (_ : (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) ⊆ pS '' D)
      (y₁ : (supportCochains pS W (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).homology 2)
      (φ : Cycles ((supportCochains pS W
        (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).sc' (2 - 1) 2 (2 + 1)))
      (φh : Cycles ((supportCochains wholeProjection W
        ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
          Compacts BordifiedOrbit) : Set BordifiedOrbit)).sc' (2 - 1) 2 (2 + 1))),
      compactCapMap pS W 3 interiorEuclidean interiorOrientation 2 3 rfl (compactClassMap pS W K 2 y₁) =
        chainClass (localChains pS pS_isQuotientCovering W) 3
          (⟨degreeEquiv pS pS_isQuotientCovering W 3 ((cellCoinvMapS W).f 3 z),
            degreeEquiv_cycle pS W _ hzS⟩ :
            Cycles ((localChains pS pS_isQuotientCovering W).sc' (3 + 1) 3 (3 - 1))) ∧
      cochainClass (supportCochains pS W (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)) 2 φ = y₁ ∧
      (∀ τ : SingularSimplex (TopCat.of Space) 2,
        vertexToFunction pS pS_isQuotientCovering
            ((supportInclusion pS W
              (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val) τ =
          vertexToFunction wholeProjection wholeQuotientCovering
            ((supportInclusion wholeProjection W
              ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
                Compacts BordifiedOrbit) : Set BordifiedOrbit)).f 2 φh.val)
            (projection upstairs 2 τ)) ∧
      SymmetricSpaceRelativeCap.relativeCapMap W 2 3 rfl
          (homologyMap (supportMap wholeProjection W
            ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
              Compacts BordifiedOrbit) : Set BordifiedOrbit)
            (SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ
            (openCompactImage_subset CompactInteriorRelativeBoundary.boundaryComplementOpen K)) 2
            (cochainClass (supportCochains wholeProjection W
              ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
                Compacts BordifiedOrbit) : Set BordifiedOrbit)) 2 φh)) =
        homologyMap (cellToBordified W) 3 (cellClass W z hz) := by
  have hD1open : IsOpen (pS '' D) :=
    pS_isQuotientCovering.isOpenQuotientMap.isOpenMap _ hDo
  let D1 : Opens ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ := ⟨pS '' D, hD1open⟩
  have hC : ∀ C ∈ 𝒞, cellSet 3 C.1 ⊆ pS ⁻¹' (D1 : Set _) := by
    intro C hC S hS
    have : S ∈ D := hFD C hC 1 (by rw [one_smul]; exact hS)
    exact ⟨S, this, rfl⟩
  have hrange := cellCoinvMapS_range (D1 : Set _) 𝒞 hC W z hz𝒞
  obtain ⟨K, hK, y₁, hy₁⟩ := dual_of_carried pS W interiorEuclidean interiorOrientation D1
    ((cellCoinvMapS W).f 3 z) hzS hrange
  obtain ⟨φh, φ, hφ, hvt, hcap⟩ := exists_transport W K y₁
  refine ⟨K, hK, y₁, φ, φh, hy₁, hφ, hvt, ?_⟩
  rw [hcap, hy₁]
  exact cell_class_link W z hz hzS


theorem dual_data (F : FrameOut) (𝒞 : Finset (Graded 3))
    (hFD : ∀ C ∈ 𝒞, ∀ g : principalSix, g • cellSet 3 C.1 ⊆ F.D)
    (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0)
    (hz𝒞 : z ∈ cellSpan W 𝒞)
    (hzS : (coinvariantChains principalSix SpaceTop W).d 3 2 ((cellCoinvMapS W).f 3 z) = 0) :
    ∃ (K : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
      (_ : (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) ⊆ F.D1 pS)
      (y₁ : (supportCochains pS W (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).homology 2)
      (φ : Cycles ((supportCochains pS W
        (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).sc' (2 - 1) 2 (2 + 1)))
      (φh : Cycles ((supportCochains wholeProjection W
        ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
          Compacts BordifiedOrbit) : Set BordifiedOrbit)).sc' (2 - 1) 2 (2 + 1))),
      compactCapMap pS W 3 interiorEuclidean interiorOrientation 2 3 rfl (compactClassMap pS W K 2 y₁) =
        chainClass (localChains pS pS_isQuotientCovering W) 3
          (⟨degreeEquiv pS pS_isQuotientCovering W 3 ((cellCoinvMapS W).f 3 z),
            degreeEquiv_cycle pS W _ hzS⟩ :
            Cycles ((localChains pS pS_isQuotientCovering W).sc' (3 + 1) 3 (3 - 1))) ∧
      cochainClass (supportCochains pS W (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)) 2 φ = y₁ ∧
      (∀ τ : SingularSimplex (TopCat.of Space) 2,
        vertexToFunction pS pS_isQuotientCovering
            ((supportInclusion pS W
              (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val) τ =
          vertexToFunction wholeProjection wholeQuotientCovering
            ((supportInclusion wholeProjection W
              ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
                Compacts BordifiedOrbit) : Set BordifiedOrbit)).f 2 φh.val)
            (projection upstairs 2 τ)) ∧
      SymmetricSpaceRelativeCap.relativeCapMap W 2 3 rfl
          (homologyMap (supportMap wholeProjection W
            ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
              Compacts BordifiedOrbit) : Set BordifiedOrbit)
            (SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ
            (openCompactImage_subset CompactInteriorRelativeBoundary.boundaryComplementOpen K)) 2
            (cochainClass (supportCochains wholeProjection W
              ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :
                Compacts BordifiedOrbit) : Set BordifiedOrbit)) 2 φh)) =
        homologyMap (cellToBordified W) 3 (cellClass W z hz) := by
  exact dual_data_open F.D F.hDo 𝒞 hFD W z hz hz𝒞 hzS

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
