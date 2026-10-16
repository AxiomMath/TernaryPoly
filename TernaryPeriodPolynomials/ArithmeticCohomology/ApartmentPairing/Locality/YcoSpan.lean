module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Eval
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Span
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.MapS
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CoeffAtT0

@[expose] public section


/-!
# Lemma 3.3, G3: the translate-sum pairing on a cellular chain is the intersection sum

`Yco_cellSpan`: for the frame of a finite set of top cells and a Thom cochain `y` with the properties of
`exists_thom_pullback` along `π/ρ'`, the translate-sum pairing `Yco` of the image under `cellCoinvMapS` of
every element of `cellSpan W 𝒞` equals `intersectionSum W` of the element.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits Finsupp TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.IntegralGL3Congruence TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  TernaryPoly.EuclideanLocalHomology SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

/-- **The translate-sum pairing on a cellular chain is the intersection sum.** -/
theorem Yco_cellSpan (F : FrameOut)
    (y : singularChainGroup ℚ SpaceTop 3 →ₗ[ℚ] ℚ)
    (hfin : ∀ τ : SingularSimplex SpaceTop 3,
      {g : principalSix | y (chainGenerator ℚ SpaceTop 3 (g • τ)) ≠ 0}.Finite)
    (hy2 : ∀ τ : SingularSimplex SpaceTop 3,
      IsSubordinate {s : SpaceTop | 1 < ‖(thomMap F.ρ' F.hρc F.hρpos).hom s‖} τ →
        y (chainGenerator ℚ SpaceTop 3 τ) = 0)
    (hy3 : ∀ c : singularChainGroup ℚ SpaceTop 3,
      (singularBoundary ℚ SpaceTop 2).hom c ∈
        subChainSubmodule ℚ SpaceTop {s : SpaceTop | 1 < ‖(thomMap F.ρ' F.hρc F.hρpos).hom s‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom
          ((singularChainMap ℚ (thomMap F.ρ' F.hρc F.hρpos) 3).hom c)) = 0,
        y c = degR3 ((singularChainMap ℚ (thomMap F.ρ' F.hρc F.hρpos) 3).hom c) h)
    (𝒞 : Finset (Graded 3))
    (hcells : ∀ C ∈ 𝒞, ∀ g : principalSix, g • C.1 ≠ T0 →
      cellSet 3 (g • C.1) ⊆ {S : SpaceTop | F.ρ' S < ‖piR3 S‖})
    (hD2 : ∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ {S : SpaceTop | F.ρ' S < ‖piR3 S‖})
    (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : z ∈ cellSpan W 𝒞) :
    Yco W y hfin ((cellCoinvMapS W).f 3 z) = (intersectionSum W).hom z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, hC, w, rfl⟩ := hx
    rw [cellCoinvMapS_mk, Yco_cell F.ρ' F.hρc F.hρpos y hfin hy2 hy3 hD2 W w C (hcells C hC)]
    change dT0 • coeffVal W w C = dT0 • ((coeffAtT0 W).hom _)
    rw [coeffAtT0_mk]
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y' _ _ hx hy' => rw [map_add, map_add, map_add, hx, hy']
  | smul r x _ hx => rw [map_smul, map_smul, map_smul, hx]

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
