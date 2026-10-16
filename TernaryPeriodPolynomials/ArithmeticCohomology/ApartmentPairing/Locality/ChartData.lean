module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.DualData
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Loc
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Over
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ChartChain
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeCore

@[expose] public section


/-!
# Lemma 3.3, G3: the chart chain of the flat and its nonvanishing

`chart_chain_data`: for the frame of a finite set of cells and a compact `Kfull` of the base lying in the image of
the neighbourhood of the retract and the closed slab and containing the slab, the localization of the flat chain
(`flat_localize`) gives a chart chain `a` whose boundary lies off the slab and such that every ambient cochain of a
compatible pair of cocycles supported in a compact `K' ≤ Kfull` takes on the flat chain the value of the
pulled-back geometric cochain on `a`.  `haB_of_ne`: if some supported cocycle takes a nonzero value on `a`, then
`a` is not zero in the relative `H₂` of the chart modulo the slab.

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
  TernaryPoly.SymmetricSpaceRationalGluing
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33

theorem openCompactImage_mono {K K' : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ}
    (h : K' ≤ K) :
    openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' ≤
      openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K :=
  Set.image_mono h

theorem wholeProjection_embedding (S : Space) : wholeProjection (embedding S) = (pS S).val := rfl

/-- The chart chain of the flat and its two properties. -/
theorem chart_chain_data (F : FrameOut)
    (Kfull : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
    (hK : (Kfull : Set _) ⊆ F.D1 pS ∪ F.Qs pS) (hQ : F.Qs pS ⊆ (Kfull : Set _)) :
    ∃ a : singularChainGroup ℚ (TopCat.of ↥(F.UT pS)) 2,
      (singularBoundary ℚ (TopCat.of ↥(F.UT pS)) 1).hom a ∈
        subChainSubmodule ℚ (TopCat.of ↥(F.UT pS))
          {u : ↥(F.UT pS) | ‖((F.eY pS pS_isQuotientCovering u : boxSet F.ε F.R0) : R3 × R2).2‖ ≤ F.δ}ᶜ
          1 ∧
      ∀ (W : Rep.{0} ℚ principalSix)
        (K' : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ), K' ≤ Kfull →
        ∀ (φ : Cycles ((supportCochains pS W
          (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).sc' (2 - 1) 2 (2 + 1)))
          (φh : Cycles ((supportCochains wholeProjection W
            ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' :
              Compacts BordifiedOrbit) : Set BordifiedOrbit)).sc' (2 - 1) 2 (2 + 1))),
          (∀ τ : SingularSimplex (TopCat.of Space) 2,
            vertexToFunction pS pS_isQuotientCovering
                ((supportInclusion pS W
                  (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val) τ =
              vertexToFunction wholeProjection wholeQuotientCovering
                ((supportInclusion wholeProjection W
                  ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' :
                    Compacts BordifiedOrbit) : Set BordifiedOrbit)).f 2 φh.val)
                (projection upstairs 2 τ)) →
          (ambientCochain W
              (openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K') φh).hom
              flatRep =
            chainDesc (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
              vertexToFunction pS pS_isQuotientCovering
                ((supportInclusion pS W
                  (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val)
                (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) a := by
  have hp := pS_isQuotientCovering
  have hKA := openCompactImage_subset CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull
  have hKT : ∀ S : Space, S ∈ flat →
      wholeProjection (embedding S) ∈
        ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull :
          Compacts BordifiedOrbit) : Set BordifiedOrbit) → S ∈ F.Tt := by
    intro S hS hmem
    obtain ⟨k, hk, hkS⟩ := hmem
    have hkp : k = pS S := Subtype.ext (hkS.trans (wholeProjection_embedding S))
    rw [hkp] at hk
    exact F.flat_over pS hp (Kfull : Set _) hK S hS hk
  obtain ⟨FT, hFT, hFTb, hFTev⟩ := flat_localize F.Tt F.Tt_open _ hKA hKT
  obtain ⟨a, ha_eq⟩ := F.exists_chart_chain pS hp FT hFT
  refine ⟨a, ?_, ?_⟩
  · have hb : (singularBoundary ℚ (TopCat.of Glued) 1).hom
        ((singularChainMap ℚ (F.chartHom pS hp) 2).hom a) ∈ subChainSubmodule ℚ (TopCat.of Glued)
          (embedding '' F.Tt ∩ (wholeProjection ⁻¹' (((openCompactImage
            CompactInteriorRelativeBoundary.boundaryComplementOpen Kfull : Compacts BordifiedOrbit) :
            Set BordifiedOrbit)))ᶜ) 1 := by
      rw [ha_eq]; exact hFTb
    have h1 := F.chart_boundary_mem_sub pS hp a _ hb
    refine subChainSubmodule_mono ?_ 1 h1
    intro u hu hle
    apply hu.2
    have hQu : (u : ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) ∈ F.Qs pS :=
      (F.hQ pS hp u).mpr hle
    have hKQ := hQ hQu
    refine ⟨u.val, hKQ, ?_⟩
    have := congrArg Subtype.val (F.p_sec pS hp u)
    exact this.symm
  · intro W K' hK' φ φh hvt
    rw [hFTev W _ (openCompactImage_mono hK') φh, ← ha_eq,
      ambientCochain_chart_chain W _ φh (F.chartHom pS hp) a]
    have hfun : (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
        vertexToFunction wholeProjection wholeQuotientCovering
          ((supportInclusion wholeProjection W
            ((openCompactImage CompactInteriorRelativeBoundary.boundaryComplementOpen K' :
              Compacts BordifiedOrbit) : Set BordifiedOrbit)).f 2 φh.val)
          (pushSimplex (F.chartHom pS hp) 2 σ)) =
        (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
          vertexToFunction pS pS_isQuotientCovering
            ((supportInclusion pS W
              (K' : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val)
            (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) :=
      funext fun σ => (hvt (pushSimplex (F.sec pS hp) 2 σ)).symm
    rw [hfun]

/-- A chain carried by a set on whose subordinate simplices a function vanishes is killed by it. -/
theorem chainDesc_eq_zero_of_sub {X : TopCat.{0}} {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : SingularSimplex X 2 → M) (S : Set X) (hf : ∀ σ, IsSubordinate S σ → f σ = 0)
    (c : singularChainGroup ℚ X 2) (hc : c ∈ subChainSubmodule ℚ X S 2) : chainDesc f c = 0 := by
  refine subChainSubmodule_induction (S := S) (p := fun x => chainDesc f x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [chainDesc_generator]
    exact hf σ hσ
  · exact map_zero _
  · intro x y hx hy; rw [map_add, hx, hy, add_zero]
  · intro r x hx; rw [map_smul, hx, smul_zero]

/-- The chart chain is nonzero in the relative `H₂` of the chart modulo the slab as soon as some supported
cocycle takes a nonzero value on it. -/
theorem haB_of_ne (F : FrameOut) (W : Rep.{0} ℚ principalSix)
    (K : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
    (hK : (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) ⊆ F.D1 pS)
    (φ : Cycles ((supportCochains pS W
      (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).sc' (2 - 1) 2 (2 + 1)))
    (a : singularChainGroup ℚ (TopCat.of ↥(F.UT pS)) 2)
    (hne : chainDesc (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
      vertexToFunction pS pS_isQuotientCovering
        ((supportInclusion pS W
          (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val)
        (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) a ≠ 0) :
    a ∉ subChainSubmodule ℚ (TopCat.of ↥(F.UT pS))
        {u : ↥(F.UT pS) | ‖((F.eY pS pS_isQuotientCovering u : boxSet F.ε F.R0) : R3 × R2).2‖ ≤ F.δ}ᶜ 2 ⊔
      LinearMap.range (singularBoundary ℚ (TopCat.of ↥(F.UT pS)) 2).hom := by
  intro h
  obtain ⟨a', ha', b, ⟨f', rfl⟩, hsum⟩ := Submodule.mem_sup.mp h
  apply hne
  rw [← hsum, map_add]
  have hφd := supportInclusion_differential pS W
    (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) φ.val φ.property
  have h1 := cochainY_cocycle pS pS_isQuotientCovering W (F.sec pS pS_isQuotientCovering) _ hφd f'
  have hslab : {u : ↥(F.UT pS) |
      ‖((F.eY pS pS_isQuotientCovering u : boxSet F.ε F.R0) : R3 × R2).2‖ ≤ F.δ}ᶜ ⊆
      (Subtype.val : ↥(F.UT pS) → _) ⁻¹' (K : Set _)ᶜ := by
    intro u hu hmem
    exact hu ((F.hD1 pS pS_isQuotientCovering u.val (hK hmem) u rfl))
  have h2 := chainDesc_eq_zero_of_sub (X := TopCat.of ↥(F.UT pS))
    (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
      vertexToFunction pS pS_isQuotientCovering
        ((supportInclusion pS W
          (K : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ.val)
        (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ))
    ((Subtype.val : ↥(F.UT pS) → _) ⁻¹' (K : Set _)ᶜ)
    (fun τ hτ => cochainY_vanish pS pS_isQuotientCovering W (F.sec pS pS_isQuotientCovering)
        (F.sec_comp pS pS_isQuotientCovering) _ (UA := (K : Set _)ᶜ)
        (fun σ hσ => supportInclusion_vanish pS W _ φ.val σ hσ) τ hτ)
    a' (subChainSubmodule_mono hslab 2 ha')
  rw [h2, zero_add]
  exact h1

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
