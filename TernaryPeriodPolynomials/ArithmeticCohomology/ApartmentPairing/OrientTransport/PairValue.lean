module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PairRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PairValueAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatChartData

@[expose] public section


/-!
# The pairwise relation with the value of the scalar

`pair_relation_value` is `Locality.pair_relation` (same proof) with the frame of `frame_for_const` (tube radius constant `η` on the
chart box), the explicit Thom pullback cochain, and `bridge_core_value` in place of `bridge_core`.  Besides the two relations
`I(z_i) = r • ev(z_i)` it returns a rational number `τ` — the value of the pulled-back planar Thom cochain on the chart chain `a`
of the flat — with `d₅ · r · τ = lamPos · lam2`, where `d₅` is the library degree of the staircase product cell.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient

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
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.OrdinaryTopBoundaryComparison
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33

/-- **The pairwise relation.**  For two cellular top cycles `z₁` (in `W₁`) and `z₂` (in `W₂`) the arithmetic
evaluator of the class of `z₂` being nonzero, there is a single scalar `r` with
`I(z_i) = r • ev(z_i)`, where `I = intersectionSum` and `ev(z) = groupApartmentEvaluation` of the class of `z`. -/
theorem pair_relation_value (W₁ W₂ : Rep.{0} ℚ principalSix)
    (z₁ : (cellCoinv W₁).X 3) (hz₁ : ((cellCoinv W₁).d 3 2).hom z₁ = 0)
    (z₂ : (cellCoinv W₂).X 3) (hz₂ : ((cellCoinv W₂).d 3 2).hom z₂ = 0)
    (hne : (groupApartmentEvaluation W₂).hom ((cellGroupHomologyMap W₂ 3).hom (cellClass W₂ z₂ hz₂)) ≠ 0) :
    ∃ (r τ : ℚ),
      (intersectionSum W₁).hom z₁ =
        r • (groupApartmentEvaluation W₁).hom ((cellGroupHomologyMap W₁ 3).hom (cellClass W₁ z₁ hz₁)) ∧
      (intersectionSum W₂).hom z₂ =
        r • (groupApartmentEvaluation W₂).hom ((cellGroupHomologyMap W₂ 3).hom (cellClass W₂ z₂ hz₂)) ∧
      d5 * r * τ = lamPos * lam2 ∧ τ = lam2 := by
  have hp := pS_isQuotientCovering
  obtain ⟨𝒞₁, h₁⟩ := exists_cellSpan W₁ z₁
  obtain ⟨𝒞₂, h₂⟩ := exists_cellSpan W₂ z₂
  have h₁' : z₁ ∈ cellSpan W₁ (𝒞₁ ∪ 𝒞₂) := cellSpan_mono W₁ Finset.subset_union_left h₁
  have h₂' : z₂ ∈ cellSpan W₂ (𝒞₁ ∪ 𝒞₂) := cellSpan_mono W₂ Finset.subset_union_right h₂
  obtain ⟨F, hFD, hcells, hD2, η, hη, hηc⟩ := frame_for_const (𝒞₁ ∪ 𝒞₂)
  obtain ⟨Y₁, Θ₁, T⟩ := exists_unitThom
  obtain ⟨hy, hy2, hy3⟩ := thom_pullback_of T (thomMap F.ρ' F.hρc F.hρpos)
  set y : singularChainGroup ℚ SpaceTop 3 →ₗ[ℚ] ℚ :=
    Y₁.comp (singularChainMap ℚ (thomMap F.ρ' F.hρc F.hρpos) 3).hom with hydef
  have hyZ : ∀ τ : SingularSimplex SpaceTop 3, IsSubordinate (tube F.ρ')ᶜ τ →
      y (chainGenerator ℚ SpaceTop 3 τ) = 0 := by
    rw [F.compl_tube_eq]; exact hy2
  have hfin := F.hfin_y y hyZ
  have hzS : ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3),
      ((cellCoinv W).d 3 2).hom z = 0 →
      (coinvariantChains principalSix SpaceTop W).d 3 2 ((cellCoinvMapS W).f 3 z) = 0 := by
    intro W z hz
    have h := ConcreteCategory.congr_hom ((cellCoinvMapS W).comm 3 2) z
    refine h.trans ?_
    change (cellCoinvMapS W).f 2 (((cellCoinv W).d 3 2) z) = 0
    rw [hz, map_zero]
  obtain ⟨K₁, hK₁, y₁, φ₁, φh₁, hy₁, hφ₁, hvt₁, hcap₁⟩ :=
    dual_data F (𝒞₁ ∪ 𝒞₂) hFD W₁ z₁ hz₁ h₁' (hzS W₁ z₁ hz₁)
  obtain ⟨K₂, hK₂, y₂, φ₂, φh₂, hy₂, hφ₂, hvt₂, hcap₂⟩ :=
    dual_data F (𝒞₁ ∪ 𝒞₂) hFD W₂ z₂ hz₂ h₂' (hzS W₂ z₂ hz₂)
  let Kfull : Compacts ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ :=
    K₁ ⊔ K₂ ⊔ ⟨F.Qs pS, F.Qs_compact pS⟩
  have hK₁le : K₁ ≤ Kfull := le_sup_of_le_left le_sup_left
  have hK₂le : K₂ ≤ Kfull := le_sup_of_le_left le_sup_right
  have hKfull : (Kfull : Set _) ⊆ F.D1 pS ∪ F.Qs pS := by
    intro b hb
    rcases hb with (hb | hb) | hb
    · exact Or.inl (hK₁ hb)
    · exact Or.inl (hK₂ hb)
    · exact Or.inr hb
  have hQK : F.Qs pS ⊆ (Kfull : Set _) := fun b hb => Or.inr hb
  obtain ⟨a, ha, hevalGen, hbdC, hdegh, hdeg⟩ := chart_chain_data_deg F Kfull hKfull hQK
  have hev₁ : (groupApartmentEvaluation W₁).hom ((cellGroupHomologyMap W₁ 3).hom (cellClass W₁ z₁ hz₁)) =
      chainDesc (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
        vertexToFunction pS pS_isQuotientCovering
          ((supportInclusion pS W₁
            (K₁ : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ₁.val)
          (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) a := by
    rw [ev_eq_ambient W₁ _ (openCompactImage_subset
      CompactInteriorRelativeBoundary.boundaryComplementOpen K₁) φh₁ z₁ hz₁ hcap₁]
    exact hevalGen W₁ K₁ hK₁le φ₁ φh₁ hvt₁
  have hev₂ : (groupApartmentEvaluation W₂).hom ((cellGroupHomologyMap W₂ 3).hom (cellClass W₂ z₂ hz₂)) =
      chainDesc (fun σ : SingularSimplex (TopCat.of ↥(F.UT pS)) 2 =>
        vertexToFunction pS pS_isQuotientCovering
          ((supportInclusion pS W₂
            (K₂ : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)).f 2 φ₂.val)
          (pushSimplex (F.sec pS pS_isQuotientCovering) 2 σ)) a := by
    rw [ev_eq_ambient W₂ _ (openCompactImage_subset
      CompactInteriorRelativeBoundary.boundaryComplementOpen K₂) φh₂ z₂ hz₂ hcap₂]
    exact hevalGen W₂ K₂ hK₂le φ₂ φh₂ hvt₂
  have haB := haB_of_ne F W₂ K₂ hK₂ φ₂ a (by rw [← hev₂]; exact hne)
  have hpB : IsLocalHomeomorph pS.hom := pS_isLocalHomeomorph
  obtain ⟨r, hr₁, hr₂, hval⟩ := bridge_core_value pS interiorEuclidean interiorOrientation (F.UT pS) (F.UB pS)
    (F.UT_open pS hp) (F.UB_open pS hp) y hy hfin hyZ (F.UB_pre pS)
    (F.sec pS hp) (F.sec_comp pS hp) (F.hone_y pS hp y hyZ) F.ε F.R0 F.δ F.hε F.hδ F.hδR
    (F.eY pS hp) a ha haB (F.Qs pS) (F.D1 pS) (F.Qs_compact pS) (F.image_slab_cov pS hp)
    (F.D1_cov pS hp) (F.hQ pS hp) (F.hD1 pS hp) W₁ W₂ ((cellCoinvMapS W₁).f 3 z₁)
    ((cellCoinvMapS W₂).f 3 z₂) (hzS W₁ z₁ hz₁) (hzS W₂ z₂ hz₂) K₁ K₂ hK₁ hK₂ y₁ y₂ hy₁ hy₂
    φ₁ φ₂ hφ₁ hφ₂ Y₁ Θ₁ T hη (thomMap F.ρ' F.hρc F.hρpos) hydef (frame_hgs F hp hηc)
    (frame_hBη F hp hηc) (F.eY_apply pS hp) hpB (interiorOrientation_generator_pS hpB)
    (frameTt F) Locality.p0 (frame_p0_mem F) (frame_hiso F hp) (frameHom F hp) (frame_hhom F hp)
    (frame_p0_Qs F) (frame_p0_notUB F) psi_p0
  have hτ : (Θ₁.comp (singularChainMap ℚ ((F.sec pS hp ≫ psiHom) ≫ rhoEHom ≫ scale2 F.δ⁻¹) 2).hom) a = lam2 := by
    obtain ⟨h', hθ⟩ := T.t_deg _ hbdC
    rw [LinearMap.comp_apply, hθ]
    exact hdeg
  refine ⟨r, _, ?_, ?_, hval, hτ⟩
  · rw [← Yco_cellSpan F y hfin hy2 hy3 (𝒞₁ ∪ 𝒞₂) hcells hD2 W₁ z₁ h₁', hr₁, hev₁]
  · rw [← Yco_cellSpan F y hfin hy2 hy3 (𝒞₁ ∪ 𝒞₂) hcells hD2 W₂ z₂ h₂', hr₂, hev₂]


end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
