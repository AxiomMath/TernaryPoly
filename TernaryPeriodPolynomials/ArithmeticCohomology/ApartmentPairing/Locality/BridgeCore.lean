module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.PDRep
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.LocalRelationBox

@[expose] public section


/-!
# Locality for Poincaré duality: the bridge core (two cycles, one scalar)

For a quotient covering `p : E ⟶ B` of an oriented five-manifold, a chart `UT` of the base with a section
`s` and a coordinate box structure `eY : UT ≃ₜ {‖u‖ < ε, ‖t‖ < R}`, and a scalar 3-cocycle `y` of `E`
supported (with all its translates) in a set `Z` that stays inside the chart, `bridge_core` shows: for
two coinvariant 3-cycles `z₁, z₂` (arbitrary coefficient representations `V₁, V₂`) whose compact-support
duals `y₁, y₂` live in a set `D₁` meeting the chart only in the slab `{‖t‖ ≤ δ}` and covered by the chart
and the complement `UB` of the support, there is a single scalar
`r` with `Yco V_i y z_i = r • φ̃_i(a)`, where `φ_i` are cocycle representatives of the duals and `φ̃_i(a)` is
the evaluation of the pulled-back cochain on a chart chain `a` that spans the relative `H₂` of the chart
modulo the slab.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.CoveringSingularOrbits
  TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

section Core

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (e : H ≃ₜ EuclideanSpace ℝ (Fin (3+2))) (o : Orientation (3+2) B)

/-- **Bridge core** (two cycles, one scalar). -/
theorem bridge_core
    (UT UB : Set B) (hUT : IsOpen UT) (hUB : IsOpen UB)
    (y : singularChainGroup ℚ E 3 →ₗ[ℚ] ℚ) (hy : ∀ e, y ((singularBoundary ℚ E 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex E 3, {g : G | y (chainGenerator ℚ E 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set E}
    (hyZ : ∀ τ : SingularSimplex E 3, IsSubordinate Zᶜ τ → y (chainGenerator ℚ E 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (s : TopCat.of UT ⟶ E) (hs : s ≫ p = sInclusion UT)
    (hone : ∀ (ρ : SingularSimplex (TopCat.of UT) 3) (g : G), g ≠ 1 →
      y (chainGenerator ℚ E 3 (g • pushSimplex s 3 ρ)) = 0)
    (ε R δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R)
    (eY : TopCat.of UT ≃ₜ boxSet ε R)
    (a : singularChainGroup ℚ (TopCat.of UT) 2)
    (ha : (singularBoundary ℚ (TopCat.of UT) 1).hom a ∈
      subChainSubmodule ℚ (TopCat.of UT) {u : UT | ‖((eY u : R3 × R2)).2‖ ≤ δ}ᶜ 1)
    (haB : a ∉ subChainSubmodule ℚ (TopCat.of UT) {u : UT | ‖((eY u : R3 × R2)).2‖ ≤ δ}ᶜ 2 ⊔
      LinearMap.range (singularBoundary ℚ (TopCat.of UT) 2).hom)
    (Q D₁ : Set B) (hQc : IsCompact Q) (hQcov : Q ⊆ UT ∪ UB) (hD₁cov : D₁ ⊆ UT ∪ UB)
    (hQ : ∀ u : UT, (u : B) ∈ Q ↔ ‖((eY u : R3 × R2)).2‖ ≤ δ)
    (hD₁ : ∀ b ∈ D₁, ∀ u : UT, (u : B) = b → ‖((eY u : R3 × R2)).2‖ ≤ δ)
    (V₁ V₂ : Rep.{0} ℚ G) (z₁ : (coinvariantChains G E V₁).X 3) (z₂ : (coinvariantChains G E V₂).X 3)
    (hz₁ : (coinvariantChains G E V₁).d 3 2 z₁ = 0) (hz₂ : (coinvariantChains G E V₂).d 3 2 z₂ = 0)
    (K₁ K₂ : Compacts B) (hK₁ : (K₁ : Set B) ⊆ D₁) (hK₂ : (K₂ : Set B) ⊆ D₁)
    (y₁ : (supportCochains p V₁ (K₁ : Set B)).homology 2)
    (y₂ : (supportCochains p V₂ (K₂ : Set B)).homology 2)
    (hy₁ : compactCapMap p V₁ 3 e o 2 3 rfl (compactClassMap p V₁ K₁ 2 y₁) =
      chainClass (localChains p hp.out V₁) 3
        (⟨degreeEquiv p hp.out V₁ 3 z₁, degreeEquiv_cycle p V₁ z₁ hz₁⟩ :
          Cycles ((localChains p hp.out V₁).sc' (3+1) 3 (3-1))))
    (hy₂ : compactCapMap p V₂ 3 e o 2 3 rfl (compactClassMap p V₂ K₂ 2 y₂) =
      chainClass (localChains p hp.out V₂) 3
        (⟨degreeEquiv p hp.out V₂ 3 z₂, degreeEquiv_cycle p V₂ z₂ hz₂⟩ :
          Cycles ((localChains p hp.out V₂).sc' (3+1) 3 (3-1))))
    (φ₁ : Cycles ((supportCochains p V₁ (K₁ : Set B)).sc' (2-1) 2 (2+1)))
    (φ₂ : Cycles ((supportCochains p V₂ (K₂ : Set B)).sc' (2-1) 2 (2+1)))
    (hφ₁ : cochainClass (supportCochains p V₁ (K₁ : Set B)) 2 φ₁ = y₁)
    (hφ₂ : cochainClass (supportCochains p V₂ (K₂ : Set B)) 2 φ₂ = y₂) :
    ∃ r : ℚ,
      Yco V₁ y hfin z₁ = r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
          vertexToFunction p hp.out ((supportInclusion p V₁ (K₁ : Set B)).f 2 φ₁.val)
            (pushSimplex s 2 σ)) a ∧
      Yco V₂ y hfin z₂ = r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
          vertexToFunction p hp.out ((supportInclusion p V₂ (K₂ : Set B)).f 2 φ₂.val)
            (pushSimplex s 2 σ)) a := by
  let K : Compacts B := K₁ ⊔ K₂ ⊔ ⟨Q, hQc⟩
  have hK₁K : K₁ ≤ K := le_sup_of_le_left le_sup_left
  have hK₂K : K₂ ≤ K := le_sup_of_le_left le_sup_right
  obtain ⟨c, hc, hcbd⟩ := exists_fundRep e o K
  obtain ⟨hφ₁d, hφ₁v, hrel₁⟩ := dual_of_rep p V₁ e o z₁ hz₁ K₁ y₁ hy₁ φ₁ hφ₁
  obtain ⟨hφ₂d, hφ₂v, hrel₂⟩ := dual_of_rep p V₂ e o z₂ hz₂ K₂ y₂ hy₂ φ₂ hφ₂
  have hW : (Subtype.val ⁻¹' (K : Set B)ᶜ : Set UT)ᶜ =
      {u : UT | ‖((eY u : R3 × R2)).2‖ ≤ δ} := by
    ext u
    constructor
    · intro hu
      have hu' : (u : B) ∈ (K : Set B) := by
        by_contra hnot
        exact hu hnot
      rcases hu' with (hu' | hu') | hu'
      · exact hD₁ _ (hK₁ hu') u rfl
      · exact hD₁ _ (hK₂ hu') u rfl
      · exact (hQ u).mp hu'
    · intro hu hnot
      exact hnot (Or.inr ((hQ u).mpr hu))
  have hWc : {u : UT | ‖((eY u : R3 × R2)).2‖ ≤ δ}ᶜ = Subtype.val ⁻¹' (K : Set B)ᶜ := by
    rw [← hW, compl_compl]
  have hKopen : IsOpen (K : Set B)ᶜ := K.isCompact.isClosed.isOpen_compl
  have hcov : UT ∪ (K : Set B)ᶜ ∪ UB = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    by_cases hbK : b ∈ (K : Set B)
    · have : b ∈ UT ∪ UB := by
        rcases hbK with (hb | hb) | hb
        · exact hD₁cov (hK₁ hb)
        · exact hD₁cov (hK₂ hb)
        · exact hQcov hb
      rcases this with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · exact Or.inl (Or.inr hbK)
  have ha' : (singularBoundary ℚ (TopCat.of UT) 1).hom a ∈
      subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' (K : Set B)ᶜ) 1 := by
    rw [← hWc]; exact ha
  have haB' : a ∉ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' (K : Set B)ᶜ) 2 ⊔
      LinearMap.range (singularBoundary ℚ (TopCat.of UT) 2).hom := by
    rw [← hWc]; exact haB
  obtain ⟨r, hr⟩ := local_relation_box p hp.out UT (K : Set B)ᶜ UB hUT hKopen hUB hcov y hy hfin
    hyZ hUBZ c hcbd s hs hone ε R δ hε hδ hδR eY hW a ha' haB'
  have hsub : ∀ {K' : Compacts B}, K' ≤ K → ∀ σ : SingularSimplex B 2,
      IsSubordinate (K : Set B)ᶜ σ → IsSubordinate (K' : Set B)ᶜ σ := by
    intro K' hK' σ hσ
    exact hσ.mono (Set.compl_subset_compl.mpr hK')
  refine ⟨r, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hrel₁ K hK₁K c hc
    rw [← Yco_eq_of_sub V₁ y hfin hy v hv.symm]
    exact hr V₁ _ hφ₁d (fun σ hσ => hφ₁v σ (hsub hK₁K σ hσ))
  · obtain ⟨v, hv⟩ := hrel₂ K hK₂K c hc
    rw [← Yco_eq_of_sub V₂ y hfin hy v hv.symm]
    exact hr V₂ _ hφ₂d (fun σ hσ => hφ₂v σ (hsub hK₂K σ hσ))

end Core

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
