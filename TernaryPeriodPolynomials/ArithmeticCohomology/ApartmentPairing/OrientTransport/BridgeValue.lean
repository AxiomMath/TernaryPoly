module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.RelationValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FundRepPoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeCore

@[expose] public section


/-!
# The bridge core with the value of the scalar

`bridge_core_value` is `Locality.bridge_core` (same proof) with the call to `local_relation_box` replaced by
`local_relation_box_value`: besides the two relations `Yco V_i y z_i = r • φ̃_i(a)` it returns
`d₅ · r · θ_X(a) = lamPos · lam2` for the pulled-back Thom cochain `θ_X = Θ₁ ∘ (δ⁻¹ ρ (s ≫ psi))_#` of the chart.  The extra hypotheses
are the Thom data, the chart geometry in the product coordinates and the orientation data (`o` is the pushforward of the
library orientation of the symmetric space along the covering `p`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly TernaryPoly.RationalManifoldCompact
  TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactDuality TernaryPoly.RationalLocalOrientation
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.CoveringSingularOrbits
  TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularResolution
  TernaryPoly.RationalLocalMap TernaryPoly.RationalSingularAugmentation TernaryPoly.ContractibleSingularHomology
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open TernaryPoly.SymmetricSpacePositive TernaryPoly.EuclideanLocalHomology

local notation "SpT" => TopCat.of Space

section Core

variable {G : Type} [Group G] [MulAction G SpT] [ContinuousConstSMul G SpT]
  [IsCancelSMul G SpT] {B : TopCat.{0}} (p : SpT ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (e : H ≃ₜ EuclideanSpace ℝ (Fin (3+2))) (o : Orientation (3+2) B)

/-- **Bridge core** (two cycles, one scalar). -/
theorem bridge_core_value
    (UT UB : Set B) (hUT : IsOpen UT) (hUB : IsOpen UB)
    (y : singularChainGroup ℚ SpT 3 →ₗ[ℚ] ℚ) (hy : ∀ e, y ((singularBoundary ℚ SpT 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex SpT 3, {g : G | y (chainGenerator ℚ SpT 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set SpT}
    (hyZ : ∀ τ : SingularSimplex SpT 3, IsSubordinate Zᶜ τ → y (chainGenerator ℚ SpT 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (s : TopCat.of UT ⟶ SpT) (hs : s ≫ p = sInclusion UT)
    (hone : ∀ (ρ : SingularSimplex (TopCat.of UT) 3) (g : G), g ≠ 1 →
      y (chainGenerator ℚ SpT 3 (g • pushSimplex s 3 ρ)) = 0)
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
    (V₁ V₂ : Rep.{0} ℚ G) (z₁ : (coinvariantChains G SpT V₁).X 3) (z₂ : (coinvariantChains G SpT V₂).X 3)
    (hz₁ : (coinvariantChains G SpT V₁).d 3 2 z₁ = 0) (hz₂ : (coinvariantChains G SpT V₂).d 3 2 z₂ = 0)
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
    (hφ₂ : cochainClass (supportCochains p V₂ (K₂ : Set B)) 2 φ₂ = y₂)
    -- the value data: Thom cochains, chart geometry, orientation
    (Y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (Θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ) (T : UnitThom Y₁ Θ₁)
    {η : ℝ} (hη : 0 < η)
    (g : SpT ⟶ TopCat.of R3) (hyform : y = Y₁.comp (singularChainMap ℚ g 3).hom)
    (hgs : ∀ u : UT, g.hom (s.hom u) = η⁻¹ • piE (psi (s.hom u)))
    (hBη : ∀ u : UT, (u : B) ∈ UB → η < ‖piE (psi (s.hom u))‖)
    (he : ∀ u : UT, ((eY u : boxSet ε R) : R3 × R2) = coordHomeo (s.hom u))
    (hpB : IsLocalHomeomorph p.hom)
    (hgen : ∀ S : Space, o.generator (p.hom S) =
      localHomeomorphMap p.hom hpB S 5 (SymmetricSpaceLocalOrientation.localGenerator S))
    (Tt : Opens Space) (p0 : Space) (hp0 : p0 ∈ Tt) (hiso : IsolatesFiber p.hom p0 Tt)
    (hom : TopCat.of UT ⟶ TopCat.of Tt) (hhom : hom ≫ TtInc Tt = s)
    (hb0Q : p.hom p0 ∈ Q) (hb0B : p.hom p0 ∉ UB) (hpsi0 : psi p0 = 0) :
    ∃ r : ℚ,
      Yco V₁ y hfin z₁ = r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
          vertexToFunction p hp.out ((supportInclusion p V₁ (K₁ : Set B)).f 2 φ₁.val)
            (pushSimplex s 2 σ)) a ∧
      Yco V₂ y hfin z₂ = r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
          vertexToFunction p hp.out ((supportInclusion p V₂ (K₂ : Set B)).f 2 φ₂.val)
            (pushSimplex s 2 σ)) a ∧
      d5 * r * (Θ₁.comp (singularChainMap ℚ ((s ≫ psiHom) ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom) a =
        lamPos * lam2 := by
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
  have hb0K : p.hom p0 ∈ (K : Set B) := Or.inr hb0Q
  have hb0A : p.hom p0 ∉ (K : Set B)ᶜ := fun h => h hb0K
  have hKp : (K : Set B)ᶜ ⊆ ({p.hom p0}ᶜ : Set B) := by
    intro z hz hz0
    apply hz
    rw [Set.mem_singleton_iff.mp hz0]
    exact hb0K
  have hcb : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B ({p.hom p0}ᶜ : Set B) 4 :=
    subChainSubmodule_mono hKp 4 hcbd
  have hc0 := fundRep_pointClass e o K c hc (p.hom p0) hb0K hcb
  obtain ⟨r, hr, hval⟩ := local_relation_box_value p hp.out UT (K : Set B)ᶜ UB hUT hKopen hUB hcov y hy
    hfin hyZ hUBZ c hcbd s hs hone ε R δ hε hδ hδR eY hW he a ha' haB' Y₁ Θ₁ T hη g hyform hgs hBη
    hpB o.generator hgen Tt p0 hp0 hiso hom hhom hb0A hb0B hpsi0 hcb hc0
  have hsub : ∀ {K' : Compacts B}, K' ≤ K → ∀ σ : SingularSimplex B 2,
      IsSubordinate (K : Set B)ᶜ σ → IsSubordinate (K' : Set B)ᶜ σ := by
    intro K' hK' σ hσ
    exact hσ.mono (Set.compl_subset_compl.mpr hK')
  refine ⟨r, ?_, ?_, hval⟩
  · obtain ⟨v, hv⟩ := hrel₁ K hK₁K c hc
    rw [← Yco_eq_of_sub V₁ y hfin hy v hv.symm]
    exact hr V₁ _ hφ₁d (fun σ hσ => hφ₁v σ (hsub hK₁K σ hσ))
  · obtain ⟨v, hv⟩ := hrel₂ K hK₂K c hc
    rw [← Yco_eq_of_sub V₂ y hfin hy v hv.symm]
    exact hr V₂ _ hφ₂d (fun σ hσ => hφ₂v σ (hsub hK₂K σ hσ))


end Core

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
