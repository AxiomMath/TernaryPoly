module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize

@[expose] public section


/-!
# Localization of the translate-sum pairing, with the chain decomposition

`localize_pairing_dec` is `Locality.localize_pairing` (same proof) with the additional output of the chain decomposition
`c = (ι_# cY) + cA + cB + ∂u` (`cA` over `UA`, `cB` over `UB`) of the localized chain `cY`: it is what allows reading off the local
class of `cY` at a point of `UT` outside `UA` and `UB` from that of `c`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

section Cap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

theorem localize_pairing_dec
    (UT UA UB : Set B) (hUT : IsOpen UT) (hUA : IsOpen UA) (hUB : IsOpen UB)
    (hcov : UT ∪ UA ∪ UB = Set.univ)
    (y : singularChainGroup ℚ E 3 →ₗ[ℚ] ℚ) (hy : ∀ e, y ((singularBoundary ℚ E 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex E 3, {g : G | y (chainGenerator ℚ E 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set E}
    (hyZ : ∀ τ : SingularSimplex E 3, IsSubordinate Zᶜ τ → y (chainGenerator ℚ E 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (c : singularChainGroup ℚ B 5) (hc : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B UA 4)
    (s : TopCat.of UT ⟶ E) (hs : s ≫ p = sInclusion UT) :
    ∃ cY : singularChainGroup ℚ (TopCat.of UT) 5,
      (∃ cA ∈ subChainSubmodule ℚ B UA 5, ∃ cB ∈ subChainSubmodule ℚ B UB 5,
        ∃ u : singularChainGroup ℚ B 6,
          c = (singularChainMap ℚ (sInclusion UT) 5).hom cY + cA + cB + (singularBoundary ℚ B 5).hom u) ∧
      (∃ aY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 4,
       ∃ bY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UB) 4,
        (singularBoundary ℚ (TopCat.of UT) 4).hom cY = aY + bY) ∧
      ∀ (V : Rep.{0} ℚ G) (φ : VertexCochain p hp V 2) (_ : differential p hp V 2 φ = 0)
        (_ : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0),
      Yco V y hfin ((degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c)) =
        Yco V y hfin (capE V 2 3 (vertexToFunction p hp φ) ((singularChainMap ℚ s 5).hom cY)) := by
  obtain ⟨cT, hcT, cA, hcA, cB, hcB, u, hcd, a', ha', b', hb', hdcT⟩ :=
    localize_chain UT UA UB hUT hUA hUB hcov 4 c hc
  obtain ⟨cY, hcY⟩ := (subChainCorestrict_bijective (R := ℚ) UT 5).2 ⟨cT, hcT⟩
  have hcY' : (singularChainMap ℚ (sInclusion UT) 5).hom cY = cT := congrArg Subtype.val hcY
  have ha'T : a' ∈ subChainSubmodule ℚ B UT 4 :=
    subChainSubmodule_mono Set.inter_subset_left 4 ha'
  have hb'T : b' ∈ subChainSubmodule ℚ B UT 4 :=
    subChainSubmodule_mono Set.inter_subset_left 4 hb'
  have ha'A : a' ∈ subChainSubmodule ℚ B UA 4 :=
    subChainSubmodule_mono Set.inter_subset_right 4 ha'
  have hb'B : b' ∈ subChainSubmodule ℚ B UB 4 :=
    subChainSubmodule_mono Set.inter_subset_right 4 hb'
  obtain ⟨aY, haY⟩ := (subChainCorestrict_bijective (R := ℚ) UT 4).2 ⟨a', ha'T⟩
  obtain ⟨bY, hbY⟩ := (subChainCorestrict_bijective (R := ℚ) UT 4).2 ⟨b', hb'T⟩
  have haY' : (singularChainMap ℚ (sInclusion UT) 4).hom aY = a' := congrArg Subtype.val haY
  have hbY' : (singularChainMap ℚ (sInclusion UT) 4).hom bY = b' := congrArg Subtype.val hbY
  have hinj : Function.Injective (singularChainMap ℚ (sInclusion UT) 4).hom :=
    singularChainMap_injective_of_pushSimplex_injective _ _ (pushSimplex_sInclusion_injective UT 4)
  have hbd : (singularBoundary ℚ (TopCat.of UT) 4).hom cY = aY + bY := by
    apply hinj
    have h1 := singularChainMap_boundary_apply ℚ (sInclusion UT) 4 cY
    rw [map_add, haY', hbY', ← hdcT, ← hcY']
    exact h1.symm
  have hmA : aY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 4 :=
    mem_sub_of_inclusion_mem UT UA 4 aY (by rw [haY']; exact ha'A)
  have hmB : bY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UB) 4 :=
    mem_sub_of_inclusion_mem UT UB 4 bY (by rw [hbY']; exact hb'B)
  refine ⟨cY, ⟨cA, hcA, cB, hcB, u, by rw [hcY']; exact hcd⟩, ⟨aY, hmA, bY, hmB, hbd⟩, ?_⟩
  intro V φ hφd hφA
  have hcap : (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c) =
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cT) +
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cA) +
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cB) +
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ ((singularBoundary ℚ B 5).hom u)) := by
    rw [hcd]
    simp only [map_add]
  have hA0 : cap p hp V 2 3 φ cA = 0 := cap_eq_zero_of_front p hp V 2 3 φ hφA hcA
  have hB0 := Yco_cap_eq_zero_of_back p hp V 2 3 φ y hfin hyZ hUBZ hcB
  have hu0 := Yco_cap_boundary p hp V 2 3 φ hφd y hy hfin u
  have hT := capE_pushforward p hp V s (sInclusion UT) hs 2 3 φ cY
  have hT' : capE V 2 3 (vertexToFunction p hp φ) ((singularChainMap ℚ s 5).hom cY) =
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cT) := by
    rw [← hcY']; exact hT
  rw [hcap, map_add, map_add, map_add, hA0, map_zero, map_zero, hB0, hu0, hT']
  simp


end Cap

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
