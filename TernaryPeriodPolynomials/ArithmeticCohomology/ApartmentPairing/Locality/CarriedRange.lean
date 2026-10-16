module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Span
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.RestrictCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SpaceCover
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Support
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.MapS

@[expose] public section


/-!
# Lemma 3.3, G3: the cellular chain map restricted to a chain carried over an open set

`coinvariantSpaceMap_mk` : the space map acts on an elementary chain `[v ⊗ c]` by pushing the scalar chain.
`cellCoinvMapS_range`: if the carriers of the cells in a finite set `𝒞` lie over an open set `D1` of the base
of `pS`, the image under `cellCoinvMapS` of an element of `cellSpan W 𝒞` is the image of a chain of the
restricted covering over `D1` (so `dual_of_carried` applies to cycles).  The instances for the concrete
covering `pS` are stated here because instance resolution for the invariant subspaces does not see through the
concrete topological category.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SymmetricSpacePositive
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- The space map of a restriction acts on an elementary chain by pushing the scalar chain. -/
theorem coinvariantSpaceMap_mk {G : Type} [Group G] {E E' : TopCat.{0}}
    [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
    (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G) (n : ℕ) (v : V)
    (c : singularChainGroup ℚ E n) :
    (coinvariantSpaceMap F hF V).f n (Rep.coinvariantsTensorMk V (chainRep G E n) v c) =
      Rep.coinvariantsTensorMk V (chainRep G E' n) v ((singularChainMap ℚ F n).hom c) := by
  have h := SingularLocalHomology.tensorCoinvariant_map_mk V (chainRep G E n) (chainRep G E' n)
    ((chainMap F hF).f n) v c
  exact h

section Range

/-- The preimage under `pS` of a subset of the base is invariant (instance for the concrete covering). -/
instance pSPreimageInvariant (A : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) :
    Fact (TernaryPoly.EquivariantSingularSmall.InvariantSet principalSix SpaceTop (pS ⁻¹' A)) :=
  TernaryPoly.EquivariantSingularSmall.preimageInvariantFact pS A

instance pSPreimageAction (A : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) :
    MulAction principalSix (pS ⁻¹' A) :=
  TernaryPoly.EquivariantSingularSmall.invariantSubtypeAction principalSix SpaceTop (pS ⁻¹' A)

instance pSPreimageContinuous (A : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ) :
    ContinuousConstSMul principalSix (pS ⁻¹' A) :=
  TernaryPoly.EquivariantSingularSmall.invariantSubtypeContinuous principalSix SpaceTop (pS ⁻¹' A)

theorem cellCoinvMapS_range (D1 : Set ↥(SymmetricSpaceBordifiedQuotient.boundary principalSix)ᶜ)
    (𝒞 : Finset (Graded 3))
    (hC : ∀ C ∈ 𝒞, cellSet 3 C.1 ⊆ pS ⁻¹' D1) (W : Rep.{0} ℚ principalSix)
    (z : (cellCoinv W).X 3) (hz : z ∈ cellSpan W 𝒞) :
    (cellCoinvMapS W).f 3 z ∈ LinearMap.range ((coinvariantSpaceMap (sInclusion (pS ⁻¹' D1))
      (fun _ _ => rfl) W).f 3).hom := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, hCm, w, rfl⟩ := hx
    rw [cellCoinvMapS_mk]
    have hmem : cellAtSpace 3 C.1 ∈ subChainSubmodule ℚ SpaceTop (pS ⁻¹' D1) 3 :=
      subChainSubmodule_mono (hC C hCm) 3 (cellAtSpace_mem_sub 3 C.1)
    obtain ⟨c', hc'⟩ := (subChainCorestrict_bijective (R := ℚ) (pS ⁻¹' D1) 3).2 ⟨_, hmem⟩
    have hc'' : (singularChainMap ℚ (sInclusion (pS ⁻¹' D1)) 3).hom c' = cellAtSpace 3 C.1 :=
      congrArg Subtype.val hc'
    refine ⟨Rep.coinvariantsTensorMk W (chainRep principalSix (TopCat.of (pS ⁻¹' D1)) 3) w c', ?_⟩
    have h := coinvariantSpaceMap_mk (sInclusion (pS ⁻¹' D1)) (fun _ _ => rfl) W 3 w c'
    rw [hc''] at h
    exact h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end Range

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
