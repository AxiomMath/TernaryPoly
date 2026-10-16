module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.LocalRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BoxRank

@[expose] public section


/-!
# Locality for Poincaré duality: the local relation on a product chart

`local_relation_box` is `local_relation` with the spanning hypothesis discharged by the rank-one theorem
`box_rank_one` for the coordinate box: if the chart `UT` is homeomorphic to the box
`{‖u‖ < ε, ‖t‖ < R}` so that the complement of the support `UA` in the chart is the slab `{‖t‖ ≤ δ}`, and
the chart chain `a` is a relative cycle that is not a relative boundary, the relation
`Yco V y (cap φ c) = r • φ̃(a)` holds with a scalar `r` independent of `V` and `φ`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

section Box

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

/-- `hspan` of the local relation from the rank-one theorem of the box. -/
theorem hspan_of_box {UT UA : Set B} (ε R δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R)
    (e : TopCat.of UT ≃ₜ boxSet ε R)
    (hW : (Subtype.val ⁻¹' UA : Set UT)ᶜ = {u | ‖((e u : R3 × R2)).2‖ ≤ δ})
    (a : singularChainGroup ℚ (TopCat.of UT) 2)
    (ha : (singularBoundary ℚ (TopCat.of UT) 1).hom a ∈
      subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 1)
    (haB : a ∉ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 2 ⊔
      LinearMap.range (singularBoundary ℚ (TopCat.of UT) 2).hom) :
    ∀ z : singularChainGroup ℚ (TopCat.of UT) 2,
      (singularBoundary ℚ (TopCat.of UT) 1).hom z ∈
        subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 1 →
      ∃ (q : ℚ) (f : singularChainGroup ℚ (TopCat.of UT) 3),
        z - q • a - (singularBoundary ℚ (TopCat.of UT) 2).hom f ∈
          subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 2 := by
  intro z hz
  set Wset : Set (TopCat.of UT) := (Subtype.val ⁻¹' UA)ᶜ with hWdef
  have hWc : Wsetᶜ = Subtype.val ⁻¹' UA := by rw [hWdef, compl_compl]
  obtain ⟨q, hq⟩ := box_rank_one ε R δ hε hδ hδR (TopCat.of UT) e Wset hW a z
    (by rw [hWc]; exact ha) (by rw [hWc]; exact hz) (by rw [hWc]; exact haB)
  rw [hWc] at hq
  obtain ⟨s, hs, w, ⟨f, rfl⟩, hsw⟩ := Submodule.mem_sup.mp hq
  refine ⟨q, f, ?_⟩
  have : z - q • a - (singularBoundary ℚ (TopCat.of UT) 2).hom f = s := by
    rw [← hsw]; abel
  rw [this]; exact hs

/-- **The local relation on a product chart.** -/
theorem local_relation_box
    (UT UA UB : Set B) (hUT : IsOpen UT) (hUA : IsOpen UA) (hUB : IsOpen UB)
    (hcov : UT ∪ UA ∪ UB = Set.univ)
    (y : singularChainGroup ℚ E 3 →ₗ[ℚ] ℚ) (hy : ∀ e, y ((singularBoundary ℚ E 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex E 3, {g : G | y (chainGenerator ℚ E 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set E}
    (hyZ : ∀ τ : SingularSimplex E 3, IsSubordinate Zᶜ τ → y (chainGenerator ℚ E 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (c : singularChainGroup ℚ B 5) (hc : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B UA 4)
    (s : TopCat.of UT ⟶ E) (hs : s ≫ p = sInclusion UT)
    (hone : ∀ (ρ : SingularSimplex (TopCat.of UT) 3) (g : G), g ≠ 1 →
      y (chainGenerator ℚ E 3 (g • pushSimplex s 3 ρ)) = 0)
    (ε R δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδR : δ < R)
    (e : TopCat.of UT ≃ₜ boxSet ε R)
    (hW : (Subtype.val ⁻¹' UA : Set UT)ᶜ = {u | ‖((e u : R3 × R2)).2‖ ≤ δ})
    (a : singularChainGroup ℚ (TopCat.of UT) 2)
    (ha : (singularBoundary ℚ (TopCat.of UT) 1).hom a ∈
      subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 1)
    (haB : a ∉ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 2 ⊔
      LinearMap.range (singularBoundary ℚ (TopCat.of UT) 2).hom) :
    ∃ r : ℚ, ∀ (V : Rep.{0} ℚ G) (φ : VertexCochain p hp V 2) (_ : differential p hp V 2 φ = 0)
      (_ : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0),
      Yco V y hfin ((degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c)) =
        r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
          vertexToFunction p hp φ (pushSimplex s 2 σ)) a :=
  local_relation p hp UT UA UB hUT hUA hUB hcov y hy hfin hyZ hUBZ c hc s hs hone a
    (hspan_of_box ε R δ hε hδ hδR e hW a ha haB)

end Box

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
