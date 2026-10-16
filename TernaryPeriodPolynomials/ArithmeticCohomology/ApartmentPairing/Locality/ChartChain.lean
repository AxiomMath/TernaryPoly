module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Loc
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ECap
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.HomEvaluation
public import TernaryPeriodPolynomials.Topology.SingularHomology.IteratedSubdivisionSmallChains

@[expose] public section


/-!
# Lemma 3.3, G3: the chart chain of a chain carried by the chart box

For the chart `UT = p(T̃)` of a `FrameOut`, `chartHom` is the section followed by the upstairs inclusion into the
bordification, a homeomorphism `chartHomeo` onto the image of the chart box.  A bordification chain carried by
that image comes from a chart chain (`exists_chart_chain`), the boundary of a chart chain is carried by the
preimage of any set carrying the boundary of its image (`chart_boundary_mem_sub`), and the ambient cochain of a
cocycle takes on the image of a chart chain the value of the pulled-back geometric cochain on the chart
chain (`ambientCochain_chart_chain`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.SymmetricSpacePositive TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.EquivariantSingularCohomology
  TernaryPoly.SingularCoverNaturality TernaryPoly.SymmetricSpaceBordifiedCohomology
  SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33

section Chart

variable {B : TopCat.{0}} (p : SpaceTop ⟶ B) (hp : IsQuotientCoveringMap p principalSix)
  (F : FrameOut)

include hp

/-- The chart of the base into the bordification: the section followed by the upstairs inclusion. -/
def FrameOut.chartHom : TopCat.of ↥(F.UT p) ⟶ TopCat.of Glued := F.sec p hp ≫ upstairs

/-- The homeomorphism of the chart onto the image of the chart box in the bordification. -/
def FrameOut.chartHomeo : ↥(F.UT p) ≃ₜ ↥(embedding '' F.Tt) :=
  (F.eT p hp).symm.trans (embedding_isOpenEmbedding.isEmbedding.homeomorphImage F.Tt)

theorem FrameOut.chartHomeo_val (u : ↥(F.UT p)) :
    ((F.chartHomeo p hp u : ↥(embedding '' F.Tt)) : Glued) = embedding ((F.sec p hp).hom u) := rfl

theorem FrameOut.chartHom_eq :
    F.chartHom p hp = TopCat.ofHom ⟨F.chartHomeo p hp, (F.chartHomeo p hp).continuous⟩ ≫
      sInclusion (embedding '' F.Tt) := rfl

/-- A chain carried by the image of the chart box comes from a chain of the chart. -/
theorem FrameOut.exists_chart_chain (FT : singularChainGroup ℚ (TopCat.of Glued) 2)
    (hFT : FT ∈ subChainSubmodule ℚ (TopCat.of Glued) (embedding '' F.Tt) 2) :
    ∃ a : singularChainGroup ℚ (TopCat.of ↥(F.UT p)) 2,
      (singularChainMap ℚ (F.chartHom p hp) 2).hom a = FT := by
  obtain ⟨y, hy⟩ := (subChainCorestrict_bijective (R := ℚ) (embedding '' F.Tt) 2).2 ⟨FT, hFT⟩
  have hy' : (singularChainMap ℚ (sInclusion (embedding '' F.Tt)) 2).hom y = FT := congrArg Subtype.val hy
  let χ : TopCat.of ↥(F.UT p) ⟶ TopCat.of ↥(embedding '' F.Tt) :=
    TopCat.ofHom ⟨F.chartHomeo p hp, (F.chartHomeo p hp).continuous⟩
  let χi : TopCat.of ↥(embedding '' F.Tt) ⟶ TopCat.of ↥(F.UT p) :=
    TopCat.ofHom ⟨(F.chartHomeo p hp).symm, (F.chartHomeo p hp).symm.continuous⟩
  have hχ : χi ≫ χ = 𝟙 _ := by
    ext x; exact congrArg Subtype.val ((F.chartHomeo p hp).apply_symm_apply x)
  refine ⟨(singularChainMap ℚ χi 2).hom y, ?_⟩
  have h1 : F.chartHom p hp = χ ≫ sInclusion (embedding '' F.Tt) := rfl
  rw [h1, singularChainMap_comp]
  have h2 : singularChainMap ℚ χi 2 ≫ singularChainMap ℚ χ 2 = 𝟙 _ := by
    rw [← singularChainMap_comp, hχ, singularChainMap_id]
  have h3 : (singularChainMap ℚ χ 2).hom ((singularChainMap ℚ χi 2).hom y) = y :=
    congrArg (fun m => m.hom y) h2
  change (singularChainMap ℚ (sInclusion (embedding '' F.Tt)) 2).hom
    ((singularChainMap ℚ χ 2).hom ((singularChainMap ℚ χi 2).hom y)) = FT
  rw [h3]
  exact hy'

/-- The boundary of the chart chain is carried by the preimage of any set carrying the boundary. -/
theorem FrameOut.chart_boundary_mem_sub (a : singularChainGroup ℚ (TopCat.of ↥(F.UT p)) 2)
    (S : Set (TopCat.of Glued))
    (hb : (singularBoundary ℚ (TopCat.of Glued) 1).hom
      ((singularChainMap ℚ (F.chartHom p hp) 2).hom a) ∈ subChainSubmodule ℚ (TopCat.of Glued) S 1) :
    (singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a ∈
      subChainSubmodule ℚ (TopCat.of ↥(F.UT p)) ((F.chartHom p hp).hom ⁻¹' S) 1 := by
  let χ : TopCat.of ↥(F.UT p) ⟶ TopCat.of ↥(embedding '' F.Tt) :=
    TopCat.ofHom ⟨F.chartHomeo p hp, (F.chartHomeo p hp).continuous⟩
  let χi : TopCat.of ↥(embedding '' F.Tt) ⟶ TopCat.of ↥(F.UT p) :=
    TopCat.ofHom ⟨(F.chartHomeo p hp).symm, (F.chartHomeo p hp).symm.continuous⟩
  have hχ : χ ≫ χi = 𝟙 _ := by
    ext x; exact congrArg Subtype.val ((F.chartHomeo p hp).symm_apply_apply x)
  have h1 : F.chartHom p hp = χ ≫ sInclusion (embedding '' F.Tt) := rfl
  have hbd : (singularBoundary ℚ (TopCat.of Glued) 1).hom
      ((singularChainMap ℚ (F.chartHom p hp) 2).hom a) =
      (singularChainMap ℚ (F.chartHom p hp) 1).hom
        ((singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a) :=
    singularChainMap_boundary_apply ℚ (F.chartHom p hp) 1 a
  rw [hbd, h1, singularChainMap_comp] at hb
  have hb' : (singularChainMap ℚ (sInclusion (embedding '' F.Tt)) 1).hom
      ((singularChainMap ℚ χ 1).hom ((singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a)) ∈
      subChainSubmodule ℚ (TopCat.of Glued) S 1 := hb
  have h2 := mem_sub_of_inclusion_mem (embedding '' F.Tt) S 1 _ hb'
  have hset : χi.hom ⁻¹' (χ.hom ⁻¹' (Subtype.val ⁻¹' S)) = Subtype.val ⁻¹' S := by
    ext t
    have : χ.hom (χi.hom t) = t := (F.chartHomeo p hp).apply_symm_apply t
    simp only [Set.mem_preimage]
    rw [this]
  have h2' : (singularChainMap ℚ χ 1).hom ((singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a) ∈
      subChainSubmodule ℚ (TopCat.of ↥(embedding '' F.Tt))
        (χi.hom ⁻¹' (χ.hom ⁻¹' (Subtype.val ⁻¹' S))) 1 := by
    rw [hset]; exact h2
  have h3 := singularChainMap_mem_sub χi (χ.hom ⁻¹' (Subtype.val ⁻¹' S)) 1 h2'
  have h4 : (singularChainMap ℚ χi 1).hom ((singularChainMap ℚ χ 1).hom
      ((singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a)) =
      (singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a := by
    have : singularChainMap ℚ χ 1 ≫ singularChainMap ℚ χi 1 = 𝟙 _ := by
      rw [← singularChainMap_comp, hχ, singularChainMap_id]
    exact congrArg (fun m => m.hom ((singularBoundary ℚ (TopCat.of ↥(F.UT p)) 1).hom a)) this
  rw [h4] at h3
  exact h3

omit hp in
/-- The ambient cochain evaluated on the image of a chart chain is the pulled-back geometric cochain
evaluated on the chart chain. -/
theorem ambientCochain_chart_chain (W : Rep.{0} ℚ principalSix) (K : Compacts BordifiedOrbit)
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    {Y : TopCat.{0}} (ψ : Y ⟶ TopCat.of Glued) (a : singularChainGroup ℚ Y 2) :
    (ambientCochain W K φh).hom ((singularChainMap ℚ ψ 2).hom a) =
      chainDesc (fun σ : SingularSimplex Y 2 =>
        vertexToFunction wholeProjection wholeQuotientCovering
          ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val)
          (pushSimplex ψ 2 σ)) a := by
  have hadd : ∀ x y : singularChainGroup ℚ (TopCat.of Glued) 2,
      (ambientCochain W K φh).hom (x + y) =
        (ambientCochain W K φh).hom x + (ambientCochain W K φh).hom y :=
    fun x y => map_add (ambientCochain W K φh).hom.toLinearMap x y
  have hsmul : ∀ (r : ℚ) (x : singularChainGroup ℚ (TopCat.of Glued) 2),
      (ambientCochain W K φh).hom (r • x) = r • (ambientCochain W K φh).hom x :=
    fun r x => map_smul (ambientCochain W K φh).hom.toLinearMap r x
  have hzero : (ambientCochain W K φh).hom (0 : singularChainGroup ℚ (TopCat.of Glued) 2) = 0 :=
    map_zero (ambientCochain W K φh).hom.toLinearMap
  have ha : a ∈ Submodule.span ℚ (Set.range (chainGenerator ℚ Y 2)) := by
    rw [chainGenerator_span_top]; trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, rfl⟩ := hx
    rw [chainDesc_generator, singularChainMap_generator]
    exact ambientCochain_eval_generator W K φh (pushSimplex ψ 2 σ)
  | zero => rw [map_zero, hzero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hadd, hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hsmul, hx]

end Chart

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
