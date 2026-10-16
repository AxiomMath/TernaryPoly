module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize

@[expose] public section


/-!
# Locality for Poincaré duality: the local relation

Combines `localize_pairing` (cap of a relative cycle, localized to a chart `UT` with a section `s`),
`Yco_capE_pushforward` (the translate-sum pairing of a section chain is the plain pairing on the chart)
and the cross relation (`CrossRelation.cross_relation`, which needs that the relative `H₂` of the pair
(chart, chart minus the support) is spanned by one class `a`).

`local_relation`: there is a scalar `r`, depending only on the cap-localized chain and on `y`, `a`, such
that for every coefficient representation `V` and every cocycle `φ` vanishing off the support,
`Yco V y (cap φ c) = r • φ̃(a)`, where `φ̃ = φ ∘ s_*`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

section LocalRelation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

theorem pushSimplex_face {Y E : TopCat.{0}} (s : Y ⟶ E) (n : ℕ) (i : Fin (n+2))
    (ρ : SingularSimplex Y (n+1)) :
    pushSimplex s n (faceSimplex Y n i ρ) = faceSimplex E n i (pushSimplex s (n+1) ρ) :=
  (ConcreteCategory.congr_hom ((TopCat.toSSet.map s).naturality (SimplexCategory.δ i).op) ρ)

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
theorem vertexToFunction_zero (V : Rep.{0} ℚ G) (n : ℕ) (τ : SingularSimplex E n) :
    vertexToFunction p hp (0 : VertexCochain p hp V n) τ = 0 := rfl

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
/-- The pulled-back cochain on a chart is a cocycle when `φ` is. -/
theorem cochainY_cocycle (V : Rep.{0} ℚ G) {Y : TopCat.{0}} (s : Y ⟶ E)
    (φ : VertexCochain p hp V 2) (hφd : differential p hp V 2 φ = 0)
    (e : singularChainGroup ℚ Y 3) :
    (chainDesc fun σ : SingularSimplex Y 2 => vertexToFunction p hp φ (pushSimplex s 2 σ))
      ((singularBoundary ℚ Y 2).hom e) = 0 := by
  have h : ((chainDesc fun σ : SingularSimplex Y 2 =>
      vertexToFunction p hp φ (pushSimplex s 2 σ)).comp (singularBoundary ℚ Y 2).hom) = 0 := by
    apply chainDesc_ext
    intro ρ
    rw [LinearMap.comp_apply, scalarBoundary_generator, map_sum]
    simp only [map_zsmul, chainDesc_generator, pushSimplex_face]
    have := differential_vertexToFunction p hp V 2 φ (pushSimplex s 3 ρ)
    rw [hφd, vertexToFunction_zero] at this
    exact this.symm
  exact LinearMap.congr_fun h e

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
/-- A cochain vanishing on `A`-subordinate simplices of the base pulls back to a cochain on the chart
that vanishes on the chart simplices subordinate to the preimage of `A`. -/
theorem cochainY_vanish (V : Rep.{0} ℚ G) {UT : Set B} (s : TopCat.of UT ⟶ E)
    (hs : s ≫ p = sInclusion UT) (φ : VertexCochain p hp V 2) {UA : Set B}
    (hφA : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0)
    (τ : SingularSimplex (TopCat.of UT) 2) (hτ : IsSubordinate (Subtype.val ⁻¹' UA) τ) :
    vertexToFunction p hp φ (pushSimplex s 2 τ) = 0 := by
  have h1 : projection p 2 (pushSimplex s 2 τ) = pushSimplex (sInclusion UT) 2 τ := by
    rw [← hs]
    exact projection_pushSimplex p s 2 τ
  have h2 : IsSubordinate UA (pushSimplex (sInclusion UT) 2 τ) :=
    (isSubordinate_pushSimplex_iff _ _ _).mpr hτ
  have h3 : φ (projection p 2 (pushSimplex s 2 τ)) = 0 := by
    rw [h1]; exact hφA _ h2
  change (φ (projection p 2 (pushSimplex s 2 τ))).val ⟨atVertex (pushSimplex s 2 τ), rfl⟩ = 0
  rw [h3]
  rfl

/-- **The local relation.**  Let `UT, UA, UB` be an open cover of the base with a section `s` of the
covering over `UT`, `y` a cocycle of `E` supported where `Z` is and (with its translates) away from the
preimage of `UB`, `a` a chain of the chart `UT` such that the relative `H₂` of the chart modulo the
`UA`-chains is spanned by `a` (`hspan`).  For a relative cycle `c` (boundary over `UA`) there is a scalar
`r` such that for every representation `V` and every cocycle `φ` supported off `UA`,
`Yco V y (cap φ c) = r • φ̃(a)`, where `φ̃ = φ ∘ s_*` is the pulled-back cochain of the chart. -/
theorem local_relation
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
    (a : singularChainGroup ℚ (TopCat.of UT) 2)
    (hspan : ∀ z : singularChainGroup ℚ (TopCat.of UT) 2,
      (singularBoundary ℚ (TopCat.of UT) 1).hom z ∈
        subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 1 →
      ∃ (q : ℚ) (f : singularChainGroup ℚ (TopCat.of UT) 3),
        z - q • a - (singularBoundary ℚ (TopCat.of UT) 2).hom f ∈
          subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 2) :
    ∃ r : ℚ, ∀ (V : Rep.{0} ℚ G) (φ : VertexCochain p hp V 2) (_ : differential p hp V 2 φ = 0)
      (_ : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0),
      Yco V y hfin ((degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c)) =
        r • (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
          vertexToFunction p hp φ (pushSimplex s 2 σ)) a := by
  obtain ⟨cY, ⟨aY, haY, bY, hbY, hbd⟩, hid⟩ :=
    localize_pairing p hp UT UA UB hUT hUA hUB hcov y hy hfin hyZ hUBZ c hc s hs
  set Wset : Set (TopCat.of UT) := (Subtype.val ⁻¹' UA)ᶜ with hW
  set Zs : Set (TopCat.of UT) := s ⁻¹' Z with hZs
  have hWc : Wsetᶜ = Subtype.val ⁻¹' UA := by rw [hW, compl_compl]
  have hps : ∀ u : UT, p (s u) = (u : B) := by
    intro u
    have h := ConcreteCategory.congr_hom hs u
    exact h
  have hZB : (Subtype.val ⁻¹' UB : Set (TopCat.of UT)) ⊆ Zsᶜ := by
    intro u hu hz
    have : p (s u) ∈ UB := by rw [hps]; exact hu
    exact hUBZ this hz
  have hy' : ∀ e, (y.comp (singularChainMap ℚ s 3).hom)
      ((singularBoundary ℚ (TopCat.of UT) 3).hom e) = 0 := by
    intro e
    rw [LinearMap.comp_apply]
    have h1 := singularChainMap_boundary_apply ℚ s 3 e
    have h2 : (singularChainMap ℚ s 3).hom ((singularBoundary ℚ (TopCat.of UT) 3).hom e) =
        (singularBoundary ℚ E 3).hom ((singularChainMap ℚ s 4).hom e) := h1.symm
    rw [h2]; exact hy _
  have hyv : ∀ τ : SingularSimplex (TopCat.of UT) 3, IsSubordinate Zsᶜ τ →
      (y.comp (singularChainMap ℚ s 3).hom) (chainGenerator ℚ (TopCat.of UT) 3 τ) = 0 := by
    intro τ hτ
    rw [LinearMap.comp_apply, singularChainMap_generator]
    apply hyZ
    rw [isSubordinate_pushSimplex_iff]
    exact hτ
  have hcc : (singularBoundary ℚ (TopCat.of UT) 4).hom cY ∈
      subChainSubmodule ℚ (TopCat.of UT) Wsetᶜ 4 ⊔ subChainSubmodule ℚ (TopCat.of UT) Zsᶜ 4 := by
    rw [hbd, hWc]
    exact Submodule.add_mem_sup haY (subChainSubmodule_mono hZB 4 hbY)
  obtain ⟨r, hr⟩ := cross_relation (TopCat.of UT) Wset Zs (y.comp (singularChainMap ℚ s 3).hom)
    hy' hyv a cY hcc (by rw [hWc]; exact hspan)
  refine ⟨r, ?_⟩
  intro V φ hφd hφA
  rw [hid V φ hφd hφA, Yco_capE_pushforward V s (vertexToFunction p hp φ) y hfin hone cY]
  apply hr (ModuleCat.of ℚ V) (chainDesc fun σ : SingularSimplex (TopCat.of UT) 2 =>
      vertexToFunction p hp φ (pushSimplex s 2 σ))
  · intro τ hτ
    rw [chainDesc_generator]
    rw [hWc] at hτ
    exact cochainY_vanish p hp V s hs φ hφA τ hτ
  · exact fun e => cochainY_cocycle p hp V s φ hφd e

end LocalRelation

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
