module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Thom
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BoxRank

@[expose] public section


/-!
# A Thom cochain on the singular chains of `ℝ²`

The planar analogue of `Locality.Thom`: for every `ε ≥ 0` there is a rational 2-cochain on the singular chains of `ℝ²`
that vanishes on boundaries and on simplices missing the ball of radius `ε`, and which computes the local degree
`H₂(ℝ², ℝ² ∖ 0) ≅ ℚ` (`localTopIso 0`) of every chain whose boundary misses the ball (`exists_thom_cochain2`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision TernaryPoly
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

/-- Singular chains of `ℝ²` modulo those of the punctured space. -/
def locR2 : chains R2 ⟶ localChains 2 := cokernel.π (inclusion (Punctured 2))

/-- The local degree of a 2-chain of `ℝ²` whose relative boundary vanishes. -/
def degR2 (c : (chains R2).X 2)
    (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0) : ℚ :=
  (localTopIso 0).hom.hom ((localChains 2).homologyπ 2 ((localChains 2).cyclesMk _ 1
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)) h))

theorem degR2_add (c c' : (chains R2).X 2)
    (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0)
    (h' : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c') = 0)
    (h'' : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (c + c')) = 0) :
    degR2 (c + c') h'' = degR2 c h + degR2 c' h' := by
  have hnext : (ComplexShape.down ℕ).next 2 = 1 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)
  have hl : (locR2.f 2).hom (c + c') = (locR2.f 2).hom c + (locR2.f 2).hom c' := map_add _ _ _
  have hxy : (forget₂ (ModuleCat.{0} ℚ) Ab).map ((localChains 2).d 2 1)
      ((locR2.f 2).hom c + (locR2.f 2).hom c') = 0 := by
    change ((localChains 2).d 2 1).hom ((locR2.f 2).hom c + (locR2.f 2).hom c') = 0
    rw [map_add, h, h', add_zero]
  have e := thomCyclesMk_add (localChains 2) ((locR2.f 2).hom c) ((locR2.f 2).hom c') hnext h h' hxy
  have e2 : (localChains 2).cyclesMk ((locR2.f 2).hom (c + c')) 1 hnext h'' =
      (localChains 2).cyclesMk ((locR2.f 2).hom c + (locR2.f 2).hom c') 1 hnext hxy :=
    thomCyclesMk_inj (localChains 2) _ _ 1 hnext h'' hxy hl
  unfold degR2
  rw [e2, e, map_add, map_add]

theorem degR2_eq_of_sub (c c' : (chains R2).X 2)
    (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0)
    (h' : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c') = 0)
    (x : (localChains 2).X 3)
    (hx : (locR2.f 2).hom c = (locR2.f 2).hom c' + ((localChains 2).d 3 2).hom x) :
    degR2 c h = degR2 c' h' := by
  unfold degR2
  congr 1
  exact thomHomologyπ_cyclesMk_eq (localChains 2) _ _ x _ _ _ hx

theorem degR2_zero (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom 0) = 0) : degR2 0 h = 0 := by
  have := degR2_add 0 0 h h (by simp)
  simpa using this

theorem locR2_sub_zero {U : Set R2} (hU : U ⊆ ({0}ᶜ : Set R2)) (n : ℕ)
    {c : (chains R2).X n} (hc : c ∈ subChainSubmodule ℚ (TopCat.of R2) U n) :
    (locR2.f n).hom c = 0 := by
  have hle : subChainSubmodule ℚ (TopCat.of R2) U n ≤
      LinearMap.ker ((locR2.f n).hom) := by
    rw [subChainSubmodule, Submodule.span_le]
    rintro _ ⟨σ, hσ, rfl⟩
    have hσ' : IsSubordinate (({0}ᶜ : Set R2)) σ := hσ.mono hU
    obtain ⟨τ, hτ⟩ := exists_pushSimplex_of_subordinate (X := TopCat.of R2) ({0}ᶜ : Set R2) n hσ'
    have hg := singularChainMap_generator ℚ (sInclusion ({0}ᶜ : Set (TopCat.of R2))) n τ
    rw [hτ] at hg
    have h1 : (locR2.f n).hom (((inclusion (Punctured 2)).f n).hom (chainGenerator ℚ _ n τ)) = 0 := by
      have := congrArg (fun m => m.hom (chainGenerator ℚ _ n τ))
        (congrArg (fun m => m.f n) (cokernel.condition (inclusion (Punctured 2))))
      exact this
    show (locR2.f n).hom _ = 0
    rw [← hg]
    exact h1
  exact hle hc

theorem locR2_cycle_of_boundary_mem {U : Set R2} (hU : U ⊆ ({0}ᶜ : Set R2))
    {c : (chains R2).X 2}
    (hc : ((chains R2).d 2 1).hom c ∈ subChainSubmodule ℚ (TopCat.of R2) U 1) :
    ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0 := by
  have hcomm := congrArg (fun m => m.hom c) (locR2.comm 2 1)
  change ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) =
    (locR2.f 1).hom (((chains R2).d 2 1).hom c) at hcomm
  rw [hcomm]
  exact locR2_sub_zero hU 1 hc

/-- **Thom cochain.** For `ε ≥ 0` there is a rational 2-cochain on the singular chains of `ℝ²`
that kills boundaries and simplices missing the `ε`-ball, and computes the local degree of every
chain whose boundary misses the `ε`-ball. -/
theorem exists_thom_cochain2 (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ y : (chains R2).X 2 →ₗ[ℚ] ℚ,
      (∀ e : (chains R2).X 3, y (((chains R2).d 3 2).hom e) = 0) ∧
      (∀ τ : singularSimplices (TopCat.of R2) 2, IsSubordinate {v : R2 | ε < ‖v‖} τ →
          y (chainGenerator ℚ (TopCat.of R2) 2 τ) = 0) ∧
      (∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
          subChainSubmodule ℚ (TopCat.of R2) {v : R2 | ε < ‖v‖} 1 →
        ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, y c = degR2 c h) := by
  set U : Set R2 := {v : R2 | ε < ‖v‖} with hUdef
  have hU : U ⊆ ({0}ᶜ : Set R2) := by
    intro v hv h0
    have : ε < ‖v‖ := hv
    rw [Set.mem_singleton_iff.mp h0, norm_zero] at this
    exact absurd this (not_lt.mpr hε)
  let Zrel : Submodule ℚ ((chains R2).X 2) :=
    Submodule.comap ((chains R2).d 2 1).hom (subChainSubmodule ℚ (TopCat.of R2) U 1)
  have hZ : ∀ c : Zrel, ((localChains 2).d 2 1).hom ((locR2.f 2).hom c.1) = 0 :=
    fun c => locR2_cycle_of_boundary_mem hU c.2
  let f0 : Zrel →+ ℚ :=
    AddMonoidHom.mk' (fun c => degR2 c.1 (hZ c)) (fun a b =>
      degR2_add a.1 b.1 (hZ a) (hZ b) (hZ (a + b)))
  obtain ⟨y, hy⟩ := LinearMap.exists_extend (f0.toRatLinearMap)
  have hyc : ∀ (c : (chains R2).X 2) (hc : c ∈ Zrel), y c = degR2 c (hZ ⟨c, hc⟩) := by
    intro c hc
    exact LinearMap.congr_fun hy ⟨c, hc⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · intro e
    have hmem : ((chains R2).d 3 2).hom e ∈ Zrel := by
      show ((chains R2).d 2 1).hom (((chains R2).d 3 2).hom e) ∈
        subChainSubmodule ℚ (TopCat.of R2) U 1
      have : ((chains R2).d 2 1).hom (((chains R2).d 3 2).hom e) = 0 := by
        rw [← ModuleCat.comp_apply, (chains R2).d_comp_d]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    rw [hyc _ hmem]
    have hl : (locR2.f 2).hom (((chains R2).d 3 2).hom e) =
        ((localChains 2).d 3 2).hom ((locR2.f 3).hom e) := by
      have := congrArg (fun m => m.hom e) (locR2.comm 3 2)
      exact this.symm
    have h0 : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (0 : (chains R2).X 2)) = 0 := by simp
    rw [degR2_eq_of_sub _ 0 (hZ ⟨_, hmem⟩) h0 ((locR2.f 3).hom e) (by rw [hl]; simp), degR2_zero]
  · intro τ hτ
    have hg : chainGenerator ℚ (TopCat.of R2) 2 τ ∈ subChainSubmodule ℚ (TopCat.of R2) U 2 :=
      chainGenerator_mem_subChainSubmodule hτ
    have hmem : chainGenerator ℚ (TopCat.of R2) 2 τ ∈ Zrel :=
      singularBoundary_maps_subChainSubmodule 1 _ hg
    rw [hyc _ hmem]
    have h0 : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (0 : (chains R2).X 2)) = 0 := by simp
    have hk := locR2_sub_zero hU 2 hg
    rw [degR2_eq_of_sub _ 0 (hZ ⟨_, hmem⟩) h0 0 (by rw [hk]; simp), degR2_zero]
  · intro c hc
    exact ⟨locR2_cycle_of_boundary_mem hU hc, hyc c hc⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
