module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVRelativeLocalization
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.Homology
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubordinateChains
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubChainSubspaceBridge

@[expose] public section


/-!
# A Thom cochain on the singular chains of `ℝ³`

For every `ε ≥ 0` there is a rational 3-cochain `y` on the singular chains of `ℝ³` which
vanishes on boundaries and on simplices missing the ball of radius `ε`, and which computes the local
degree `H₃(ℝ³, ℝ³ ∖ 0) ≅ ℚ` of every chain whose boundary misses the ball (`exists_thom_cochain`).
The cochain is a `ℚ`-linear extension of the local degree, which is defined on the subspace of
chains whose boundary lies over `{ε < ‖v‖}`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision TernaryPoly
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

/-- Three-dimensional Euclidean space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Singular chains of `ℝ³` modulo those of the punctured space. -/
def locR3 : chains R3 ⟶ localChains 3 := cokernel.π (inclusion (Punctured 3))

/-- The local degree of a 3-chain of `ℝ³` whose relative boundary vanishes. -/
def degR3 (c : (chains R3).X 3)
    (h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0) : ℚ :=
  (localTopIso 1).hom.hom ((localChains 3).homologyπ 3 ((localChains 3).cyclesMk _ 2
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)) h))

theorem thomCyclesMk_inj (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) {i : ℕ}
    (x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X i)) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (hx hy) (h : x = y) :
    K.cyclesMk x j hj hx = K.cyclesMk y j hj hy := by
  subst h
  rfl

theorem thomHomologyπ_cyclesMk_eq (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) {i j : ℕ}
    (x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X j))
    (z : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X i))
    (hj : (ComplexShape.down ℕ).next j = j - 1) (hx hy)
    (h : x = y + (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.d i j) z) :
    (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ j) (K.cyclesMk x (j - 1) hj hx) =
      (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ j) (K.cyclesMk y (j - 1) hj hy) := by
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.iCycles j)) :=
    (Preadditive.mono_iff_injective (K.iCycles j)).1 inferInstance
  have e : K.cyclesMk x (j - 1) hj hx = K.cyclesMk y (j - 1) hj hy +
      (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.toCycles i j) z := by
    apply inj
    rw [map_add, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk,
      ← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_i, h]
  rw [e, map_add]
  have : (forget₂ (ModuleCat.{0} ℚ) Ab).map (K.homologyπ j)
      ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.toCycles i j) z) = 0 := by
    rw [← ConcreteCategory.forget₂_comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    simp
  rw [this, add_zero]

theorem thomCyclesMk_add (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) {j : ℕ}
    (x y : (forget₂ (ModuleCat.{0} ℚ) Ab).obj (K.X j))
    (hj : (ComplexShape.down ℕ).next j = j - 1) (hx hy hxy) :
    K.cyclesMk (x + y) (j - 1) hj hxy = K.cyclesMk x (j - 1) hj hx + K.cyclesMk y (j - 1) hj hy := by
  have inj : Function.Injective ((forget₂ (ModuleCat.{0} ℚ) Ab).map (K.iCycles j)) :=
    (Preadditive.mono_iff_injective (K.iCycles j)).1 inferInstance
  apply inj
  rw [map_add, HomologicalComplex.i_cyclesMk, HomologicalComplex.i_cyclesMk,
    HomologicalComplex.i_cyclesMk]

theorem degR3_add (c c' : (chains R3).X 3)
    (h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0)
    (h' : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c') = 0)
    (h'' : ((localChains 3).d 3 2).hom ((locR3.f 3).hom (c + c')) = 0) :
    degR3 (c + c') h'' = degR3 c h + degR3 c' h' := by
  have hnext : (ComplexShape.down ℕ).next 3 = 2 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 3 2 from rfl)
  have hl : (locR3.f 3).hom (c + c') = (locR3.f 3).hom c + (locR3.f 3).hom c' := map_add _ _ _
  have hxy : (forget₂ (ModuleCat.{0} ℚ) Ab).map ((localChains 3).d 3 2)
      ((locR3.f 3).hom c + (locR3.f 3).hom c') = 0 := by
    change ((localChains 3).d 3 2).hom ((locR3.f 3).hom c + (locR3.f 3).hom c') = 0
    rw [map_add, h, h', add_zero]
  have e := thomCyclesMk_add (localChains 3) ((locR3.f 3).hom c) ((locR3.f 3).hom c') hnext h h' hxy
  have e2 : (localChains 3).cyclesMk ((locR3.f 3).hom (c + c')) 2 hnext h'' =
      (localChains 3).cyclesMk ((locR3.f 3).hom c + (locR3.f 3).hom c') 2 hnext hxy :=
    thomCyclesMk_inj (localChains 3) _ _ 2 hnext h'' hxy hl
  unfold degR3
  rw [e2, e, map_add, map_add]

theorem degR3_eq_of_sub (c c' : (chains R3).X 3)
    (h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0)
    (h' : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c') = 0)
    (x : (localChains 3).X 4)
    (hx : (locR3.f 3).hom c = (locR3.f 3).hom c' + ((localChains 3).d 4 3).hom x) :
    degR3 c h = degR3 c' h' := by
  unfold degR3
  congr 1
  exact thomHomologyπ_cyclesMk_eq (localChains 3) _ _ x _ _ _ hx

theorem degR3_zero (h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom 0) = 0) : degR3 0 h = 0 := by
  have := degR3_add 0 0 h h (by simp)
  simpa using this

theorem locR3_sub_zero {U : Set R3} (hU : U ⊆ ({0}ᶜ : Set R3)) (n : ℕ)
    {c : (chains R3).X n} (hc : c ∈ subChainSubmodule ℚ (TopCat.of R3) U n) :
    (locR3.f n).hom c = 0 := by
  have hle : subChainSubmodule ℚ (TopCat.of R3) U n ≤
      LinearMap.ker ((locR3.f n).hom) := by
    rw [subChainSubmodule, Submodule.span_le]
    rintro _ ⟨σ, hσ, rfl⟩
    have hσ' : IsSubordinate (({0}ᶜ : Set R3)) σ := hσ.mono hU
    obtain ⟨τ, hτ⟩ := exists_pushSimplex_of_subordinate (X := TopCat.of R3) ({0}ᶜ : Set R3) n hσ'
    have hg := singularChainMap_generator ℚ (sInclusion ({0}ᶜ : Set (TopCat.of R3))) n τ
    rw [hτ] at hg
    have h1 : (locR3.f n).hom (((inclusion (Punctured 3)).f n).hom (chainGenerator ℚ _ n τ)) = 0 := by
      have := congrArg (fun m => m.hom (chainGenerator ℚ _ n τ))
        (congrArg (fun m => m.f n) (cokernel.condition (inclusion (Punctured 3))))
      exact this
    show (locR3.f n).hom _ = 0
    rw [← hg]
    exact h1
  exact hle hc

theorem locR3_cycle_of_boundary_mem {U : Set R3} (hU : U ⊆ ({0}ᶜ : Set R3))
    {c : (chains R3).X 3}
    (hc : ((chains R3).d 3 2).hom c ∈ subChainSubmodule ℚ (TopCat.of R3) U 2) :
    ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0 := by
  have hcomm := congrArg (fun m => m.hom c) (locR3.comm 3 2)
  change ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) =
    (locR3.f 2).hom (((chains R3).d 3 2).hom c) at hcomm
  rw [hcomm]
  exact locR3_sub_zero hU 2 hc

/-- **Thom cochain.** For `ε ≥ 0` there is a rational 3-cochain on the singular chains of `ℝ³`
that kills boundaries and simplices missing the `ε`-ball, and computes the local degree of every
chain whose boundary misses the `ε`-ball. -/
theorem exists_thom_cochain (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ y : (chains R3).X 3 →ₗ[ℚ] ℚ,
      (∀ e : (chains R3).X 4, y (((chains R3).d 4 3).hom e) = 0) ∧
      (∀ τ : singularSimplices (TopCat.of R3) 3, IsSubordinate {v : R3 | ε < ‖v‖} τ →
          y (chainGenerator ℚ (TopCat.of R3) 3 τ) = 0) ∧
      (∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
          subChainSubmodule ℚ (TopCat.of R3) {v : R3 | ε < ‖v‖} 2 →
        ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y c = degR3 c h) := by
  set U : Set R3 := {v : R3 | ε < ‖v‖} with hUdef
  have hU : U ⊆ ({0}ᶜ : Set R3) := by
    intro v hv h0
    have : ε < ‖v‖ := hv
    rw [Set.mem_singleton_iff.mp h0, norm_zero] at this
    exact absurd this (not_lt.mpr hε)
  let Zrel : Submodule ℚ ((chains R3).X 3) :=
    Submodule.comap ((chains R3).d 3 2).hom (subChainSubmodule ℚ (TopCat.of R3) U 2)
  have hZ : ∀ c : Zrel, ((localChains 3).d 3 2).hom ((locR3.f 3).hom c.1) = 0 :=
    fun c => locR3_cycle_of_boundary_mem hU c.2
  let f0 : Zrel →+ ℚ :=
    AddMonoidHom.mk' (fun c => degR3 c.1 (hZ c)) (fun a b =>
      degR3_add a.1 b.1 (hZ a) (hZ b) (hZ (a + b)))
  obtain ⟨y, hy⟩ := LinearMap.exists_extend (f0.toRatLinearMap)
  have hyc : ∀ (c : (chains R3).X 3) (hc : c ∈ Zrel), y c = degR3 c (hZ ⟨c, hc⟩) := by
    intro c hc
    exact LinearMap.congr_fun hy ⟨c, hc⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · intro e
    have hmem : ((chains R3).d 4 3).hom e ∈ Zrel := by
      show ((chains R3).d 3 2).hom (((chains R3).d 4 3).hom e) ∈
        subChainSubmodule ℚ (TopCat.of R3) U 2
      have : ((chains R3).d 3 2).hom (((chains R3).d 4 3).hom e) = 0 := by
        rw [← ModuleCat.comp_apply, (chains R3).d_comp_d]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    rw [hyc _ hmem]
    have hl : (locR3.f 3).hom (((chains R3).d 4 3).hom e) =
        ((localChains 3).d 4 3).hom ((locR3.f 4).hom e) := by
      have := congrArg (fun m => m.hom e) (locR3.comm 4 3)
      exact this.symm
    have h0 : ((localChains 3).d 3 2).hom ((locR3.f 3).hom (0 : (chains R3).X 3)) = 0 := by simp
    rw [degR3_eq_of_sub _ 0 (hZ ⟨_, hmem⟩) h0 ((locR3.f 4).hom e) (by rw [hl]; simp), degR3_zero]
  · intro τ hτ
    have hg : chainGenerator ℚ (TopCat.of R3) 3 τ ∈ subChainSubmodule ℚ (TopCat.of R3) U 3 :=
      chainGenerator_mem_subChainSubmodule hτ
    have hmem : chainGenerator ℚ (TopCat.of R3) 3 τ ∈ Zrel :=
      singularBoundary_maps_subChainSubmodule 2 _ hg
    rw [hyc _ hmem]
    have h0 : ((localChains 3).d 3 2).hom ((locR3.f 3).hom (0 : (chains R3).X 3)) = 0 := by simp
    have hk := locR3_sub_zero hU 3 hg
    rw [degR3_eq_of_sub _ 0 (hZ ⟨_, hmem⟩) h0 0 (by rw [hk]; simp), degR3_zero]
  · intro c hc
    exact ⟨locR3_cycle_of_boundary_mem hU hc, hyc c hc⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
