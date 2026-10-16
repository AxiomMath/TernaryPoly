module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.DegreeHomotopyR2
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartValue

@[expose] public section


/-!
# Rescaling a pair of unit Thom cochains

Given Thom cochains `y₁` of `ℝ³` and `θ₁` of `ℝ²` of radius `1`, the cochains `y₁ ∘ (4·)_#` and `θ₁ ∘ (4·)_#` form a `ThomPair`
(Thom cochains of radius `1/4`).  The proof uses the homotopy invariance of the local degree under the dilation.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open CategoryTheory SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open TernaryPoly.EuclideanLocalHomology
open TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular

/-- Dilation of `ℝ³` by `s`. -/
def scale3 (s : ℝ) : TopCat.of R3 ⟶ TopCat.of R3 :=
  TopCat.ofHom ⟨fun v => s • v, by fun_prop⟩

/-- Dilation of `ℝ²` by `s`. -/
def scale2 (s : ℝ) : TopCat.of R2 ⟶ TopCat.of R2 :=
  TopCat.ofHom ⟨fun v => s • v, by fun_prop⟩

theorem scale3_apply (s : ℝ) (v : R3) : (scale3 s).hom v = s • v := rfl
theorem scale2_apply (s : ℝ) (v : R2) : (scale2 s).hom v = s • v := rfl

theorem preimage_scale3 : (scale3 4).hom ⁻¹' {v : R3 | 1 < ‖v‖} = {v : R3 | 1 / 4 < ‖v‖} := by
  ext v
  change 1 < ‖(4 : ℝ) • (v : R3)‖ ↔ 1 / 4 < ‖(v : R3)‖
  rw [norm_smul, Real.norm_ofNat]
  constructor <;> intro h <;> linarith

theorem preimage_scale2 : (scale2 4).hom ⁻¹' {v : R2 | 1 < ‖v‖} = {v : R2 | 1 / 4 < ‖v‖} := by
  ext v
  change 1 < ‖(4 : ℝ) • (v : R2)‖ ↔ 1 / 4 < ‖(v : R2)‖
  rw [norm_smul, Real.norm_ofNat]
  constructor <;> intro h <;> linarith

/-- The straight-line homotopy from the dilation by `4` to the identity of `ℝ³`. -/
def scaleHomotopy3 : ContinuousMap.Homotopy (scale3 4).hom (TopCat.ofHom (ContinuousMap.id R3)).hom where
  toFun p := ((4 : ℝ) - 3 * (p.1 : ℝ)) • (p.2 : R3)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change ((4 : ℝ) - 3 * ((0 : unitInterval) : ℝ)) • (x : R3) = (4 : ℝ) • (x : R3)
    simp
  map_one_left x := by
    change ((4 : ℝ) - 3 * ((1 : unitInterval) : ℝ)) • (x : R3) = (x : R3)
    simp; norm_num

/-- The straight-line homotopy from the dilation by `4` to the identity of `ℝ²`. -/
def scaleHomotopy2 : ContinuousMap.Homotopy (scale2 4).hom (TopCat.ofHom (ContinuousMap.id R2)).hom where
  toFun p := ((4 : ℝ) - 3 * (p.1 : ℝ)) • (p.2 : R2)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change ((4 : ℝ) - 3 * ((0 : unitInterval) : ℝ)) • (x : R2) = (4 : ℝ) • (x : R2)
    simp
  map_one_left x := by
    change ((4 : ℝ) - 3 * ((1 : unitInterval) : ℝ)) • (x : R2) = (x : R2)
    simp; norm_num

theorem degR3_congr (a b : singularChainGroup ℚ (TopCat.of R3) 3) (hab : a = b)
    (ha : ((localChains 3).d 3 2).hom ((locR3.f 3).hom a) = 0)
    (hb : ((localChains 3).d 3 2).hom ((locR3.f 3).hom b) = 0) : degR3 a ha = degR3 b hb := by
  subst hab; rfl

theorem degR2_congr (a b : singularChainGroup ℚ (TopCat.of R2) 2) (hab : a = b)
    (ha : ((localChains 2).d 2 1).hom ((locR2.f 2).hom a) = 0)
    (hb : ((localChains 2).d 2 1).hom ((locR2.f 2).hom b) = 0) : degR2 a ha = degR2 b hb := by
  subst hab; rfl

theorem degR3_scale4 (c : singularChainGroup ℚ (TopCat.of R3) 3)
    (hc : (singularBoundary ℚ (TopCat.of R3) 2).hom c ∈
      subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 / 4 < ‖v‖} 2) :
    ∃ (hf : ((localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ (scale3 4) 3).hom c)) = 0)
      (hg : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0),
      degR3 ((singularChainMap ℚ (scale3 4) 3).hom c) hf = degR3 c hg := by
  obtain ⟨hf, hg, h⟩ := degR3_homotopy (scale3 4) (TopCat.ofHom (ContinuousMap.id R3)) scaleHomotopy3
    {v : R3 | 1 / 4 < ‖v‖} (by
      intro t x hx
      have hx0 : (x : R3) ≠ 0 := by
        intro h0
        have : (1 / 4 : ℝ) < ‖(x : R3)‖ := hx
        rw [h0, norm_zero] at this
        linarith
      have ht : (4 : ℝ) - 3 * (t : ℝ) ≠ 0 := by
        have := t.2.2
        intro h0
        linarith
      change ((4 : ℝ) - 3 * (t : ℝ)) • (x : R3) ≠ 0
      exact smul_ne_zero ht hx0) c hc
  have e : (singularChainMap ℚ (TopCat.ofHom (ContinuousMap.id R3)) 3).hom c = c := by
    have := singularChainMap_id ℚ (TopCat.of R3) 3
    exact congrArg (fun F => F.hom c) this
  have hg' : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0 := by rw [← e]; exact hg
  exact ⟨hf, hg', h.trans (degR3_congr _ _ e _ _)⟩

theorem degR2_scale4 (c : singularChainGroup ℚ (TopCat.of R2) 2)
    (hc : (singularBoundary ℚ (TopCat.of R2) 1).hom c ∈
      subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 / 4 < ‖v‖} 1) :
    ∃ (hf : ((localChains 2).d 2 1).hom ((locR2.f 2).hom ((singularChainMap ℚ (scale2 4) 2).hom c)) = 0)
      (hg : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0),
      degR2 ((singularChainMap ℚ (scale2 4) 2).hom c) hf = degR2 c hg := by
  obtain ⟨hf, hg, h⟩ := degR2_homotopy (scale2 4) (TopCat.ofHom (ContinuousMap.id R2)) scaleHomotopy2
    {v : R2 | 1 / 4 < ‖v‖} (by
      intro t x hx
      have hx0 : (x : R2) ≠ 0 := by
        intro h0
        have : (1 / 4 : ℝ) < ‖(x : R2)‖ := hx
        rw [h0, norm_zero] at this
        linarith
      have ht : (4 : ℝ) - 3 * (t : ℝ) ≠ 0 := by
        have := t.2.2
        intro h0
        linarith
      change ((4 : ℝ) - 3 * (t : ℝ)) • (x : R2) ≠ 0
      exact smul_ne_zero ht hx0) c hc
  have e : (singularChainMap ℚ (TopCat.ofHom (ContinuousMap.id R2)) 2).hom c = c := by
    have := singularChainMap_id ℚ (TopCat.of R2) 2
    exact congrArg (fun F => F.hom c) this
  have hg' : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0 := by rw [← e]; exact hg
  exact ⟨hf, hg', h.trans (degR2_congr _ _ e _ _)⟩

/-- **Rescaling unit Thom cochains.**  If `y₁` and `θ₁` satisfy the Thom conditions of radius `1` (cocycle, vanishing off the
unit ball, local degree on chains with boundary off the unit ball), then `y₁ ∘ (4·)_#` and `θ₁ ∘ (4·)_#` form a `ThomPair`
(radius `1/4`). -/
theorem thomPair_scale (y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ)
    (hy₁d : ∀ e : (chains R3).X 4, y₁ (((chains R3).d 4 3).hom e) = 0)
    (hy₁v : ∀ τ : singularSimplices (TopCat.of R3) 3, IsSubordinate {v : R3 | 1 < ‖v‖} τ →
      y₁ (chainGenerator ℚ (TopCat.of R3) 3 τ) = 0)
    (hy₁c : ∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₁ c = degR3 c h)
    (hθ₁d : ∀ e : (chains R2).X 3, θ₁ (((chains R2).d 3 2).hom e) = 0)
    (hθ₁v : ∀ τ : singularSimplices (TopCat.of R2) 2, IsSubordinate {v : R2 | 1 < ‖v‖} τ →
      θ₁ (chainGenerator ℚ (TopCat.of R2) 2 τ) = 0)
    (hθ₁c : ∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
        subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 →
      ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₁ c = degR2 c h) :
    ThomPair (y₁.comp (singularChainMap ℚ (scale3 4) 3).hom) (θ₁.comp (singularChainMap ℚ (scale2 4) 2).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rw [LinearMap.comp_apply]
    have h1 := singularChainMap_boundary_apply ℚ (scale3 4) 3 e
    have h2 : (singularChainMap ℚ (scale3 4) 3).hom ((singularBoundary ℚ (TopCat.of R3) 3).hom e) =
        (singularBoundary ℚ (TopCat.of R3) 3).hom ((singularChainMap ℚ (scale3 4) 4).hom e) := h1.symm
    exact (congrArg y₁ h2).trans (hy₁d _)
  · intro τ hτ
    rw [LinearMap.comp_apply, singularChainMap_generator]
    apply hy₁v
    rw [isSubordinate_pushSimplex_iff, preimage_scale3]
    exact hτ
  · intro c hc
    have h1 := singularChainMap_boundary_apply ℚ (scale3 4) 2 c
    have hb : (singularBoundary ℚ (TopCat.of R3) 2).hom ((singularChainMap ℚ (scale3 4) 3).hom c) ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 := by
      have : (singularBoundary ℚ (TopCat.of R3) 2).hom ((singularChainMap ℚ (scale3 4) 3).hom c) =
          (singularChainMap ℚ (scale3 4) 2).hom ((singularBoundary ℚ (TopCat.of R3) 2).hom c) := h1
      rw [this]
      refine singularChainMap_mem_sub (scale3 4) {v : R3 | 1 < ‖v‖} 2 ?_
      rw [show (scale3 4).hom ⁻¹' {v : R3 | 1 < ‖v‖} = {v : R3 | 1 / 4 < ‖v‖} from preimage_scale3]
      exact hc
    obtain ⟨h', hy'⟩ := hy₁c _ hb
    obtain ⟨hf, hg, hdeg⟩ := degR3_scale4 c hc
    exact ⟨hg, by
      rw [LinearMap.comp_apply, hy']
      exact (degR3_congr _ _ rfl h' hf).trans hdeg⟩
  · intro e
    rw [LinearMap.comp_apply]
    have h1 := singularChainMap_boundary_apply ℚ (scale2 4) 2 e
    have h2 : (singularChainMap ℚ (scale2 4) 2).hom ((singularBoundary ℚ (TopCat.of R2) 2).hom e) =
        (singularBoundary ℚ (TopCat.of R2) 2).hom ((singularChainMap ℚ (scale2 4) 3).hom e) := h1.symm
    exact (congrArg θ₁ h2).trans (hθ₁d _)
  · intro τ hτ
    rw [LinearMap.comp_apply, singularChainMap_generator]
    apply hθ₁v
    rw [isSubordinate_pushSimplex_iff, preimage_scale2]
    exact hτ
  · intro c hc
    have h1 := singularChainMap_boundary_apply ℚ (scale2 4) 1 c
    have hb : (singularBoundary ℚ (TopCat.of R2) 1).hom ((singularChainMap ℚ (scale2 4) 2).hom c) ∈
        subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 := by
      have : (singularBoundary ℚ (TopCat.of R2) 1).hom ((singularChainMap ℚ (scale2 4) 2).hom c) =
          (singularChainMap ℚ (scale2 4) 1).hom ((singularBoundary ℚ (TopCat.of R2) 1).hom c) := h1
      rw [this]
      refine singularChainMap_mem_sub (scale2 4) {v : R2 | 1 < ‖v‖} 1 ?_
      rw [show (scale2 4).hom ⁻¹' {v : R2 | 1 < ‖v‖} = {v : R2 | 1 / 4 < ‖v‖} from preimage_scale2]
      exact hc
    obtain ⟨h', hy'⟩ := hθ₁c _ hb
    obtain ⟨hf, hg, hdeg⟩ := degR2_scale4 c hc
    exact ⟨hg, by
      rw [LinearMap.comp_apply, hy']
      exact (degR2_congr _ _ rfl h' hf).trans hdeg⟩

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
