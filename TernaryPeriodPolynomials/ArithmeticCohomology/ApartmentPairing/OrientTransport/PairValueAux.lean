module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.BridgeValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.InteriorGenerator
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FrameConst
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ThomY

@[expose] public section


/-!
# Auxiliary facts for the value of the bridge scalar

Facts about a frame `F` whose tube radius is the constant `η` on the chart box, used to instantiate `bridge_core_value`:
the Thom map on the chart is `η⁻¹ π`, the chart section meets the translates of the tube only in `{‖π‖ ≤ η}`, the base point
`p₀` lies in the slab image and in the tube, and `psi p₀ = 0`.  Also `exists_unitThom` and `thom_pullback_of`, the explicit
form of the Thom pullback cochain.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open CategoryTheory TopologicalSpace TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.RationalLocalMap
  TernaryPoly.SymmetricSpaceBordifiedCohomology
  TernaryPoly.RationalSingularAugmentation TernaryPoly.ContractibleSingularHomology
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalRelativeSingular
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

/-- Existence of a pair of unit Thom cochains of `ℝ³` and `ℝ²`. -/
theorem exists_unitThom : ∃ (y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ), UnitThom y₁ θ₁ := by
  obtain ⟨y₁, h1, h2, h3⟩ := exists_thom_cochain 1 zero_le_one
  obtain ⟨θ₁, k1, k2, k3⟩ := exists_thom_cochain2 1 zero_le_one
  exact ⟨y₁, θ₁, ⟨h1, h2, h3, k1, k2, k3⟩⟩

/-- **The Thom cochain along a map to `ℝ³`, in explicit form** (the three properties of `exists_thom_pullback`). -/
theorem thom_pullback_of {y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ} {θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ} (T : UnitThom y₁ θ₁)
    {E : TopCat.{0}} (g : E ⟶ TopCat.of R3) :
    (∀ e : singularChainGroup ℚ E 4,
      (y₁.comp (singularChainMap ℚ g 3).hom) ((singularBoundary ℚ E 3).hom e) = 0) ∧
    (∀ τ : SingularSimplex E 3, IsSubordinate {s : E | 1 < ‖g s‖} τ →
      (y₁.comp (singularChainMap ℚ g 3).hom) (chainGenerator ℚ E 3 τ) = 0) ∧
    (∀ c : singularChainGroup ℚ E 3,
      (singularBoundary ℚ E 2).hom c ∈ subChainSubmodule ℚ E {s : E | 1 < ‖g s‖} 2 →
      ∃ h : ((EuclideanLocalHomology.localChains 3).d 3 2).hom ((locR3.f 3).hom ((singularChainMap ℚ g 3).hom c)) = 0,
        (y₁.comp (singularChainMap ℚ g 3).hom) c = degR3 ((singularChainMap ℚ g 3).hom c) h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    rw [LinearMap.comp_apply]
    have h1 := singularChainMap_boundary_apply ℚ g 3 e
    have h2 : (singularChainMap ℚ g 3).hom ((singularBoundary ℚ E 3).hom e) =
        (singularBoundary ℚ (TopCat.of R3) 3).hom ((singularChainMap ℚ g 4).hom e) := h1.symm
    rw [h2]
    exact T.y_cocycle _
  · intro τ hτ
    rw [LinearMap.comp_apply, singularChainMap_generator]
    apply T.y_vanish
    rw [isSubordinate_pushSimplex_iff]
    exact hτ
  · intro c hc
    have h1 := singularChainMap_boundary_apply ℚ g 2 c
    have hb : (singularBoundary ℚ (TopCat.of R3) 2).hom ((singularChainMap ℚ g 3).hom c) ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 := by
      have : (singularBoundary ℚ (TopCat.of R3) 2).hom ((singularChainMap ℚ g 3).hom c) =
          (singularChainMap ℚ g 2).hom ((singularBoundary ℚ E 2).hom c) := h1
      rw [this]
      exact singularChainMap_mem_sub g {v : R3 | 1 < ‖v‖} 2 hc
    exact T.y_deg _ hb

theorem prodE_eq (q : R3 × R2) : (prodE q : EuclideanSpace ℝ (Fin 5)) = prodEL q := rfl

theorem piE_psi (S : Space) : piE (psi S) = piR3 S := by
  have : psi S = prodEL (coordHomeo S) := rfl
  rw [this, piE_prodEL]
  rfl

theorem rhoE_psi (S : Space) : rhoE (psi S) = (coordHomeo S).2 := by
  have : psi S = prodEL (coordHomeo S) := rfl
  rw [this, rhoE_prodEL]

theorem psi_p0 : psi Locality.p0 = 0 := by
  have h : psi Locality.p0 = prodEL (coordHomeo Locality.p0) := rfl
  rw [h, coordHomeo_p0]
  exact map_zero _


section FrameFacts

variable (F : FrameOut) (hp : IsQuotientCoveringMap pS principalSix)

/-- The chart box as an open subset of the symmetric space. -/
def frameTt : Opens Space := ⟨F.Tt, F.Tt_open⟩

theorem frame_p0_mem : Locality.p0 ∈ frameTt F := p0_mem_boxO F.hε (F.hδ.trans F.hδR)

include hp in
theorem frame_hiso : IsolatesFiber pS.hom Locality.p0 (frameTt F) := fun _ hz he =>
  F.Tt_injOn pS hp hz (frame_p0_mem F) he

/-- The corestriction of the section to the chart box. -/
def frameHom : TopCat.of ↥(F.UT pS) ⟶ TopCat.of ↥(frameTt F) :=
  TopCat.ofHom ⟨fun u => ⟨(F.sec pS hp).hom u, F.sec_mem pS hp u⟩,
    ((F.sec pS hp).hom.continuous).subtype_mk _⟩

theorem frame_hhom : frameHom F hp ≫ TtInc (frameTt F) = F.sec pS hp := rfl

theorem frame_p0_Qs : pS.hom Locality.p0 ∈ F.Qs pS := by
  refine ⟨Locality.p0, ?_, rfl⟩
  show coordHomeo Locality.p0 ∈ (Metric.closedBall (0 : R3) F.ε ×ˢ Metric.closedBall (0 : R2) F.δ)
  rw [coordHomeo_p0]
  exact ⟨Metric.mem_closedBall_self F.hε.le, Metric.mem_closedBall_self F.hδ.le⟩

theorem frame_p0_notUB : pS.hom Locality.p0 ∉ F.UB pS := by
  intro h
  apply h
  refine ⟨Locality.p0, ?_, rfl⟩
  show ‖piR3 Locality.p0‖ ≤ F.ρ' Locality.p0
  have : piR3 Locality.p0 = 0 := Locality.p0_mem_flat
  rw [this, norm_zero]
  exact (F.hρpos _).le

theorem frame_hgs {η : ℝ} (hηc : ∀ S ∈ boxC F.ε F.R0, F.ρ' S = η) (u : ↥(F.UT pS)) :
    (thomMap F.ρ' F.hρc F.hρpos).hom ((F.sec pS hp).hom u) = η⁻¹ • piE (psi ((F.sec pS hp).hom u)) := by
  rw [thomMap_apply, hηc _ (F.Tt_sub (F.sec_mem pS hp u)), piE_psi]

theorem frame_hBη {η : ℝ} (hηc : ∀ S ∈ boxC F.ε F.R0, F.ρ' S = η) (u : ↥(F.UT pS)) (hu : (u : ↥(boundary principalSix)ᶜ) ∈ F.UB pS) :
    η < ‖piE (psi ((F.sec pS hp).hom u))‖ := by
  rw [piE_psi]
  by_contra hle
  push Not at hle
  apply hu
  refine ⟨(F.sec pS hp).hom u, ?_, F.p_sec pS hp u⟩
  show ‖piR3 _‖ ≤ F.ρ' _
  rw [hηc _ (F.Tt_sub (F.sec_mem pS hp u))]
  exact hle

end FrameFacts

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
