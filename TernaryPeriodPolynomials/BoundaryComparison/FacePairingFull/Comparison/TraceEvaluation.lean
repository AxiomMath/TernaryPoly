module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.KernelProperty
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.TraceNonvanishing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.GeoEval
public import TernaryPeriodPolynomials.Topology.TopHomology.FundamentalTie

@[expose] public section


/-!
# The whole-boundary trace comparison

Assembly of the D3 chain: the level boundary trace `levelTrace` is a nonzero multiple of the evaluation
`evalOmega Ω` on the finite rational chain `Ω = cornerChain v` of a spanning cycle `v` of the model cone
(`traceComparison`).  Proof: the kernel of this evaluation consists of boundary-exact cochains
(`KernelProperty.boundaryExactAt_of_cornerChain`, then `LevelAveraging.boundaryExactAt_of_N6`), on which the
trace vanishes (`TraceQuotient.levelTrace_eq_zero_of_boundaryExactAt`), so the two functionals are
proportional (`exists_smul_of_ker_le`); the constant is nonzero because the trace is nonzero
(`TraceNonvanishing.exists_closed_levelTrace_ne_zero`).  The tie to the boundary fundamental class is
`FundamentalTie.fundamental_tie` for the homotopy equivalence `coneEquiv` between the model cone and
the library's stabilizer cone, whose top cohomology is evaluated by `GeoEval.geoIso`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

/-- Two linear functionals with `ker ev ≤ ker τ` are proportional. -/
theorem exists_smul_of_ker_le {M : Type*} [AddCommGroup M] [Module ℂ M] (τ ev : M →ₗ[ℂ] ℂ)
    (h : ∀ m, ev m = 0 → τ m = 0) : ∃ c : ℂ, ∀ m, τ m = c * ev m := by
  by_cases hev : ∀ m, ev m = 0
  · exact ⟨0, fun m => by rw [h m (hev m), hev m, mul_zero]⟩
  · push Not at hev
    obtain ⟨m₀, hm₀⟩ := hev
    refine ⟨τ m₀ / ev m₀, fun m => ?_⟩
    have h1 : ev (m - (ev m / ev m₀) • m₀) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hm₀, sub_self]
    have h2 := h _ h1
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
    rw [h2]
    field_simp

theorem closedEdgeCochains_mono {N S : Subgroup RationalGL3} (hNS : N ≤ S) :
    closedEdgeCochains S ≤ closedEdgeCochains N := fun _ hf =>
  ⟨cochains_mono _ hNS 3 hf.1, hf.2⟩

/-- The homotopy equivalence between the model cone and the stabilizer cone. -/
def coneEquiv : _root_.HomotopyEquiv coneR stabilizerFaceCone := Classical.choose exists_coneEquiv

theorem coneCocycle_trivialMap_closed (r : ℂ →ₗ[ℚ] ℚ) (f : closedEdgeCochains N6) :
    coneR.d 5 4 ≫ coneCocycle f ≫ trivialMap r = 0 := by
  rw [← Category.assoc, coneCocycle_closed, zero_comp]

/-- The `ℚ`-valued cocycle of the stabilizer cone attached to the `r`-component of a closed edge
three-cochain, and its geometric evaluation on the boundary fundamental class. -/
def modelClass (r : ℂ →ₗ[ℚ] ℚ) (f : closedEdgeCochains N6) : ℚ :=
  cocycleClass (stabilizerTotalCochains trivialW) geoIso (coneEquiv.inv.f 4 ≫ coneCocycle f ≫ trivialMap r)
    (inv_comp_cocycle coneEquiv _ (coneCocycle_trivialMap_closed r f))

/-- **The trace comparison.** -/
theorem traceComparison :
    ∃ (Ω : MonoidAlgebra ℚ ((Fin 4 → RationalGL3) × Flag)) (c : ℂ) (κ : ℚ),
      c ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : closedEdgeCochains rationalLevel, levelTrace f = c * evalOmega Ω f.1) ∧
      (∀ f : closedEdgeCochains rationalLevel, evalOmega Ω f.1 = 0 → BoundaryExactAt rationalLevel f.1) ∧
      (∀ (r : ℂ →ₗ[ℚ] ℚ) (f : closedEdgeCochains N6), modelClass r f = κ * r (evalOmega Ω f.1)) := by
  obtain ⟨ω, hω0, hcyc, hspan⟩ := exists_fundamental_cycle coneR coneR_H4
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ ω
  obtain ⟨κ, hκ, htie⟩ := fundamental_tie coneEquiv geoIso
    (Representation.Coinvariants.mk (coneR.X 4).ρ v) hcyc
  let ev : closedEdgeCochains rationalLevel →ₗ[ℂ] ℂ :=
    (evalOmega (cornerChain v)).comp (closedEdgeCochains rationalLevel).subtype
  have hexact : ∀ f : closedEdgeCochains rationalLevel, evalOmega (cornerChain v) f.1 = 0 →
      BoundaryExactAt rationalLevel f.1 := by
    intro f hf
    have hN6 : f.val ∈ closedEdgeCochains N6 := closedEdgeCochains_mono N6_le_rationalLevel f.2
    exact boundaryExactAt_of_N6 f.2 (boundaryExactAt_of_cornerChain v hspan ⟨f.val, hN6⟩ hf)
  have hker : ∀ f : closedEdgeCochains rationalLevel, ev f = 0 → levelTrace f = 0 :=
    fun f hf => levelTrace_eq_zero_of_boundaryExactAt (hexact f hf)
  obtain ⟨c, hc⟩ := exists_smul_of_ker_le levelTrace ev hker
  obtain ⟨f₀, hf₀⟩ := exists_closed_levelTrace_ne_zero
  refine ⟨cornerChain v, c, κ, ?_, hκ, hc, hexact, ?_⟩
  · intro hc0
    apply hf₀
    rw [hc f₀, hc0, zero_mul]
  · intro r f
    unfold modelClass
    rw [htie _ (coneCocycle_trivialMap_closed r f), coinvHom_comp_right, coinvHom_coneCocycle]

/-- **Uniqueness of the boundary trace on level-invariant closed three-cochains.** Every linear functional
on `closedEdgeCochains rationalLevel` that kills boundary-exact cochains is a multiple of the boundary trace
`traceDataL2.trace`. -/
theorem boundaryTrace_unique (σ : closedEdgeCochains rationalLevel →ₗ[ℂ] ℂ)
    (hσ : ∀ f : closedEdgeCochains rationalLevel, BoundaryExactAt rationalLevel f.1 → σ f = 0) :
    ∃ a : ℂ, ∀ f : closedEdgeCochains rationalLevel, σ f = a * levelTrace f := by
  obtain ⟨Ω, c, κ, hc, hκ, htr, hex, -⟩ := traceComparison
  obtain ⟨a', ha'⟩ := exists_smul_of_ker_le σ
    ((evalOmega Ω).comp (closedEdgeCochains rationalLevel).subtype) (fun f hf => hσ f (hex f hf))
  refine ⟨a' / c, fun f => ?_⟩
  rw [ha' f, htr f]
  change a' * evalOmega Ω f.1 = a' / c * (c * evalOmega Ω f.1)
  field_simp

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
