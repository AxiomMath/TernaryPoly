module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CanonicalMain

@[expose] public section


open scoped MatrixGroups DirectSum
open CategoryTheory
open scoped Classical
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK

/-!
# The mixed cuspidal group `𝒞_P(E^∨)` and cuspidality of `T^∨η`

Formalized by Claude Sonnet 5.5.
Paper: "apply the preceding construction to `ȷ(Γ)` and pull back".  `𝒞_P(E^∨)` at the plane cusp `h⁻¹Ph` is defined as `𝒞_Q(E^∨)` is (`dualCuspidalQ`):
the `ȷ`-pullback of `𝒞_Q(E)` at the line cusp `ȷ(h)`.  The plane coordinate of the dual series lies in it, because the line coordinate of the series does (
`Tξ ∈ 𝒞_Q(E)`).

* `dualCuspidalP`, `dualCuspidalP_jmath`;
* `dual_rP_mem_dualCuspidalP`: `r_P ℰ^∨(u) ∈ 𝒞_P(E^∨)` at every plane cusp `ȷ(l)` (`3 ≤ N`);
* `dual_Td_mem_dualCuspidalP`: under canonicity of `T`, `T^∨η ∈ 𝒞_P(E^∨)` for every `η`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **`𝒞_P(E^∨)` at the plane cusp `h⁻¹Ph`**: the `ȷ`-pullback of the mixed cuspidal classes `lineFaceCuspidalInH2` of the line cusp `ȷ(h)⁻¹Qȷ(h)`. -/
def dualCuspidalP (h : SL(3, ℤ)) :
    Submodule ℂ (groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h))))) :=
  Submodule.map (facePullC (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n)
    (lineFaceCuspidalInH2 N (jmath h) n)

theorem dualCuspidalP_aux (c l : SL(3, ℤ)) (e : jmath c = l) (hp : ∀ s : gammaNPAt N c, jmath s.1 ∈ gammaNQAt N l) :
    dualCuspidalP N n c = Submodule.map (facePullC (gammaNPAt_le N c) (gammaNQAt_le_N N l) hp n)
      (lineFaceCuspidalInH2 N l n) := by
  subst e; rfl

/-- `𝒞_P(E^∨)` at the plane cusp `ȷ(l)` is the `ȷ`-pullback of `𝒞_Q(E)` at `l`. -/
theorem dualCuspidalP_jmath (l : SL(3, ℤ)) :
    dualCuspidalP N n (jmath l) = Submodule.map (pullPQ' N n l) (lineFaceCuspidalInH2 N l n) :=
  dualCuspidalP_aux N n (jmath l) l (jmath_jmath l) _

/-- **The plane restriction of the dual global class of a tuple lies in `𝒞_P(E^∨)`** (at every plane cusp `ȷ(l)`). -/
theorem dual_rP_mem_dualCuspidalP (hN : 3 ≤ N) (hn : 4 ≤ n)
    (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (l : SL(3, ℤ)) :
    resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath l)) (gammaNPAt_le N (jmath l)) (dualEJ N n hn u) ∈
      dualCuspidalP N n (jmath l) := by
  rw [dualCuspidalP_jmath, dualEJ_eq]
  refine Eq.mpr (congrArg (· ∈ _) (resToC_dual_P N n l (classCG N n hn u))) ?_
  refine Submodule.mem_map_of_mem ?_
  exact zeroFlags_line_mixed N n hN _ (classicalPlaneConstantTerms N n hN hn u).1 l

/-- **`T^∨η` is cuspidal** (conditional on canonicity of `T`): the map `T^∨` of `dual_rP_eq_dualT_of_canonical` takes values in `∏_i 𝒞_P(E^∨)`. -/
theorem dual_Td_mem_dualCuspidalP (hN : 3 ≤ N) (hn : 4 ≤ n)
    (hT : ClassicalLineConstantTerm N n hn) :
    ∃ Td : (∀ x : PlaneFaces N, QDJ N n x) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i,
      (∀ η i, Td η i ∈ dualCuspidalP N n (jmath i.rep)) ∧
      ∀ (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (η : ∀ x : PlaneFaces N, QDJ N n x),
        (∀ x, (η x).1 = dualSeedHolC N n (u x false) (jmath (planeFaceRepr x)) +
            dualSeedConjC N n (u x true) (jmath (planeFaceRepr x))) →
        (∀ x, resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
            (gammaNQAt_le_N N (jmath (planeFaceRepr x))) (dualEJ N n hn u) = (η x).1) ∧
        (∀ i : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath i.rep))
            (gammaNPAt_le N (jmath i.rep)) (dualEJ N n hn u) = Td η i) ∧
        DualZeroFlags N n (dualEJ N n hn u) := by
  obtain ⟨Td, hTd⟩ := dual_rP_eq_dualT_of_canonical N n hN hn hT
  refine ⟨Td, fun η i => ?_, hTd⟩
  obtain ⟨u, hu⟩ := dual_seed_exists N n η
  rw [← (hTd u η hu).2.1 i]
  exact dual_rP_mem_dualCuspidalP N n hN hn u i.rep

end TernaryPeriodPolynomials.Argument.EisensteinDual
