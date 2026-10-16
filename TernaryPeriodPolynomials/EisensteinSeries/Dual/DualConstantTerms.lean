module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.RepMain
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.SeedInjective

@[expose] public section


open scoped MatrixGroups DirectSum
open CategoryTheory
open scoped Classical
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK

/-!
# The dual constant terms `r_P ℰ_Q^∨(η) = T^∨η`, UNCONDITIONAL

Formalized by Claude Sonnet 5.5.
the Eichler-Shimura injectivity at `Γ(N)` (`EichlerShimuraInj.seedMapInjective`) gives the canonicity of `T`
(`classicalLine : ClassicalLineConstantTerm N n hn`, `3 ≤ N`, `4 ≤ n`), which is the hypothesis of the conditional dual theorems
`dual_rP_eq_dualT_of_canonical`, `_reps`, `_literal`, `dual_constant_terms_all`, `dual_Td_mem_dualCuspidalP`.  Their unconditional versions follow.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- Canonicity of `T` (S4): `r_Q ℰ_P(ξ) = Tξ` for ONE linear `T` and every presentation of `ξ`. -/
theorem classicalLineConstantTerm (hN : 3 ≤ N) (hn : 4 ≤ n) : ClassicalLineConstantTerm N n hn :=
  TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn

theorem dual_rP_eq_dualT_reps (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ Td' : (⨁ i : LineFaces N, QDi N n i) →ₗ[ℂ] PDmod N n,
      (∀ η' y, (Td' η') y ∈ dualCuspidalP N n (planeFaceRepr y)) ∧
      ∀ u' : DualTuple N n, dualRQ hN hn (dualEH hn u') = dualS u' ∧ dualRP hn (dualEH hn u') = Td' (dualS u') :=
  dual_rP_eq_dualT_of_canonical_reps N n hN hn (TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn)

theorem dual_rP_eq_dualT_literal (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ TdL : (⨁ i : LineFaces N, QDiL N n i) →ₗ[ℂ] PDL N n,
      ∀ u' : DualTuple N n, dualRQL hN hn (isoHd hn (dualEH hn u')) = ΦQ (dualS u') ∧
        dualRPL hn (isoHd hn (dualEH hn u')) = TdL (ΦQ (dualS u')) :=
  dual_rP_eq_dualT_of_canonical_literal N n hN hn (TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn)

theorem dual_constant_terms_all_uncond (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ Td : (∀ x : PlaneFaces N, QDJ N n x) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i,
      ∀ η : ∀ x : PlaneFaces N, QDJ N n x, ∃ c : groupCohomology.H2 (Rep.of (dualRhoC N n)),
        (∀ x, resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
            (gammaNQAt_le_N N (jmath (planeFaceRepr x))) c = (η x).1) ∧
        (∀ i : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath i.rep))
            (gammaNPAt_le N (jmath i.rep)) c = Td η i) ∧ DualZeroFlags N n c := by
  exact dual_constant_terms_all N n hN hn (TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn)

theorem dual_Td_mem_dualCuspidalP_uncond (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ Td : (∀ x : PlaneFaces N, QDJ N n x) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i,
      (∀ η i, Td η i ∈ dualCuspidalP N n (jmath i.rep)) ∧
      ∀ (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (η : ∀ x : PlaneFaces N, QDJ N n x),
        (∀ x, (η x).1 = dualSeedHolC N n (u x false) (jmath (planeFaceRepr x)) +
            dualSeedConjC N n (u x true) (jmath (planeFaceRepr x))) →
        (∀ x, resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
            (gammaNQAt_le_N N (jmath (planeFaceRepr x))) (dualEJ N n hn u) = (η x).1) ∧
        (∀ i : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath i.rep))
            (gammaNPAt_le N (jmath i.rep)) (dualEJ N n hn u) = Td η i) ∧
        DualZeroFlags N n (dualEJ N n hn u) :=
  dual_Td_mem_dualCuspidalP N n hN hn (TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn)

theorem dual_rP_eq_dualT (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ∃ Td : (∀ x : PlaneFaces N, QDJ N n x) →ₗ[ℂ] ∀ i : LineFaces N, DPi N n i,
      ∀ (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (η : ∀ x : PlaneFaces N, QDJ N n x),
        (∀ x, (η x).1 = dualSeedHolC N n (u x false) (jmath (planeFaceRepr x)) +
            dualSeedConjC N n (u x true) (jmath (planeFaceRepr x))) →
        (∀ x, resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath (planeFaceRepr x)))
            (gammaNQAt_le_N N (jmath (planeFaceRepr x))) (dualEJ N n hn u) = (η x).1) ∧
        (∀ i : LineFaces N, resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath i.rep))
            (gammaNPAt_le N (jmath i.rep)) (dualEJ N n hn u) = Td η i) ∧
        DualZeroFlags N n (dualEJ N n hn u) :=
  dual_rP_eq_dualT_of_canonical N n hN hn (TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn)

end TernaryPeriodPolynomials.Argument.EisensteinDual
