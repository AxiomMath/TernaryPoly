module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Literal
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Eigenperiod

@[expose] public section

/-!
# Lemma B.1, period clause: the unconditional bundle

Formalized by Claude Sonnet 5.5.  Removes the hypothesis "the complexified residue coordinate of `x`
is `periodMap f`" of `lemmaB1_analytic_instance`: the period map is bijective for even degree (`periodMap_bijective_even`), so every
class `x ∈ H₃(G, ℛ_n ⊗ det)` determines a unique cusp form (`lemmaB1_analytic_exists`, `lemmaB1_analytic_unique`).  For odd `n + 1`
the period space and hence `H₃(G, ℛ_n ⊗ det)` is zero (`H3_trivial_of_odd`), so the sentence holds for all `n`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

open TernaryPoly TernaryPoly.BinaryCuspPeriod TernaryPoly.BinaryCuspSymbol
open TernaryPeriodPolynomials.Argument.Statements
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open scoped Classical

section Unconditional

/-- The actual period map is bijective for every even degree. -/
theorem periodMap_bijective_even (d : ℕ) (hd : Even d) : Function.Bijective (BinaryCuspPeriod.periodMap d hd) :=
  BinaryCuspPeriodDetection.actual_periodMap_bijective d hd (BinaryLiftableResidueDetection.actualIntertwining d hd)

/-- **Every residue class is the period of a unique cusp form** (no hypothesis): for `n + 1` even and a class `x ∈ H₃(G, ℛ_n ⊗ det)`, there
is a unique level-one cusp form `f` of weight `n + 3` whose period `periodMap f` is the complexified residue coordinate of `x`. -/
theorem lemmaB1_analytic_exists (n : ℕ) (hd : Even (n + 1)) (x : groupHomology (ResRep n) 3) :
    ∃! f : Forms (n + 1), BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
      (BinaryComplexPeriod.actualPeriodEquiv n (H3_G_equiv n x)) = periodMap (n + 1) hd f := by
  obtain ⟨f, hf⟩ := (periodMap_bijective_even (n + 1) hd).2
    (BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1) (BinaryComplexPeriod.actualPeriodEquiv n (H3_G_equiv n x)))
  exact ⟨f, hf.symm, fun g hg => (periodMap_bijective_even (n + 1) hd).1 (hg.symm.trans hf.symm)⟩

/-- **The unconditional analytic clause for `n + 1` even.**  With `c = resScalar` (the scalar of the comparison square), every class
`x ∈ H₃(G, ℛ_n ⊗ det)` determines a unique level-one cusp form `f` of weight `n + 3` such that the complexified class `κ(Sh x)` is
`c · analyticClass f` and the literal residue `res_H x` is the odd period polynomial of `f` coefficientwise in `b = X 0`, `c = X 1`. -/
theorem lemmaB1_analytic_unique (n : ℕ) (hd : Even (n + 1)) (x : groupHomology (ResRep n) 3) :
    ∃! f : Forms (n + 1),
      complexClass (n + 1) (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) =
          LemmaB1Literal.resScalar • analyticClass hd f ∧
        ∀ m : Fin 2 →₀ ℕ,
          algebraMap ℚ ℂ (((resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : MvPolynomial (Fin 2) ℚ).coeff m) =
            (oddPeriod f).coeff m := by
  obtain ⟨f, hf, hu⟩ := lemmaB1_analytic_exists n hd x
  refine ⟨f, lemmaB1_analytic_instance n hd x f hf |>.2, ?_⟩
  intro g hg
  have h1 : oddPeriod g = oddPeriod f := by
    ext m
    exact (hg.2 m).symm.trans ((lemmaB1_analytic_instance n hd x f hf).2.2 m)
  apply (periodMap_bijective_even (n + 1) hd).1
  apply Subtype.ext
  exact h1

/-- Odd degree: `ℬ_{n+1} = 0`, hence `H₃(G, ℛ_n ⊗ det) = 0` when `n + 1` is odd. -/
theorem H3_trivial_of_odd (n : ℕ) (hd : Odd (n + 1)) (x : groupHomology (ResRep n) 3) : x = 0 := by
  have h := (residuePeriodAlg n).injective (a₁ := x) (a₂ := 0)
  apply h
  have hb : OrdinaryResiduePeriod.periodSpace (n + 1) = ⊥ := Lemma45Full.periodSpace_odd_eq_bot (n + 1) hd
  have h0 : ((residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) :
      SinglePoleCoordinate.BinaryV (n + 1)) = 0 := (Submodule.mem_bot ℚ).mp (hb ▸ (residuePeriodAlg n x).2)
  rw [map_zero]
  exact Subtype.ext h0

end Unconditional

end TernaryPeriodPolynomials.Argument.LemmaB1Period
