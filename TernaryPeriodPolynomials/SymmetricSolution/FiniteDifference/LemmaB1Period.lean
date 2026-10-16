module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Literal
public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.PeriodClause

@[expose] public section


/-!
# Lemma B.1 (`lem:literal-residue-comparison`), last sentence and last proof paragraph: the analytic (period) clause

Formalized by Claude Sonnet 5.5.  Paper: "the composite identifies the residue with the usual odd
period polynomial in the same variables `b, c`" ("the binary modular symbol from `0` to `i∞` crosses the standard
edge once. Pairing with an arbitrary dual binary coefficient identifies its edge coefficient with the odd part of
`∫_0^{i∞} h(z)(zc - b)^{n+1} dz`, with the same orientation normalization").

**Statement (`lemma_B_1_analytic`).**  `Γ = GL₂(ℤ)`, `H₁(Γ, M) = groupHomology M 1` (Mathlib), `d = n + 1` even, `b = X 0`, `c = X 1`.

*Normalizations of the binary duality `H₁(Γ, M) ≃ Hom_Γ(St^δ, M)` (`St^δ = St ⊗ sign det`), all visible:*
* `edgeSym p₀ = reference`: the standard oriented dual edge `p₀ = (triPlus → triMinus)` carries the modular symbol `reference =
  {∞ → 0}`; `piL E₀ = 2 · reference` for `E₀ = [p₀] - [p₀.swap]`, so `κ_Frobenius = 2`: `Φ_x(E₀) = 2 · edge₂ x`
  for the Frobenius form `Φ_x` of a class `x`, while the period symbol (descent of `Φ_x` along `π : P1 → St`) has
  `σ_x(reference) = edge₂ x`, i.e. `c₂ = 1`, orientation sign `+1`.
* `edge₂ (symbolClass Φ) = periodEquiv Φ` for `Φ ∈ PeriodHom d`; `symbolClass d` is a bijection (the binary duality, built from the
  dual Farey data: `e ↦ Φ(edgeSym e)`).

*Analytic class.*  For a level-one cusp form `h` of weight `d + 2`, `analyticClass h ∈ H₁(Γ, Sym^d ⊗ ℂ)` is the unique class whose
period symbol is the analytic odd modular symbol `oddHom h`.  Its standard-edge coefficient is the odd period polynomial of `h` in
`ℂ[b, c]`: coefficient of `b^j c^(d-j)` is `binom(d, j) (-1)^j ∫_0^{i∞} h(z) z^(d-j) dz` for odd `j` and `0` for even `j`, and
`2 · edge₂(b, c) = P(b, c) - P(-b, c)` for the literal contour integral `P(b, c) = ∫_0^∞ h(it)(itc - b)^d i dt`.

*Ternary composite.*  `κ(Sh x) = resScalar · symbolClass(κ^{Hom}(Sh^{Hom} F))` for `F = H3_G_equiv x`, and for a class `x` whose
complexified residue coordinate is the period of `h`: `complexClass(κ(Sh x)) = resScalar · analyticClass h`, and `res_H x` is the odd
period polynomial of `h` coefficientwise; every cusp form period is a finite complex combination of residue coordinates.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.LemmaB1Period

open TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.BinaryCuspPeriod TernaryPoly.BinaryCuspSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.LemmaB1Period
open TernaryPeriodPolynomials.Argument.HeckeNormalization
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPeriodPolynomials.Argument.Statements TernaryPoly.RankTwoAugmentedFrames

/-- **Lemma B.1, analytic clause** (see the module documentation). -/
theorem lemma_B_1_analytic :
    -- orientation and normalizations of the binary duality
    edgeSym p0 = reference ∧
    piL E0 = (2 : ℚ) • reference ∧
    (∀ (M : Rep ℚ IntegralGL) (y : groupHomology M 1),
      ((frobM M y : PhiM M) : P1 →ₗ[ℚ] M) E0 = (2 : ℚ) • edge2 M y) ∧
    (∀ (M : Rep ℚ IntegralGL) (y : groupHomology M 1),
      ((symbolEquiv M y : SymHom M) : St →ₗ[ℚ] M) reference = edge2 M y) ∧
    (∀ (d : ℕ) (Φ : PeriodHom d), edge2 (Dplain d) (symbolClass d Φ) = (periodEquiv d Φ).val) ∧
    (∀ d : ℕ, Function.Bijective (symbolClass d)) ∧
    -- the analytic class of a cusp form
    (∀ (d : ℕ) (hd : Even d) (h : Forms d),
      ((edge2 (DC d) (analyticClass hd h) : DC d) : MvPolynomial (Fin 2) ℂ) = oddPeriod h ∧
      (∀ j : ℕ, j ≤ d →
        ((edge2 (DC d) (analyticClass hd h) : DC d) : MvPolynomial (Fin 2) ℂ).coeff (exponent d j) =
          if Odd j then (d.choose j : ℂ) * (-1) ^ j * axisMoment h (d - j) else 0) ∧
      (∀ b c : ℂ, 2 * MvPolynomial.eval ![b, c] ((edge2 (DC d) (analyticClass hd h) : DC d) : MvPolynomial (Fin 2) ℂ) =
        (∫ t : ℝ in Set.Ioi 0, h (UpperHalfPlane.ofComplex (Complex.I * t)) * (Complex.I * t * c - b) ^ d * Complex.I) -
        ∫ t : ℝ in Set.Ioi 0, h (UpperHalfPlane.ofComplex (Complex.I * t)) * (Complex.I * t * c + b) ^ d * Complex.I)) ∧
    -- the ternary composite
    (LemmaB1Literal.resScalar ≠ 0) ∧
    (∀ (n : ℕ) (x : groupHomology (AppendixBResidue.ResRep n) 3),
      AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x) =
        LemmaB1Literal.resScalar • symbolClass (n + 1)
          (AppendixBResidue.kappa n (AppendixBResidue.Sh n (AppendixBResidue.H3_G_equiv n x)))) ∧
    (∀ (n : ℕ) (hd : Even (n + 1)) (x : groupHomology (AppendixBResidue.ResRep n) 3) (f : Forms (n + 1)),
      BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n (AppendixBResidue.H3_G_equiv n x)) = periodMap (n + 1) hd f →
      rationalFunctionHom (n + 1)
          (AppendixBResidue.kappa n (AppendixBResidue.Sh n (AppendixBResidue.H3_G_equiv n x))) = oddHom f ∧
        complexClass (n + 1) (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) =
          LemmaB1Literal.resScalar • analyticClass hd f ∧
        ∀ m : Fin 2 →₀ ℕ,
          algebraMap ℚ ℂ (((AppendixBResidue.resHLit n x : TernaryPoly.OrdinaryResiduePeriod.periodSpace (n + 1)) :
              MvPolynomial (Fin 2) ℚ).coeff m) = (oddPeriod f).coeff m) ∧
    (∀ (n : ℕ) (hd : Even (n + 1)) (f : Forms (n + 1)),
      ∃ S : Finset (ℂ × groupHomology (AppendixBResidue.ResRep n) 3),
        periodMap (n + 1) hd f = ∑ p ∈ S, p.1 • BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
          (BinaryComplexPeriod.actualPeriodEquiv n (AppendixBResidue.H3_G_equiv n p.2))) := by
  refine ⟨edgeSym_p0, TernaryPeriodPolynomials.Argument.LemmaB1Period.piL_E0, fun M y => frobM_E0 M y, fun M y => symbolEquiv_reference M y,
    fun d Φ => edge2_symbolClass d Φ, symbolClass_bijective, ?_, LemmaB1Literal.resScalar_ne_zero,
    kappaLit_shLit_eq_symbolClass, ?_, exists_residue_decomposition⟩
  · intro d hd h
    exact ⟨edge2_analyticClass hd h, fun j hj => edge2_analyticClass_coeff hd h j hj,
      fun b c => two_mul_eval_edge2_analyticClass hd h b c⟩
  · intro n hd x f hf
    exact lemmaB1_analytic_instance n hd x f hf

/-- **Lemma B.1, analytic clause, unconditional form.**  With the single scalar `c = resScalar ≠ 0` of the comparison square: for every
`n` with `n + 1` even and every class `x ∈ H₃(G, ℛ_n ⊗ det)` there is a unique level-one cusp form `f` of weight `n + 3` with
`complexClass(κ(Sh x)) = c · analyticClass f` and `res_H x = oddPeriod f` coefficientwise in `b = X 0`, `c = X 1`; the standard-edge
coefficient of `analyticClass f` is that odd part (`lemma_B_1_analytic`, first block).  For `n + 1` odd all classes vanish. -/
theorem lemma_B_1_analytic_full :
    LemmaB1Literal.resScalar ≠ 0 ∧
    ∀ n : ℕ,
      (∀ (hd : Even (n + 1)) (x : groupHomology (AppendixBResidue.ResRep n) 3),
        ∃! f : Forms (n + 1),
          complexClass (n + 1) (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) =
              LemmaB1Literal.resScalar • analyticClass hd f ∧
            ∀ m : Fin 2 →₀ ℕ,
              algebraMap ℚ ℂ (((AppendixBResidue.resHLit n x : TernaryPoly.OrdinaryResiduePeriod.periodSpace (n + 1)) :
                  MvPolynomial (Fin 2) ℚ).coeff m) = (oddPeriod f).coeff m) ∧
      (Odd (n + 1) → ∀ x : groupHomology (AppendixBResidue.ResRep n) 3, x = 0) :=
  ⟨LemmaB1Literal.resScalar_ne_zero, fun n => ⟨fun hd x => lemmaB1_analytic_unique n hd x,
    fun hd x => H3_trivial_of_odd n hd x⟩⟩

end TernaryPeriodPolynomials.Argument.Statements.LemmaB1Period
