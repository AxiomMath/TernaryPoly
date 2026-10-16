module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Natural
public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.SymbolClass
public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.LemmaB1Literal
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.CompositeOdd

@[expose] public section

/-!
# Lemma B.1, period clause: the ternary route, the analytic class, and the single scalar

Formalized by Claude Sonnet 5.5.  Paper: Lemma B.1 and its proof.

* `complexClass d : H₁(Γ, Sym^d) → H₁(Γ, Sym^d ⊗ ℂ)`, `symbolEquiv_complexClass`, `edge2_complexClass`: complexification of
  coefficients is natural for the period symbol and for `edge₂`.
* `complexClass_symbolClass_eq_analyticClass`: if the complexified Hom-class `Φ` is the analytic odd symbol of `h`
  (`rationalFunctionHom Φ = oddHom h`), the complexified class of `symbolClass Φ` is `analyticClass h`.
* `kappaLit_shLit_eq_symbolClass` (R4 `S3`): `κ(Sh x) = resScalar · symbolClass(κ^{Hom}(Sh^{Hom} H3_G_equiv x))`; the scalar `c₂` of
  `edge2_symbolClass` is `1`.
* `lemmaB1_analytic_instance` (R4 `S0` strengthened): for a class `x` whose complexified residue coordinate is the period of a cusp
  form `h`: the Hom class of `x` is `oddHom h`, `complexClass(κ(Sh x)) = resScalar · analyticClass h`, and `res_H x` is the odd period
  polynomial of `h` coefficientwise.
* `exists_residue_decomposition`: every cusp form period is a finite complex combination of residue coordinates.
* `lemma_B_1_period_clause`: the literal clause composed with `lemma_B_1_literal`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPoly.BinaryCuspSymbol TernaryPoly.BinaryCuspPeriod
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open scoped Classical

section Complexification

/-- **Complexification of a rational class**: `H₁(GL₂(ℤ), Sym^d) → H₁(GL₂(ℤ), Sym^d ⊗ ℂ)`, induced by the coefficient inclusion
`cInc d : Sym^d → Sym^d ⊗ ℂ` (a morphism of `ℚ`-representations). -/
def complexClass (d : ℕ) : groupHomology (Dplain d) 1 →ₗ[ℚ] groupHomology (DC d) 1 :=
  (groupHomology.map (MonoidHom.id IntegralGL) (cInc d) 1).hom

/-- The complexified period symbol of a rational class. -/
def complexSymbol (d : ℕ) (y : groupHomology (Dplain d) 1) : SymHom (DC d) :=
  ⟨(cInc d).hom.toLinearMap ∘ₗ ((symbolEquiv (Dplain d) y : SymHom (Dplain d)) : St →ₗ[ℚ] Dplain d), fun g c => by
    change (cInc d).hom (((symbolEquiv (Dplain d) y : SymHom (Dplain d)) : St →ₗ[ℚ] Dplain d) (stD g c)) =
      (DC d).ρ g ((cInc d).hom (((symbolEquiv (Dplain d) y : SymHom (Dplain d)) : St →ₗ[ℚ] Dplain d) c))
    rw [(symbolEquiv (Dplain d) y).2 g c]
    exact Rep.hom_comm_apply (cInc d) g _⟩

/-- **Naturality**: the period symbol of the complexified class is the complexified period symbol. -/
theorem symbolEquiv_complexClass (d : ℕ) (y : groupHomology (Dplain d) 1) :
    symbolEquiv (DC d) (complexClass d y) = complexSymbol d y :=
  Subtype.ext (symbolEquiv_natural (cInc d) y)

/-- `edge₂` commutes with complexification of coefficients. -/
theorem edge2_complexClass (d : ℕ) (y : groupHomology (Dplain d) 1) :
    edge2 (DC d) (complexClass d y) = (cInc d).hom (edge2 (Dplain d) y) :=
  edge2_natural (cInc d) y

/-- If the complexified class of a rational class `y` is the analytic class of `h`, the complexified standard-edge coefficient of
`y` is the odd period polynomial of `h` coefficientwise (complex coefficient transport `algebraMap ℚ ℂ`). -/
theorem complexified_edge2_eq_oddPeriod {d : ℕ} (hd : Even d) (f : Forms d) (y : groupHomology (Dplain d) 1)
    (hy : complexClass d y = analyticClass hd f) (m : Fin 2 →₀ ℕ) :
    algebraMap ℚ ℂ (((edge2 (Dplain d) y : Dplain d) : MvPolynomial (Fin 2) ℚ).coeff m) =
      (oddPeriod f).coeff m := by
  have h1 := edge2_complexClass d y
  rw [hy] at h1
  have h2 := congrArg (fun P : DC d => (P : MvPolynomial (Fin 2) ℂ).coeff m) h1
  change ((edge2 (DC d) (analyticClass hd f) : DC d) : MvPolynomial (Fin 2) ℂ).coeff m =
    (((cInc d).hom (edge2 (Dplain d) y) : DC d) : MvPolynomial (Fin 2) ℂ).coeff m at h2
  rw [edge2_analyticClass, cInc_apply, MvPolynomial.coeff_map] at h2
  exact h2.symm

end Complexification

section Bridge

open TernaryPoly.OrdinaryResiduePeriod

/-- **From the rational Hom-model to the analytic class.**  If the complexification of the Hom-class `Φ ∈ PeriodHom d` is the
analytic odd modular symbol of the cusp form `h` (`rationalFunctionHom d Φ = oddHom h`), then the complexified class of `Φ`
(`complexClass d (symbolClass d Φ)`) is `analyticClass h`. -/
theorem complexClass_symbolClass_eq_analyticClass {d : ℕ} (hd : Even d) (f : Forms d) (Φ : PeriodHom d)
    (hΦ : rationalFunctionHom d Φ = oddHom f) :
    complexClass d (symbolClass d Φ) = analyticClass hd f := by
  apply (symbolEquiv (DC d)).injective
  rw [symbolEquiv_complexClass, symbolEquiv_analyticClass]
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  apply evalForm_injective d
  have h1 : (symbolEquiv (Dplain d) (symbolClass d Φ) : SymHom (Dplain d)) = periodHomEquivSym d Φ :=
    symbolEquiv_symbolClassM (Dplain d) _
  change evaluate (((cInc d).hom (((symbolEquiv (Dplain d) (symbolClass d Φ) : SymHom (Dplain d)) :
      St →ₗ[ℚ] Dplain d) c) : DC d) : MvPolynomial (Fin 2) ℂ) =
    evaluate ((oddSymbolFun hd f c : DC d) : MvPolynomial (Fin 2) ℂ)
  rw [evaluate_oddSymbolFun, h1, cInc_apply, ← rationalEvaluate_map, ← hΦ, rationalFunctionHom_apply]
  rfl

end Bridge

section Ternary

open TernaryPeriodPolynomials.Argument.Statements

/-- **The ternary route agrees with the binary duality** (R4 `S3`, acceptance test for the orientation convention):
`κ(Sh x) = resScalar · symbolClass(κ^{Hom}(Sh^{Hom} F))` for `F = H3_G_equiv x`, with `c₂ = 1`
(`edge2_symbolClass`: `edge₂ ∘ symbolClass = periodEquiv`; the standard dual edge `p₀ = (triPlus → triMinus)` carries the symbol
`reference = ∞ → 0`). -/
theorem kappaLit_shLit_eq_symbolClass (n : ℕ) (x : groupHomology (AppendixBResidue.ResRep n) 3) :
    AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x) =
      LemmaB1Literal.resScalar • symbolClass (n + 1)
        (AppendixBResidue.kappa n (AppendixBResidue.Sh n (AppendixBResidue.H3_G_equiv n x))) := by
  apply TernaryPeriodPolynomials.Argument.FareyTree.edge2_injective (Dplain (n + 1))
  rw [map_smul, edge2_symbolClass]
  have h1 : ((TernaryPeriodPolynomials.Argument.FareyTree.edge2 (Dplain (n + 1))
      (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) : Dplain (n + 1)) :
        MvPolynomial (Fin 2) ℚ) =
      ((AppendixBResidue.residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) :
        MvPolynomial (Fin 2) ℚ) := rfl
  have h2 : (periodEquiv (n + 1) (AppendixBResidue.kappa n (AppendixBResidue.Sh n (AppendixBResidue.H3_G_equiv n x)))) =
      AppendixBResidue.resHLit n x := by
    change AppendixBResidue.edge2 n (AppendixBResidue.kappa n (AppendixBResidue.Sh n (AppendixBResidue.H3_G_equiv n x))) = _
    exact AppendixBResidue.residue_comparison_square n _
  apply Subtype.ext
  rw [h1, LemmaB1Literal.residuePeriodAlg_eq_resScalar]
  rw [h2]
  rfl

end Ternary

section Instance

open TernaryPeriodPolynomials.Argument.Statements

/-- **Lemma B.1, analytic clause, for a class and its cusp form** (strengthening of R4 `S0` by `S1`-`S3`).  Let `x ∈ H₃(G, 𝓡_n ⊗ det)`
and `h` a level-one cusp form of weight `n + 3` whose period is the complexified residue coordinate of `x`
(`hf`, as in `composite_is_odd_period`).  Then, with `y = κ(Sh x) ∈ H₁(GL₂(ℤ), Sym^{n+1})` and `c = resScalar`:

1. the Hom class of `x` is the analytic odd modular symbol of `h`;
2. the complexified class `complexClass y = c · analyticClass h` (the canonical class of `h`, scalar `c` exactly the scalar of the
   comparison square, no other factor: `c₂ = 1`, `κ_Frobenius = 2` cancel);
3. the complexified residue `res_H x` is the odd period polynomial of `h` coefficientwise in `b = X 0, c = X 1`. -/
theorem lemmaB1_analytic_instance (n : ℕ) (hd : Even (n + 1)) (x : groupHomology (AppendixBResidue.ResRep n) 3)
    (f : Forms (n + 1))
    (hf : BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
      (BinaryComplexPeriod.actualPeriodEquiv n (AppendixBResidue.H3_G_equiv n x)) = periodMap (n + 1) hd f) :
    rationalFunctionHom (n + 1) (AppendixBResidue.kappa n (AppendixBResidue.Sh n (AppendixBResidue.H3_G_equiv n x))) =
        oddHom f ∧
      complexClass (n + 1) (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) =
        LemmaB1Literal.resScalar • analyticClass hd f ∧
      ∀ m : Fin 2 →₀ ℕ,
        algebraMap ℚ ℂ (((AppendixBResidue.resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : MvPolynomial (Fin 2) ℚ).coeff m) =
          (oddPeriod f).coeff m := by
  have hc := AppendixBResidue.composite_is_odd_period n hd (AppendixBResidue.H3_G_equiv n x) f hf
  refine ⟨hc.1, ?_, ?_⟩
  · rw [kappaLit_shLit_eq_symbolClass, map_smul,
      complexClass_symbolClass_eq_analyticClass hd f _ hc.1]
  · intro m
    have h1 : MvPolynomial.map (algebraMap ℚ ℂ)
        ((AppendixBResidue.resH n (AppendixBResidue.H3_G_equiv n x)).val.val) = oddPeriod f := by
      rw [← AppendixBResidue.resH_extend_val, hf]
      rfl
    have h2 := congrArg (·.coeff m) h1
    rw [MvPolynomial.coeff_map] at h2
    exact h2

end Instance

section Existence

open TernaryPeriodPolynomials.Argument.Statements

/-- **Every level-one cusp form is a complex combination of residue classes**: the odd period of `h` is
`∑ a_i · extend(actualPeriodEquiv(H3_G_equiv x_i))` for finitely many rational classes `x_i ∈ H₃(G, 𝓡_n ⊗ det)` and complex scalars
`a_i` (complex transport by the explicit `tensorPeriodEquiv`), and hence coefficientwise
`[b^j c^(d-j)] (odd part of ∫_0^{i∞} h(z)(zc-b)^d dz) = ∑ a_i · [b^j c^(d-j)] res_H x_i`. -/
theorem exists_residue_decomposition (n : ℕ) (hd : Even (n + 1)) (f : Forms (n + 1)) :
    ∃ S : Finset (ℂ × groupHomology (AppendixBResidue.ResRep n) 3),
      periodMap (n + 1) hd f = ∑ p ∈ S, p.1 • BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n (AppendixBResidue.H3_G_equiv n p.2)) := by
  let g : groupHomology (AppendixBResidue.ResRep n) 3 ≃ₗ[ℚ] BinaryComplexPeriod.space ℚ (n + 1) :=
    (AppendixBResidue.H3_G_equiv n).trans (BinaryComplexPeriod.actualPeriodEquiv n)
  let T := BinaryComplexPeriod.tensorPeriodEquiv (n + 1)
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset
    ((LinearMap.lTensor ℂ g.symm.toLinearMap) (T.symm (periodMap (n + 1) hd f)))
  refine ⟨S, ?_⟩
  have h1 : LinearMap.lTensor ℂ g.toLinearMap ((LinearMap.lTensor ℂ g.symm.toLinearMap) (T.symm (periodMap (n + 1) hd f))) =
      T.symm (periodMap (n + 1) hd f) := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext; intro v; simp
    rw [this, LinearMap.lTensor_id]
    rfl
  have h2 := congrArg (fun w => T (LinearMap.lTensor ℂ g.toLinearMap w)) hS
  simp only [h1, LinearEquiv.apply_symm_apply, map_sum, LinearMap.lTensor_tmul] at h2
  refine h2.trans (Finset.sum_congr rfl fun p _ => ?_)
  exact BinaryComplexPeriod.tensorPeriodEquiv_tmul (n + 1) p.1 (g p.2)

end Existence

section Clause

open TernaryPeriodPolynomials.Argument.Statements

/-- **Lemma B.1, period clause, composed with `lemma_B_1_literal`.**  There is one nonzero scalar `c` (the scalar of the comparison
square) such that: whenever the complexified class `κ(Sh x) ∈ H₁(GL₂(ℤ), Sym^{n+1} ⊗ ℂ)` is the canonical class `analyticClass h`
of a level-one cusp form `h` of weight `n + 3`, the normalized residue `c · res_H x` is, coefficientwise in the same variables
`b = X 0`, `c = X 1`, the odd part of the contour integral `∫_0^{i∞} h(z)(zc - b)^{n+1} dz`. -/
theorem lemma_B_1_period_clause :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ (n : ℕ) (hd : Even (n + 1)) (x : groupHomology (AppendixBResidue.ResRep n) 3) (f : Forms (n + 1)),
      complexClass (n + 1) (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) =
          analyticClass hd f →
      ∀ m : Fin 2 →₀ ℕ,
        algebraMap ℚ ℂ (c * ((AppendixBResidue.resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : MvPolynomial (Fin 2) ℚ).coeff m) =
          (oddPeriod f).coeff m := by
  refine ⟨LemmaB1Literal.resScalar, LemmaB1Literal.resScalar_ne_zero, fun n hd x f hy m => ?_⟩
  have h3 := complexified_edge2_eq_oddPeriod hd f _ hy m
  rw [← h3]
  congr 1
  have h4 : ((TernaryPeriodPolynomials.Argument.FareyTree.edge2 (Dplain (n + 1))
      (AppendixBLiteral.kappa_literal n (AppendixBLiteral.shapiro_literal n x)) : Dplain (n + 1)) :
        MvPolynomial (Fin 2) ℚ) =
      ((AppendixBResidue.residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : MvPolynomial (Fin 2) ℚ) := rfl
  rw [h4, LemmaB1Literal.residuePeriodAlg_eq_resScalar]
  simp

end Clause

end TernaryPeriodPolynomials.Argument.LemmaB1Period
