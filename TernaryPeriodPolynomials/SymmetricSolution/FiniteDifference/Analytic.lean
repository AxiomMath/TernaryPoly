module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.ComplexCoeff
public import TernaryPeriodPolynomials.ModularForm.Endpoint.Ray

@[expose] public section

/-!
# Lemma B.1, period clause: the analytic class of a cusp form and its standard-edge coefficient

Formalized by Claude Sonnet 5.5.  Paper: Lemma B.1, last sentence and last paragraph of the proof: "the composite identifies the residue with the usual
odd period polynomial in the same variables `b, c`".

For `d` even and a level-one cusp form `h : Forms d` of weight `d + 2` (`TernaryPoly.BinaryCuspPeriod.Forms`):
* `oddSymbolFun hd h`, `analyticSymbol hd h : Hom_Γ(St^δ, Sym^d ⊗ ℂ)`: the analytic odd modular symbol
  `{α, β} ↦ ∫ h(z)(zc - b)^d dz` (`TernaryPoly.BinaryCuspSymbol.oddHom h`), whose values are complex forms of degree `d`
  (`oddHom_mem_range`, by integral generation of `St` by the translates of the reference symbol) and which is equivariant for the
  determinant-twisted action `stD` (`oddSymbolFun_mem`, `determinantCharacter_neg_one_integral`).
* `analyticClass hd h : H₁(GL₂(ℤ), Sym^d ⊗ ℂ)`: the class whose period symbol (`symbolEquiv`, descent of the Frobenius duality)
  is `analyticSymbol hd h`.
* `edge2_analyticClass`: the standard-edge coefficient `edge₂` of this class is the odd period polynomial `oddPeriod h` of `h`
  in `ℂ[b, c]`, with `b = X 0`, `c = X 1`; `edge2_analyticClass_coeff`: the coefficient of `b^j c^(d-j)` is
  `binom(d, j) (-1)^j ∫_0^{i∞} h(z) z^(d-j) dz` for odd `j` and `0` for even `j`;
  `two_mul_eval_edge2_analyticClass`: `2 · edge₂(b, c) = P(b, c) - P(-b, c)` with the literal contour integral
  `P(b, c) = ∫_0^∞ h(it)(itc - b)^d i dt = ∫_0^{i∞} h(z)(zc - b)^d dz`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames Matrix
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPoly.BinaryCuspSymbol TernaryPoly.BinaryCuspPeriod MvPolynomial
open scoped Classical

section Analytic

variable {d : ℕ}

theorem determinantCharacter_neg_one_integral (g : IntegralGL) :
    BinaryModularSymbolCoefficients.determinantCharacter (-1) (integral g) = detQ g := by
  unfold BinaryModularSymbolCoefficients.determinantCharacter
  change (((Matrix.GeneralLinearGroup.det (integral g) : ℚˣ) : ℚ)) ^ (-1 : ℤ) = _
  have h : (((Matrix.GeneralLinearGroup.det (integral g) : ℚˣ) : ℚ)) = detQ g := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact det_integral_eq g
  rw [h, _root_.zpow_neg_one]
  exact inv_eq_of_mul_eq_one_right (detQ_mul_self g)

theorem oddPeriod_mem_CForm (f : Forms d) : oddPeriod f ∈ CForm d := oddPeriod_isHomogeneous f

/-- The values of the analytic odd symbol are evaluations of complex forms of degree `d`. -/
theorem oddHom_mem_range (hd : Even d) (f : Forms d) (c : St) :
    (oddHom f).val c ∈ LinearMap.range (evalForm d) := by
  have hc : c ∈ integralSpan := by rw [integralSpan_eq_top]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨g, rfl⟩ := hc
    rw [hom_equivariant, oddHom_reference hd]
    refine ⟨BinaryModularSymbolCoefficients.determinantCharacter (-1) (integral g) •
      cAction d g ⟨oddPeriod f, oddPeriod_mem_CForm f⟩, ?_⟩
    rw [map_smul]
    change _ • evaluate (cAction d g ⟨oddPeriod f, oddPeriod_mem_CForm f⟩ : MvPolynomial (Fin 2) ℂ) = _
    rw [evaluate_cAction]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul q c _ hc => rw [map_smul]; exact Submodule.smul_mem _ q hc

/-- The analytic odd modular symbol of a level-one cusp form `h`, as a `ℚ`-linear map `St → Sym^d ⊗ ℂ`:
`{α, β} ↦ ∫_β^α h(z)(zc - b)^d dz` (odd part, with the orientation `∞ → 0` of the reference symbol), obtained by
descending `oddHom h` (whose values are polynomial functions) through the evaluation `ℂ[b, c]_d ↪ Functions`. -/
def oddSymbolFun (hd : Even d) (f : Forms d) : St →ₗ[ℚ] DC d :=
  (LinearEquiv.ofInjective (evalForm d) (evalForm_injective d)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (evalForm d)) (oddHom f).val (oddHom_mem_range hd f)

theorem evaluate_oddSymbolFun (hd : Even d) (f : Forms d) (c : St) :
    evaluate ((oddSymbolFun hd f c : DC d) : MvPolynomial (Fin 2) ℂ) = (oddHom f).val c := by
  have h := (LinearEquiv.ofInjective (evalForm d) (evalForm_injective d)).apply_symm_apply
    ⟨(oddHom f).val c, oddHom_mem_range hd f c⟩
  exact congrArg Subtype.val h

theorem oddSymbolFun_mem (hd : Even d) (f : Forms d) : oddSymbolFun hd f ∈ SymHom (DC d) := by
  intro g c
  apply evalForm_injective d
  change evaluate ((oddSymbolFun hd f (stD g c) : DC d) : MvPolynomial (Fin 2) ℂ) =
    evaluate ((cAction d g (oddSymbolFun hd f c) : DC d) : MvPolynomial (Fin 2) ℂ)
  rw [evaluate_oddSymbolFun, evaluate_cAction, evaluate_oddSymbolFun, stD_apply, map_smul, hom_equivariant]
  change detQ g • (BinaryModularSymbolCoefficients.determinantCharacter (-1) (integral g) •
    functionUntwisted (integral g) ((oddHom f).val c)) = _
  rw [determinantCharacter_neg_one_integral, smul_smul, detQ_mul_self, one_smul]

/-- The **analytic modular symbol of `h`** in `Hom_Γ(St^δ, Sym^d ⊗ ℂ)`. -/
def analyticSymbol (hd : Even d) (f : Forms d) : SymHom (DC d) := ⟨oddSymbolFun hd f, oddSymbolFun_mem hd f⟩

/-- Its value on the reference symbol `∞ → 0` is the odd period polynomial `∫_0^{i∞} h(z)(zc - b)^d dz` (odd part). -/
theorem analyticSymbol_reference (hd : Even d) (f : Forms d) :
    ((analyticSymbol hd f : SymHom (DC d)) : St →ₗ[ℚ] DC d) reference = ⟨oddPeriod f, oddPeriod_mem_CForm f⟩ := by
  apply evalForm_injective d
  change evaluate ((oddSymbolFun hd f reference : DC d) : MvPolynomial (Fin 2) ℂ) = evaluate (oddPeriod f)
  rw [evaluate_oddSymbolFun, oddHom_reference hd]

/-- **The complex homology class of `h`**: the unique class in `H₁(GL₂(ℤ), Sym^d ⊗ ℂ)` whose period symbol is the analytic
modular symbol of `h`. -/
def analyticClass (hd : Even d) (f : Forms d) : groupHomology (DC d) 1 :=
  (symbolEquiv (DC d)).symm (analyticSymbol hd f)

theorem symbolEquiv_analyticClass (hd : Even d) (f : Forms d) :
    symbolEquiv (DC d) (analyticClass hd f) = analyticSymbol hd f :=
  (symbolEquiv (DC d)).apply_symm_apply _

/-- **The standard-edge coefficient of the class of `h` is the odd period polynomial of `h`**, in the variables `b = X 0`,
`c = X 1`. -/
theorem edge2_analyticClass (hd : Even d) (f : Forms d) :
    ((edge2 (DC d) (analyticClass hd f) : DC d) : MvPolynomial (Fin 2) ℂ) = oddPeriod f := by
  rw [← symbolEquiv_reference, symbolEquiv_analyticClass, analyticSymbol_reference]

/-- Coefficientwise: the coefficient of `b^j c^(d-j)` of the standard-edge coefficient is `binom(d, j) (-1)^j ∫_0^{i∞} h(z) z^(d-j) dz`
for odd `j` and `0` for even `j`. -/
theorem edge2_analyticClass_coeff (hd : Even d) (f : Forms d) (j : ℕ) (hj : j ≤ d) :
    ((edge2 (DC d) (analyticClass hd f) : DC d) : MvPolynomial (Fin 2) ℂ).coeff (exponent d j) =
      if Odd j then (d.choose j : ℂ) * (-1) ^ j * axisMoment f (d - j) else 0 := by
  rw [edge2_analyticClass]
  split_ifs with ho
  · rw [coeff_oddPeriod f hj ho, periodCoefficient_eq_axisMoment]
  · have he : Even j := Nat.not_odd_iff_even.mp ho
    exact coeff_oddPeriod_zero_of_even_x f _ (by simpa using he)

/-- **The literal contour integral.**  For all `b, c`, `2 · (edge₂ class of h)(b, c)` is the odd part
`P(b, c) - P(-b, c)` of `P(b, c) = ∫_0^{i∞} h(z)(zc - b)^d dz = ∫_0^∞ h(it)(itc - b)^d i dt`. -/
theorem two_mul_eval_edge2_analyticClass (hd : Even d) (f : Forms d) (b c : ℂ) :
    2 * MvPolynomial.eval ![b, c] ((edge2 (DC d) (analyticClass hd f) : DC d) : MvPolynomial (Fin 2) ℂ) =
      (∫ t : ℝ in Set.Ioi 0, f (UpperHalfPlane.ofComplex (Complex.I * t)) * (Complex.I * t * c - b) ^ d * Complex.I) -
      ∫ t : ℝ in Set.Ioi 0, f (UpperHalfPlane.ofComplex (Complex.I * t)) * (Complex.I * t * c + b) ^ d * Complex.I := by
  rw [edge2_analyticClass, two_mul_eval_oddPeriod, eval_period_eq_integral, eval_period_eq_integral]
  simp only [rayIntegrand, periodIntegrand, sub_neg_eq_add]

end Analytic

end TernaryPeriodPolynomials.Argument.LemmaB1Period
