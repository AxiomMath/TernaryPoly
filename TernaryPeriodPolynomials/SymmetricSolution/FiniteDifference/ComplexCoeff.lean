module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Symbol
public import TernaryPeriodPolynomials.ModularForm.Symbol.Odd

@[expose] public section

/-!
# Lemma B.1, period clause: the complex coefficient module `Sym^d ⊗ ℂ`

Formalized by Claude Sonnet 5.5.  Paper: Lemma B.1.

* `CForm d`: complex binary forms of degree `d`, a `ℚ`-submodule of `ℂ[b, c]` (`b = X 0`, `c = X 1`).
* `DC d : Rep ℚ GL₂(ℤ)`: `Sym^d ⊗ ℂ`, complex forms of degree `d` with the untwisted integral action `P ↦ P ∘ g⁻¹` (a `ℚ`-representation, so
  that Mathlib's `groupHomology (DC d) 1` is `H₁(GL₂(ℤ), Sym^d ⊗ ℂ)`).
* `cInc d : Dplain d ⟶ DC d`: the complexification of coefficients (`map (algebraMap ℚ ℂ)`), a morphism of `ℚ`-representations
  (`cExtend_equivariant`).
* `evalForm d`: evaluation of a complex form as a function on `ℂ²`, injective (`evalForm_injective`), `Γ`-equivariant (`evaluate_cAction`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames Matrix
open TernaryPeriodPolynomials.Argument.FareyTree
open TernaryPeriodPolynomials.Argument.HeckeDuality
open scoped Classical

section ComplexCoeff

open TernaryPoly.BinaryCuspSymbol MvPolynomial

/-- Complex binary forms of degree `d`, as a `ℚ`-submodule of `ℂ[b, c]`. -/
def CForm (d : ℕ) : Submodule ℚ (MvPolynomial (Fin 2) ℂ) :=
  (homogeneousSubmodule (Fin 2) ℂ d).restrictScalars ℚ

theorem mem_CForm {d : ℕ} {P : MvPolynomial (Fin 2) ℂ} : P ∈ CForm d ↔ P.IsHomogeneous d := Iff.rfl

theorem linearForm_isHomogeneous (M : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (TernaryPoly.BinaryCuspSymbol.linearForm M i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

theorem substitute_isHomogeneous (M : Matrix (Fin 2) (Fin 2) ℂ) {P : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) : (TernaryPoly.BinaryCuspSymbol.substitute M P).IsHomogeneous d :=
  isHomogeneous_bind₁_linear hP _ (linearForm_isHomogeneous M)

/-- The untwisted integral action of `GL₂(ℤ)` on complex binary forms (substitution by the inverse matrix). -/
def cRep : Representation ℚ IntegralGL (MvPolynomial (Fin 2) ℂ) := polynomialUntwisted.comp integral

def cAction (d : ℕ) : Representation ℚ IntegralGL (CForm d) :=
  cRep.subrepresentation (CForm d) (fun _ _ hP => substitute_isHomogeneous _ hP)

theorem cAction_coe (d : ℕ) (g : IntegralGL) (P : CForm d) :
    ((cAction d g P : CForm d) : MvPolynomial (Fin 2) ℂ) =
      TernaryPoly.BinaryCuspSymbol.substitute ((complexify (integral g))⁻¹ : GeneralLinearGroup (Fin 2) ℂ) P := rfl

/-- `Sym^d ⊗ ℂ`: complex binary forms of degree `d`, viewed as a `ℚ`-representation of `GL₂(ℤ)` (untwisted action). -/
abbrev DC (d : ℕ) : Rep ℚ IntegralGL := Rep.of (cAction d)

/-- Evaluation of a polynomial on `ℂ²` is `GL₂(ℤ)`-equivariant for the untwisted actions. -/
theorem evaluate_cAction (d : ℕ) (g : IntegralGL) (P : CForm d) :
    evaluate (cAction d g P : MvPolynomial (Fin 2) ℂ) =
      functionUntwisted (integral g) (evaluate (P : MvPolynomial (Fin 2) ℂ)) := by
  funext v
  change eval v (substitute ((complexify (integral g))⁻¹ : GeneralLinearGroup (Fin 2) ℂ) (P : MvPolynomial (Fin 2) ℂ)) = _
  rw [eval_substitute]
  rfl

open TernaryPoly.BinaryModularSymbolCoefficients in
theorem map_substitute (M : Matrix (Fin 2) (Fin 2) ℚ) (f : MvPolynomial (Fin 2) ℚ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (TernaryPoly.BinaryModularSymbolCoefficients.substitute M f) =
      TernaryPoly.BinaryCuspSymbol.substitute (M.map (algebraMap ℚ ℂ)) (MvPolynomial.map (algebraMap ℚ ℂ) f) := by
  unfold TernaryPoly.BinaryModularSymbolCoefficients.substitute TernaryPoly.BinaryCuspSymbol.substitute
  rw [MvPolynomial.map_bind₁]
  have : (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (TernaryPoly.BinaryModularSymbolCoefficients.linearForm M i)) =
      TernaryPoly.BinaryCuspSymbol.linearForm (M.map (algebraMap ℚ ℂ)) := by
    funext i
    simp [TernaryPoly.BinaryModularSymbolCoefficients.linearForm, TernaryPoly.BinaryCuspSymbol.linearForm]
  rw [this]

/-- Coefficient extension `ℚ[b, c]_d → ℂ[b, c]_d`. -/
def cExtend (d : ℕ) : BinaryModularSymbolCoefficients.HomogeneousPoly d →ₗ[ℚ] CForm d where
  toFun f := ⟨MvPolynomial.map (algebraMap ℚ ℂ) (f : MvPolynomial (Fin 2) ℚ), (f.2).map _⟩
  map_add' f g := Subtype.ext (by simp)
  map_smul' q f := Subtype.ext (map_rat_smul (MvPolynomial.map (algebraMap ℚ ℂ)) q (f : MvPolynomial (Fin 2) ℚ))

theorem cExtend_equivariant (d : ℕ) (g : IntegralGL) (f : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    cExtend d ((Dplain d).ρ g f) = cAction d g (cExtend d f) := by
  apply Subtype.ext
  change MvPolynomial.map (algebraMap ℚ ℂ)
      ((BinaryModularSymbolCoefficients.action 0 (GeneralLinearGroup.map (Int.castRingHom ℚ) g)
        (f : MvPolynomial (Fin 2) ℚ))) = _
  rw [BinaryModularSymbolCoefficients.action_apply]
  have h0 : BinaryModularSymbolCoefficients.determinantCharacter 0 (GeneralLinearGroup.map (Int.castRingHom ℚ) g) = 1 := by
    simp [BinaryModularSymbolCoefficients.determinantCharacter]
  rw [h0, one_smul, map_substitute]
  rw [cAction_coe]
  congr 2

/-- Complexification of coefficients `Sym^d → Sym^d ⊗ ℂ` as a morphism of `ℚ`-representations of `GL₂(ℤ)`. -/
def cInc (d : ℕ) : Dplain d ⟶ DC d :=
  Rep.ofHom ⟨cExtend d, fun g => LinearMap.ext fun f => cExtend_equivariant d g f⟩

theorem cInc_apply (d : ℕ) (f : (Dplain d)) :
    (((cInc d).hom f : DC d) : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.map (algebraMap ℚ ℂ) (f : MvPolynomial (Fin 2) ℚ) := rfl

/-- Evaluation `evaluate : ℂ[b, c] → Functions` is injective on `CForm d`. -/
def evalForm (d : ℕ) : CForm d →ₗ[ℚ] Functions := evaluate ∘ₗ (CForm d).subtype

theorem evalForm_injective (d : ℕ) : Function.Injective (evalForm d) := fun _ _ h =>
  Subtype.ext (evaluate_injective h)

end ComplexCoeff

end TernaryPeriodPolynomials.Argument.LemmaB1Period
