module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Matrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodSpace

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryModularSymbol
open RankTwoAugmentedFrames

/-- Evaluation of a genuine full integral modular symbol satisfies all four literal period equations. -/
theorem evaluation_period (d : ℕ) (f : PeriodHom d) :
    SymmetricBinaryPeriodRelations (f.val reference).val := by
  let q := (f.val reference).val
  have h (i : Fin 5) := congrArg Subtype.val
    (hom_equivariant (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) f (periodGL i) reference)
  have hn0 : bind₁ ![-X 0,X 1] q = -q := by
    have he := h 0
    rw [periodGL_reference] at he
    change q = BinaryModularSymbolCoefficients.action (-1) (integral (periodGL 0)) q at he
    rw [periodGL_action] at he
    change q = -bind₁ ![-X 0,X 1] q at he
    linear_combination he
  have hn1 : bind₁ ![X 0,-X 1] q = -q := by
    have he := h 1
    rw [periodGL_reference] at he
    change q = BinaryModularSymbolCoefficients.action (-1) (integral (periodGL 1)) q at he
    rw [periodGL_action] at he
    change q = -bind₁ ![X 0,-X 1] q at he
    linear_combination he
  have hs : bind₁ ![X 1,X 0] q = q := by
    have he := h 2
    rw [periodGL_reference] at he
    change (f.val (-reference)).val = _ at he
    rw [map_neg] at he
    change -q = BinaryModularSymbolCoefficients.action (-1) (integral (periodGL 2)) q at he
    rw [periodGL_action] at he
    change -q = -bind₁ ![X 1,X 0] q at he
    exact neg_injective he.symm
  refine ⟨hs,hn0,hn1,?_⟩
  have ht := congrArg (fun c : St => (f.val c).val)
    (symbol_triangle (augmentedLine 1 0) (augmentedLine 1 2) (augmentedLine 1 1))
  have h3 := h 3
  have h4 := h 4
  rw [periodGL_reference] at h3 h4
  change (f.val (symbol (augmentedLine 1 0) (augmentedLine 1 2))).val =
    BinaryModularSymbolCoefficients.action (-1) (integral (periodGL 3)) q at h3
  change (f.val (symbol (augmentedLine 1 2) (augmentedLine 1 1))).val =
    BinaryModularSymbolCoefficients.action (-1) (integral (periodGL 4)) q at h4
  rw [periodGL_action] at h3 h4
  simp only [map_add,Submodule.coe_add] at ht
  rw [h3,h4] at ht
  have hn := congrArg (bind₁ (![X 0,X 0-X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)) hn1
  simp only [map_neg,bind₁_bind₁] at hn
  have hv : (fun i => bind₁ ![X 0,X 0-X 1] (![X 0,-X 1] i)) =
      (![X 0,X 1-X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) := by
    funext i
    fin_cases i <;> simp
  rw [hv] at hn
  change bind₁ ![X 0-X 1,X 1] q + bind₁ ![X 0,X 1-X 0] q = q at ht
  change q - bind₁ ![X 0-X 1,X 1] q + bind₁ ![X 0,X 0-X 1] q = 0
  linear_combination -ht + hn

/-- Faithful reference evaluation into the exact existing homogeneous binary period space. -/
def periodEvaluation (d : ℕ) : PeriodHom d →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace d where
  toFun f := ⟨f.val reference,evaluation_period d f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem periodEvaluation_val (d : ℕ) (f : PeriodHom d) :
    (periodEvaluation d f).val = f.val reference := rfl

theorem periodEvaluation_injective (d : ℕ) : Function.Injective (periodEvaluation d) := by
  intro f h he
  exact evaluation_injective _ (congrArg Subtype.val he)

end TernaryPoly.BinaryModularSymbol
