module

public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Hom
public import TernaryPeriodPolynomials.SymmetricSolution.BinaryPeriodLift

@[expose] public section

open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.BinaryModularSymbol
open RankTwoAugmentedFrames

/-- Diagonal signs, swap, and the two positive elementary shears. -/
def periodMatrix : Fin 5 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![-1,0;0,1], !![1,0;0,-1], !![0,1;1,0], !![1,1;0,1], !![1,0;1,1]]

def periodInverse : Fin 5 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![-1,0;0,1], !![1,0;0,-1], !![0,1;1,0], !![1,-1;0,1], !![1,0;-1,1]]

def periodGL (i : Fin 5) : IntegralGL where
  val := periodMatrix i
  inv := periodInverse i
  val_inv := by fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;> norm_num [periodMatrix,periodInverse,Matrix.mul_apply,Fin.sum_univ_two]
  inv_val := by fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;> norm_num [periodMatrix,periodInverse,Matrix.mul_apply,Fin.sum_univ_two]

/-- The polynomial action of the five literal matrices, including its determinant sign. -/
theorem periodGL_action (q : MvPolynomial (Fin 2) ℚ) (i : Fin 5) :
    BinaryModularSymbolCoefficients.action (-1) (integral (periodGL i)) q =
      ![-bind₁ ![-X 0,X 1] q, -bind₁ ![X 0,-X 1] q, -bind₁ ![X 1,X 0] q,
        bind₁ ![X 0-X 1,X 1] q, bind₁ ![X 0,X 1-X 0] q] i := by
  have hs (i : Fin 5) : BinaryModularSymbolCoefficients.linearForm
      (integral (periodGL i))⁻¹.val =
      ![![-X 0,X 1], ![X 0,-X 1], ![X 1,X 0], ![X 0-X 1,X 1], ![X 0,X 1-X 0]] i := by
    funext r
    fin_cases i <;> fin_cases r <;>
      norm_num [BinaryModularSymbolCoefficients.linearForm,integral,periodGL,periodInverse,
        Fin.sum_univ_two,GeneralLinearGroup.map_apply,←map_inv] <;> ring
  rw [BinaryModularSymbolCoefficients.action_apply,BinaryModularSymbolCoefficients.substitute,hs]
  fin_cases i <;>
    norm_num [BinaryModularSymbolCoefficients.determinantCharacter,integral,periodGL,periodMatrix,
      GeneralLinearGroup.val_det_apply,GeneralLinearGroup.map_apply,Matrix.det_fin_two]

/-- The two column lines of each period matrix are literal coordinate or sum lines. -/
theorem periodGL_lines (i : Fin 5) (j : Fin 2) :
    augmentedLine (periodGL i) j.castSucc =
      augmentedLine 1 (![![0,1],![0,1],![1,0],![0,2],![2,1]] i j) := by
  let k : Fin 3 := ![![0,1],![0,1],![1,0],![0,2],![2,1]] i j
  let c : ℚ := ![![-1,1],![1,-1],![1,1],![1,1],![1,1]] i j
  have hc : IsUnit c := by fin_cases i <;> fin_cases j <;> norm_num [c]
  have hv : rationalRepresentation (periodGL i) (template j.castSucc) = c • template k := by
    rw [rationalRepresentation_apply]
    funext r
    fin_cases i <;> fin_cases j <;> fin_cases r <;>
      norm_num [periodGL,periodMatrix,template,c,k,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        GeneralLinearGroup.map_apply,Matrix.cons_val_two]
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (periodGL i) (template j.castSucc)} =
    Submodule.span ℚ {rationalRepresentation 1 (template k)}
  rw [hv,Submodule.span_singleton_smul_eq hc,map_one]
  rfl

/-- Signs fix the reference, swap reverses it, and the two shears subdivide it. -/
theorem periodGL_reference (i : Fin 5) :
    action (integral (periodGL i)) reference =
      ![reference,reference,-reference,
        symbol (augmentedLine 1 0) (augmentedLine 1 2),
        symbol (augmentedLine 1 2) (augmentedLine 1 1)] i := by
  rw [action_reference]
  have h0 : augmentedLine (periodGL i) 0 =
      augmentedLine 1 (![![0,1],![0,1],![1,0],![0,2],![2,1]] i 0) := periodGL_lines i 0
  have h1 : augmentedLine (periodGL i) 1 =
      augmentedLine 1 (![![0,1],![0,1],![1,0],![0,2],![2,1]] i 1) := periodGL_lines i 1
  rw [h0,h1]
  fin_cases i <;> first | rfl | exact symbol_reverse _ _

end TernaryPoly.BinaryModularSymbol
