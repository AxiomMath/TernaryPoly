module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.TraceDetects

@[expose] public section


/-!
# Bilinearity of the trace pairing

`traceValue z w y` is additive and homogeneous in the line datum `(z, w)` and in the plane cocycle
`y` (`traceValue_add_left`, `traceValue_smul_left`, `traceValue_add_right`,
`traceValue_smul_right`). Together with the representative independence of
`TraceDetects.traceValue_eq_of_classes` this makes the face pairing a well-defined bilinear form on
inner classes (`FacePairing.lean`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

theorem linearCombination_fun_add {X : Type} (f g : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun x => f x + g x) c =
      Finsupp.linearCombination ℂ f c + Finsupp.linearCombination ℂ g c := by
  simp only [Finsupp.linearCombination_apply, smul_add]
  exact Finsupp.sum_add

theorem linearCombination_fun_smul {X : Type} (a : ℂ) (f : X → ℂ) (c : X →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun x => a * f x) c =
      a * Finsupp.linearCombination ℂ f c := by
  simp only [Finsupp.linearCombination_apply, smul_eq_mul]
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  ring

variable {n : ℕ}

theorem lineValue_add_left (v : Fin 2) (z z' : MaximalCycles n trivialCharacter .line)
    (w w' : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) :
    lineValue traceDataL2 (dualityData n trivialCharacter) v (z + z') (w + w') y =
      lineValue traceDataL2 (dualityData n trivialCharacter) v z w y +
        lineValue traceDataL2 (dualityData n trivialCharacter) v z' w' y := by
  unfold lineValue
  simp only [Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply,
    linearCombination_fun_add, Finset.sum_add_distrib]
  abel

theorem lineValue_smul_left (v : Fin 2) (a : ℂ) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) :
    lineValue traceDataL2 (dualityData n trivialCharacter) v (a • z) (a • w) y =
      a * lineValue traceDataL2 (dualityData n trivialCharacter) v z w y := by
  unfold lineValue
  simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    linearCombination_fun_smul, ← Finset.mul_sum, mul_sub]

theorem lineValue_add_right (v : Fin 2) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y y' : MaximalCycles n trivialCharacter .plane) :
    lineValue traceDataL2 (dualityData n trivialCharacter) v z w (y + y') =
      lineValue traceDataL2 (dualityData n trivialCharacter) v z w y +
        lineValue traceDataL2 (dualityData n trivialCharacter) v z w y' := by
  unfold lineValue
  simp only [Submodule.coe_add, Pi.add_apply, map_add, linearCombination_fun_add,
    Finset.sum_add_distrib]
  abel

theorem lineValue_smul_right (v : Fin 2) (a : ℂ) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) :
    lineValue traceDataL2 (dualityData n trivialCharacter) v z w (a • y) =
      a * lineValue traceDataL2 (dualityData n trivialCharacter) v z w y := by
  unfold lineValue
  simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
    linearCombination_fun_smul, ← Finset.mul_sum, mul_sub]

theorem traceValue_add_left (z z' : MaximalCycles n trivialCharacter .line)
    (w w' : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) :
    traceValue (z + z') (w + w') y = traceValue z w y + traceValue z' w' y := by
  unfold traceValue
  simp only [lineValue_add_left, Finset.sum_add_distrib]

theorem traceValue_smul_left (a : ℂ) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) :
    traceValue (a • z) (a • w) y = a * traceValue z w y := by
  unfold traceValue
  simp only [lineValue_smul_left, Finset.mul_sum]

theorem traceValue_add_right (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y y' : MaximalCycles n trivialCharacter .plane) :
    traceValue z w (y + y') = traceValue z w y + traceValue z w y' := by
  unfold traceValue
  simp only [lineValue_add_right, Finset.sum_add_distrib]

theorem traceValue_smul_right (a : ℂ) (z : MaximalCycles n trivialCharacter .line)
    (w : EdgeCochains n trivialCharacter 1) (y : MaximalCycles n trivialCharacter .plane) :
    traceValue z w (a • y) = a * traceValue z w y := by
  unfold traceValue
  simp only [lineValue_smul_right, Finset.mul_sum]

end TernaryPeriodPolynomials.Argument.FacePairingFull
