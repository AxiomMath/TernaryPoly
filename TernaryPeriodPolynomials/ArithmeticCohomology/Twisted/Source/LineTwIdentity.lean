module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineTwSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineDetectTwClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LinePotentialsTw
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity.Helpers
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line

@[expose] public section


/-!
# The line source at the good-line reflection

For the odd character of conductor three, the line source `lineSourceTw` is evaluated at the adelic
point `rationalGroup rationalGoodLine⁻¹`.  The finite part of this point lies in the cell
`P_line(𝔸_f) · goodLineCusp · K₁` of the good-line cusp: with the permutation `w`, the unipotent
`γ = [[1,0,-1],[0,1,0],[0,0,1]]` of the finite level and the reference frame `r`,
`w = (w γ r) · r⁻¹ · γ⁻¹`, and `w γ r = [[1,1,1],[0,1,0],[0,-1,-1]]` is an integral element of the
line parabolic with corner `1` (`cellParabolicInt`).  On such an element the finite twist of the
line source is trivial (`cell_smul_alpha`), so the line source at the reflection is the real Iwasawa
expression in the Levi cocycle at the identity adele (`lineSourceTw_w`).  This is the cup product of
the potentials `lineCupDataTw` (`lineSourceTw_cupData`); the final theorem
`sphericalSourceConstructionLine_of_conductorThree` combines it with the line Levi cocycle of nonzero
class, the Kostant law and the good-line detection of the twisted source construction.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Separation (goodLineFrame goodLineFrame_val)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (lastRow_vecMul)
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial
  (ConductorThree chi_realNegOne_eq_neg_one)
open TernaryPeriodPolynomials.Separation
  (SphericalSourceConstructionLine coordinateImage_ne_bot_iff)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
  (evaluatedSource_realizes)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (rationalGoodLine rationalGoodLine_inverse)

namespace TernaryPeriodPolynomials.TwistedSource

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## The decomposition of the reflection in the cell -/

section Decomposition

/-- The integral element `w γ r = [[1,1,1],[0,1,0],[0,-1,-1]]` of the line parabolic. -/
def cellParabolicInt : GeneralLinearGroup (Fin 3) IntegralAdeles :=
  antiDiagonal * lineUnipotent (0 : IntegralAdeles) (-1) * goodLineFrame IntegralAdeles

/-- The element `γ⁻¹ = [[1,0,1],[0,1,0],[0,0,1]]` of the finite level. -/
def cellLevelInt : GeneralLinearGroup (Fin 3) IntegralAdeles :=
  lineUnipotent (0 : IntegralAdeles) 1

theorem antiDiagonal_val_int :
    (antiDiagonal : GeneralLinearGroup (Fin 3) IntegralAdeles).val =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

theorem lineUnipotent_val_int (s t : IntegralAdeles) :
    (lineUnipotent s t).val = !![1, s, t; 0, 1, 0; 0, 0, 1] := rfl

theorem cellParabolicInt_val :
    cellParabolicInt.val = !![1, 1, 1; 0, 1, 0; 0, -1, -1] := by
  unfold cellParabolicInt
  rw [Units.val_mul, Units.val_mul, goodLineFrame_val, antiDiagonal_val_int,
    lineUnipotent_val_int, Matrix.mul_fin_three, Matrix.mul_fin_three]
  congr 1
  simp

theorem cellLevelInt_val : cellLevelInt.val = !![1, 0, 1; 0, 1, 0; 0, 0, 1] :=
  lineUnipotent_val_int 0 1

theorem cellParabolicInt_mem : cellParabolicInt ∈ lineParabolic IntegralAdeles := by
  have h := cellParabolicInt_val
  refine ⟨?_, ?_⟩
  · rw [h]
    simp
  · rw [h]
    simp

theorem cellParabolicInt_reduction : integralReduction (cellParabolicInt.val 0 0) = 1 := by
  rw [cellParabolicInt_val]
  simp

theorem cellLevelInt_mem : GeneralLinearGroup.map integralEmbedding cellLevelInt ∈ finiteLevel := by
  refine Subgroup.mem_map.mpr ⟨cellLevelInt, ?_, rfl⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction cellLevelInt).val = lastRow
  rw [lastRow_vecMul]
  funext j
  rw [GeneralLinearGroup.map_apply, cellLevelInt_val]
  fin_cases j <;> simp [lastRow]

theorem cellUnipotent_mul :
    lineUnipotent (0 : IntegralAdeles) (-1) * lineUnipotent (0 : IntegralAdeles) 1 = 1 := by
  apply Units.ext
  rw [Units.val_mul, lineUnipotent_val_int, lineUnipotent_val_int, Units.val_one,
    Matrix.mul_fin_three, Matrix.one_fin_three]
  congr 1
  simp

theorem rationalFinite_w :
    rationalFinite rationalGoodLine =
      GeneralLinearGroup.map integralEmbedding
        (antiDiagonal : GeneralLinearGroup (Fin 3) IntegralAdeles) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, antiDiagonal_val_int]
  fin_cases i <;> fin_cases j <;>
    simp [rationalFinite, rationalGoodLine, GeneralLinearGroup.map_apply]

/-- **The finite part of the reflection lies in the cell of the good-line cusp.** -/
theorem rationalFinite_w_decomp :
    rationalFinite rationalGoodLine =
      GeneralLinearGroup.map integralEmbedding cellParabolicInt * goodLineCusp *
        GeneralLinearGroup.map integralEmbedding cellLevelInt := by
  have h : GeneralLinearGroup.map integralEmbedding
        (lineUnipotent (0 : IntegralAdeles) (-1)) *
      GeneralLinearGroup.map integralEmbedding cellLevelInt = 1 := by
    rw [← map_mul]
    unfold cellLevelInt
    rw [cellUnipotent_mul, map_one]
  rw [rationalFinite_w]
  unfold cellParabolicInt goodLineCusp
  simp only [map_mul]
  calc GeneralLinearGroup.map integralEmbedding
          (antiDiagonal : GeneralLinearGroup (Fin 3) IntegralAdeles)
      = GeneralLinearGroup.map integralEmbedding
          (antiDiagonal : GeneralLinearGroup (Fin 3) IntegralAdeles) *
        (GeneralLinearGroup.map integralEmbedding (lineUnipotent (0 : IntegralAdeles) (-1)) *
          GeneralLinearGroup.map integralEmbedding cellLevelInt) := by rw [h, mul_one]
    _ = _ := by group

theorem map_cellParabolicInt_mem :
    GeneralLinearGroup.map integralEmbedding cellParabolicInt ∈ lineParabolic FiniteAdeles := by
  have h := cellParabolicInt_mem
  refine ⟨?_, ?_⟩
  · rw [GeneralLinearGroup.map_apply, h.1, map_zero]
  · rw [GeneralLinearGroup.map_apply, h.2, map_zero]

end Decomposition

/-! ## The finite twist on the cell of the reflection -/

section Twist

/-- **The finite twist is trivial on the cell of the reflection.** -/
theorem cell_smul_alpha (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFinL D (rationalFinite rationalGoodLine) •
        E.α h (x * bFinL (rationalFinite rationalGoodLine)) = E.α h x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [twist_coeff_cellL D E h3 (rationalFinite rationalGoodLine) h x ν, ← rz_lift E ν h x]
  refine congrArg (fun v => rz D.cusp v x) ?_
  have hv := E.spherical ν h
  have hc := cellMap_apply_of_eq (lineCellFixes D.cusp D.chi 2 (((n : ℂ) + 1) / 2) h3)
    ⟨_, map_cellParabolicInt_mem⟩ cellLevelInt_mem rationalFinite_w_decomp hv
  unfold lineCell
  rw [hc, lineFactorHom_apply]
  exact lineFactor_apply_of_integral D.chi 2 (((n : ℂ) + 1) / 2) h3 hv map_cellParabolicInt_mem
    cellParabolicInt_mem rfl cellParabolicInt_reduction

theorem finiteGroup_w :
    finiteGroup (rationalGroup rationalGoodLine⁻¹) = rationalFinite rationalGoodLine := by
  rw [finiteGroup_rational, rationalGoodLine_inverse]

theorem realGroup_w :
    realGroup (rationalGroup rationalGoodLine⁻¹) = ratReal rationalGoodLine := by
  rw [realGroup_rational, rationalGoodLine_inverse]

/-- **The line source at the good-line reflection**: the finite twist disappears and only the real
Iwasawa expression in the Levi cocycle at the identity adele remains. -/
theorem lineSourceTw_w (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (y : Fin 3 → RealGL3) :
    lineSourceTw D E y (rationalGroup rationalGoodLine⁻¹) =
      realCoefficientComponent n D.chi (ratReal rationalGoodLine)⁻¹
        ((lineRadical n D.chi (iwL (ratReal rationalGoodLine * y 2)) -
            lineRadical n D.chi (iwL (ratReal rationalGoodLine * y 1)))
          (E.α (iwAL (ratReal rationalGoodLine * y 1)) 1 -
            E.α (iwAL (ratReal rationalGoodLine * y 0)) 1)) := by
  unfold lineSourceTw lineSourceAtTw cFL bFL
  rw [finiteGroup_w, realGroup_w, smul_sub, cell_smul_alpha D E h3, cell_smul_alpha D E h3]

/-- **The line source at the good-line reflection is the cup product of the potentials**
`lineCupDataTw` on rational vertices. -/
theorem lineSourceTw_cupData (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h3 : ConductorThree D.chi) (x : Fin 3 → RationalGL3) :
    lineSourceTw D E (fun i => ratReal (x i)) (rationalGroup rationalGoodLine⁻¹) =
      ((lineCupDataTw E D.chi).l (x 2) - (lineCupDataTw E D.chi).l (x 1))
        ((lineCupDataTw E D.chi).a (x 1) - (lineCupDataTw E D.chi).a (x 0)) :=
  (lineSourceTw_w D E h3 _).trans (lineCupDataTw_cup E D.chi x).symm

end Twist

/-! ## The final assembly -/

/-- **Source construction at the good line for the odd character of conductor three.**  If the
cuspidal representation of `D` has a `GL₂(ℤ̂)`-fixed vector and the character is a nontrivial
character of conductor three, then some summand class has a nonzero Shapiro coordinate at the
good-line cusp. -/
theorem sphericalSourceConstructionLine_of_conductorThree (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (h3 : ConductorThree D.chi) (_hne : associatePair D ≠ ⊥) :
    SphericalSourceConstructionLine D := by
  intro hsph
  have hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1 := chi_realNegOne_eq_neg_one hχ h3
  have hn : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  have pos : 0 < n := hn.pos
  obtain ⟨E, φ, hφ, hφ0⟩ := exists_lineLeviCocycle_ne_zero D hsph hn
  have hsrc := lineSourceTw_isSourceCocycle D E h3 hodd
  refine (coordinateImage_ne_bot_iff D .line true).mpr ⟨⟨lineSourceTw D E, hsrc⟩, ?_⟩
  have key := cuspRes_line_true_ne_zero_of_evaluatesTw D hodd (lineCupDataTw E D.chi)
    (lowerKostant_lineCupData E D.chi hodd) (lineKostant_constant_ne_zero n) φ
    (fun m => hφ m) hφ0 pos
    (evaluatedSource_realizes D .line ⟨lineSourceTw D E, hsrc⟩)
    (lineSourceTw_cupData D E h3)
  exact key

end TernaryPeriodPolynomials.TwistedSource
