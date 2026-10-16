module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Integrand
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.PlaneClass
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitInduction
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitPlane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitExhaust
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FibreConst

@[expose] public section


/-!
# Negative-determinant reduction of the line step

For `det g∞ < 0`: `globalIntegrand_neg`: `F_{Z,g∞}(s,t) = F_{RZR,Rg∞}(s,-t)` with `R = diag(1,-1)` (rational, integral at every place), proved by absorption with the reflected local
data `P' = D₁ P D₁`, `κ' = D₁ κ D₂` (`D₁ = diag(1,-1,1)`, `D₂ = diag(1,1,-1)`, `L(s,-t) = D₁ L(s,t) D₂`), `blk₂ P' = R blk₂ P R`, and the conjugation formula of
`ModelComparisonNeg`/`ShellLitNegConj` for `vhValueFull`.  `lineStep_neg_of_pos` derives the line step for `(Z, g∞)` from that for `(RZR, Rg∞)` (positive determinant) by the
measure preserving change of variables `x₂ ↦ -x₂` on `K_q`.

Formalized by Claude Sonnet 5.5.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlaneClass
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitExhaust
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
open MeasureTheory
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction (binaryRationalReal binaryRationalFinite)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof (evM)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LineStepNeg

section Alg

variable {K : Type*} [CommRing K]

/-- `diag(1, -1, 1)`. -/
def D1m : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, -1, 1]

/-- `diag(1, 1, -1)`. -/
def D2m : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, 1, -1]

theorem D1m_mul_self : (D1m : Matrix (Fin 3) (Fin 3) K) * D1m = 1 := by
  rw [D1m, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i; fin_cases i <;> simp

theorem D2m_mul_self : (D2m : Matrix (Fin 3) (Fin 3) K) * D2m = 1 := by
  rw [D2m, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i; fin_cases i <;> simp

/-- The reflection of the second coordinate of `L(s,t)`: `L(s,-t) = D1 L(s,t) D2`. -/
theorem LstR_neg (s t : K) : LstR s (-t) = D1m * LstR s t * D2m := by
  ext i j
  simp only [D1m, D2m, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [LstR]

theorem blk2_conj (P : Matrix (Fin 3) (Fin 3) K) :
    blk2 (D1m * P * D1m) = (reflectionGL K).val * blk2 P * (reflectionGL K).val := by
  ext i j
  simp only [blk2, D1m, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [reflectionGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- `D1`, as a unit of `GL₃`. -/
def d1GL (K : Type*) [CommRing K] : GL (Fin 3) K where
  val := D1m
  inv := D1m
  val_inv := D1m_mul_self
  inv_val := D1m_mul_self

/-- `D2`, as a unit of `GL₃`. -/
def d2GL (K : Type*) [CommRing K] : GL (Fin 3) K where
  val := D2m
  inv := D2m
  val_inv := D2m_mul_self
  inv_val := D2m_mul_self

end Alg

section Local

variable (w : FinitePlace)

theorem intGL3_D1 : IntGL3 w (D1m : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) := by
  have hinv : (D1m : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))⁻¹ = D1m :=
    Matrix.inv_eq_right_inv D1m_mul_self
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse D1m_mul_self
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [D1m, (OS w).zero_mem, (OS w).one_mem, (OS w).neg_mem]
  · rw [hinv]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [D1m, (OS w).zero_mem, (OS w).one_mem, (OS w).neg_mem]

theorem intGL3_D2 : IntGL3 w (D2m : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) := by
  have hinv : (D2m : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ))⁻¹ = D2m :=
    Matrix.inv_eq_right_inv D2m_mul_self
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_right_inverse D2m_mul_self
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [D2m, (OS w).zero_mem, (OS w).one_mem, (OS w).neg_mem]
  · rw [hinv]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [D2m, (OS w).zero_mem, (OS w).one_mem, (OS w).neg_mem]

end Local

section Global

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem D1_conj_apply {K : Type*} [CommRing K] (P : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    ((D1m * P * D1m : Matrix (Fin 3) (Fin 3) K) i j) = (![1, -1, 1] : Fin 3 → K) i * P i j * (![1, -1, 1] : Fin 3 → K) j := by
  simp only [D1m, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The finite reflection evaluated at `w`. -/
theorem eval_Rf (w : FinitePlace) :
    (GeneralLinearGroup.map (finiteEvaluation w) (binaryRationalFinite reflectionQ)).val =
      (reflectionGL (w.adicCompletion ℚ)).val := by
  show (binaryRationalFinite reflectionQ).val.map (finiteEvaluation w) = _
  show evM w (reflectionQ.val.map (algebraMap ℚ FiniteAdeles)) = _
  rw [evM_map_rat, qv_reflection]

theorem hZ_reflect (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val) (w : FinitePlace) :
    IntGL w (GeneralLinearGroup.map (finiteEvaluation w)
      (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)).val := by
  have e : (GeneralLinearGroup.map (finiteEvaluation w)
      (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)).val =
      (reflectionGL (w.adicCompletion ℚ)).val * (GeneralLinearGroup.map (finiteEvaluation w) Z).val *
        (reflectionGL (w.adicCompletion ℚ)).val := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, eval_Rf]
  rw [e]
  exact intGL_reflect w _ (hZ w)

/-- **The global integrand under the reflection.** For `det g∞ < 0` and `z = (s,t)`: `F_{Z,g∞}(s,t) = F_{RZR,Rg∞}(s,-t)`. -/
theorem globalIntegrand_neg (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hneg : (Matrix.GeneralLinearGroup.det gInf).val < 0)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (z : FiniteAwayThree × FiniteAwayThree) :
    globalIntegrand I Z gInf z =
      globalIntegrand I (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)
        (binaryRationalReal reflectionQ * gInf) (z.1, -z.2) := by
  obtain ⟨T, hzT⟩ := Uex_cover z
  set S := SEP T with hSdef
  have hz : z ∈ UregionS S := hzT
  have hz' : ((z.1, -z.2) : FiniteAwayThree × FiniteAwayThree) ∈ UregionS S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hz w hw
    refine ⟨h1, ?_⟩
    show finiteEvaluation w (-(awayVal z.2)) ∈ OS w
    rw [map_neg]
    exact (OS w).neg_mem h2
  choose P κ hP20 hP21 hfac hκ _ using
    fun w : FinitePlace => local_plane_level w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2))
  -- original absorption
  obtain ⟨X, hX, heq⟩ := globalIntegrand_absorb I h hform S P κ (fun w _ => ⟨hP20 w, hP21 w⟩) z
    (fun w _ => by rw [evM3_LfinGLof]; exact hfac w) (fun w _ => hκ w)
    (fun w hw => intGL3_LfinGLof_of_mem hz w hw) Z hZ gInf
  -- reflected data
  let P' : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
    fun w => d1GL _ * P w * d1GL _
  let κ' : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
    fun w => d1GL _ * κ w * d2GL _
  have hP' : ∀ w ∈ S, (P' w).val 2 0 = 0 ∧ (P' w).val 2 1 = 0 := by
    intro w _
    constructor
    · show ((D1m * (P w).val * D1m : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) 2 0) = 0
      rw [D1_conj_apply, hP20 w]; simp
    · show ((D1m * (P w).val * D1m : Matrix (Fin 3) (Fin 3) (w.adicCompletion ℚ)) 2 1) = 0
      rw [D1_conj_apply, hP21 w]; simp
  have hnegz : (awayVal (-z.2)) = -(awayVal z.2) := rfl
  have hS' : ∀ w ∈ S, evM3 w (LfinGLof (awayVal z.1) (awayVal (-z.2))).val = (P' w).val * (κ' w).val := by
    intro w _
    rw [evM3_LfinGLof, hnegz, map_neg, LstR_neg, hfac w]
    show _ = (D1m * (P w).val * D1m) * (D1m * (κ w).val * D2m)
    calc D1m * ((P w).val * (κ w).val) * D2m
        = D1m * (P w).val * 1 * (κ w).val * D2m := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = D1m * (P w).val * (D1m * D1m) * (κ w).val * D2m := by rw [D1m_mul_self]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hκ' : ∀ w ∈ S, IntGL3 w (κ' w).val := by
    intro w _
    show IntGL3 w (D1m * (κ w).val * D2m)
    exact intGL3_mul w (intGL3_mul w (intGL3_D1 w) (hκ w)) (intGL3_D2 w)
  have hL' : ∀ w, w ∉ S → IntGL3 w (evM3 w (LfinGLof (awayVal (z.1, -z.2).1) (awayVal (z.1, -z.2).2)).val) :=
    fun w hw => intGL3_LfinGLof_of_mem hz' w hw
  obtain ⟨X', hX', heq'⟩ := globalIntegrand_absorb I h hform S P' κ' hP' (z.1, -z.2) hS' hκ' hL'
    (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)
    (hZ_reflect Z hZ) (binaryRationalReal reflectionQ * gInf)
  -- the blocks
  have hRR : binaryRationalFinite reflectionQ * binaryRationalFinite reflectionQ = 1 := reflectionF_mul_self
  have hXX : X' = binaryRationalFinite reflectionQ * X * binaryRationalFinite reflectionQ := by
    apply gl2_ext
    intro w
    simp only [map_mul, Units.val_mul]
    rw [hX' w, eval_Rf, hX w]
    have hRl := reflect_mul_self_mat (w.adicCompletion ℚ)
    by_cases hw : w ∈ S
    · rw [ite_eq_left hw, ite_eq_left hw]
      show blk2 (D1m * (P w).val * D1m) = _
      rw [blk2_conj]
    · rw [ite_eq_right hw, ite_eq_right hw, Matrix.mul_one, hRl]
  have hdetblk : ∀ w ∈ S, (blk2 (P' w).val).det = (blk2 (P w).val).det := by
    intro w _
    show (blk2 (D1m * (P w).val * D1m)).det = _
    rw [blk2_conj, Matrix.det_mul, Matrix.det_mul]
    have hd : (reflectionGL (w.adicCompletion ℚ)).val.det = -1 := by
      show (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)).det = -1
      rw [Matrix.det_fin_two_of]; ring
    rw [hd]; ring
  have hvh : vhValueFull (-2 * I.halfWeight) h (binaryRationalReal reflectionQ * gInf)
      (X' * (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)) =
      vhValueFull (-2 * I.halfWeight) h gInf (X * Z) := by
    have hRg : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal reflectionQ * gInf)).val := by
      simp only [map_mul, Units.val_mul, det_reflectionQ_real]
      linarith
    have e1 : X' * (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ) =
        binaryRationalFinite reflectionQ * (X * Z) * binaryRationalFinite reflectionQ := by
      rw [hXX]
      calc binaryRationalFinite reflectionQ * X * binaryRationalFinite reflectionQ *
            (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)
          = binaryRationalFinite reflectionQ * X * (binaryRationalFinite reflectionQ *
              binaryRationalFinite reflectionQ) * Z * binaryRationalFinite reflectionQ := by
            simp only [mul_assoc]
        _ = _ := by rw [hRR]; simp only [mul_assoc, mul_one]
    rw [e1]
    unfold vhValueFull
    rw [ite_eq_left hRg, ite_eq_right (not_lt.2 hneg.le), vhValueNeg_eq_conj _ h gInf hneg (X * Z)]
  have hprod : ∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ)) =
      ∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w (blk2 (P' w).val).det‖ : ℂ)) :=
    Finset.prod_congr rfl fun w hw => by rw [hdetblk w hw]
  rw [heq, heq', hprod, det_reflect_base Z, hvh]

open MeasureTheory in
/-- **The line step for `det g∞ < 0` from the line step for the reflected data.** -/
theorem lineStep_neg_of_pos (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hneg : (Matrix.GeneralLinearGroup.det gInf).val < 0)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (q : FinitePlace) (hq : q ≠ placeThree) (c : ℂ)
    (hpos : GlobalLimitInduction.LineStep I (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)
      (binaryRationalReal reflectionQ * gInf) q hq c) :
    GlobalLimitInduction.LineStep I Z gInf q hq c := by
  intro T hT hqT y
  set F' := globalIntegrand I (binaryRationalFinite reflectionQ * Z * binaryRationalFinite reflectionQ)
    (binaryRationalReal reflectionQ * gInf) with hF'
  have hpt : ∀ z : FiniteAwayThree × FiniteAwayThree, globalIntegrand I Z gInf z = F' (z.1, -z.2) :=
    fun z => globalIntegrand_neg I h hform gInf hneg Z hZ z
  let φ : (q.adicCompletion ℚ × q.adicCompletion ℚ) ≃ᵐ (q.adicCompletion ℚ × q.adicCompletion ℚ) :=
    (MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.neg _)
  have hφ : MeasurePreserving φ ((finiteCompletionMeasure q).prod (finiteCompletionMeasure q))
      ((finiteCompletionMeasure q).prod (finiteCompletionMeasure q)) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
  set G : q.adicCompletion ℚ × q.adicCompletion ℚ → ℂ := fun x =>
    F' (finiteAwayThreeAtPlace q hq x.1 + iotaS T hT y.1, finiteAwayThreeAtPlace q hq x.2 + iotaS T hT (-y.2))
    with hG
  have hcongr : ∀ x : q.adicCompletion ℚ × q.adicCompletion ℚ,
      globalIntegrand I Z gInf (finiteAwayThreeAtPlace q hq x.1 + iotaS T hT y.1,
        finiteAwayThreeAtPlace q hq x.2 + iotaS T hT y.2) = G (φ x) := by
    intro x
    rw [hpt]
    show F' _ = F' _
    congr 1
    refine Prod.ext rfl ?_
    show -(finiteAwayThreeAtPlace q hq x.2 + iotaS T hT y.2) = finiteAwayThreeAtPlace q hq (-x.2) + iotaS T hT (-y.2)
    rw [map_neg, map_neg, neg_add]
  simp_rw [hcongr]
  rw [hφ.integral_comp' G]
  have h1 := hpos T hT hqT (y.1, -y.2)
  rw [hpt (iotaS T hT y.1, iotaS T hT y.2)]
  show ∫ x, G x ∂_ = c * F' (iotaS T hT y.1, -iotaS T hT y.2)
  rw [← map_neg]
  exact h1

end Global

end TernaryPeriodPolynomials.Argument.LatticeCounts.LineStepNeg
