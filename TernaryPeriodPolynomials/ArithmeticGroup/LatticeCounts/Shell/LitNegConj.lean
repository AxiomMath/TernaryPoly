module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.ModelComparisonNeg
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof

@[expose] public section


/-!
# Conjugation by the reflection on the negative-determinant branch

For `det g∞ < 0`, the value `vhValueNeg k h g∞ gf` equals the positive-determinant value
`vhValue k h (R g∞) (R gf R)`, where `R = diag(1, -1)` is the rational reflection, both at the
real and at the finite level. The finite reflection conjugates the local factor `ι_v(A)` into
`ι_v(D A D)` with `D = diag(1, -1)` in `GL₂(K_v)`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue vhValue_eq_of_reduction)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
  (ιGL ιGL_val ιMat ext_of_evM evM_ιMat_self evM_ιMat_ne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
  (binaryRationalFinite binaryIntegralFinite binaryRationalReal LatticeReduction)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
  (qv evM evM_qFA latticeReductionExists)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
  (reflectionGL reflectionQ det_reflectionGL reflectionQ_finite_mem det_reflectionQ_real
    reflectionQ_mul_self vhValueNeg vhValueNeg_eq_of_reduction)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj

theorem reflectionQ_mul_self_GL : reflectionQ * reflectionQ = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact reflectionQ_mul_self

/-- Cancellation for a self-inverse element. -/
theorem conj_cancel {G : Type*} [Group G] (a b g : G) (h : a * a = 1) :
    a * b * a * (a * g) = a * b * g := by
  calc a * b * a * (a * g) = a * b * (a * a) * g := by simp only [mul_assoc]
    _ = a * b * g := by rw [h, mul_one]

/-- The conjugate of a reduction of `gf` by the reflection is a reduction of `R gf R`. -/
def conjReduction (gf : BinaryFiniteGL) (L : LatticeReduction gf) :
    LatticeReduction (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ) where
  γ := reflectionQ * L.γ * reflectionQ
  det_pos := by
    have e : (Matrix.GeneralLinearGroup.det (reflectionQ * L.γ * reflectionQ)).val =
        (Matrix.GeneralLinearGroup.det L.γ).val := by
      simp only [map_mul, Units.val_mul, det_reflectionGL]
      ring
    rw [e]
    exact L.det_pos
  integral := by
    have hR : binaryRationalFinite reflectionQ ∈ binaryIntegralFinite := reflectionQ_finite_mem
    have hRR : binaryRationalFinite reflectionQ * binaryRationalFinite reflectionQ = 1 := by
      rw [← map_mul, reflectionQ_mul_self_GL, map_one]
    have key : binaryRationalFinite (reflectionQ * L.γ * reflectionQ) *
        (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ) =
        binaryRationalFinite reflectionQ * (binaryRationalFinite L.γ * gf) *
          binaryRationalFinite reflectionQ := by
      simp only [map_mul]
      calc binaryRationalFinite reflectionQ * binaryRationalFinite L.γ * binaryRationalFinite reflectionQ *
            (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
          = binaryRationalFinite reflectionQ * binaryRationalFinite L.γ *
              (binaryRationalFinite reflectionQ * binaryRationalFinite reflectionQ) * gf *
              binaryRationalFinite reflectionQ := by simp only [mul_assoc]
        _ = _ := by rw [hRR]; simp only [mul_assoc, mul_one]
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hR L.integral) hR

/-- **Reduction conjugation.** For `det g∞ < 0`, `vhValueNeg` is the positive-determinant value
of `R g∞` at the conjugate `R gf R`. -/
theorem vhValueNeg_eq_conj (k : ℤ)
    (h : CuspForm levelOne k) (gInf : BinaryRealGL) (hgInf : (Matrix.GeneralLinearGroup.det gInf).val < 0)
    (gf : BinaryFiniteGL) :
    vhValueNeg k h gInf gf =
      vhValue k h (binaryRationalReal reflectionQ * gInf)
        (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ) := by
  have hRRr : binaryRationalReal reflectionQ * binaryRationalReal reflectionQ = 1 := by
    rw [← map_mul, reflectionQ_mul_self_GL, map_one]
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal reflectionQ * gInf)).val := by
    simp only [map_mul, Units.val_mul, det_reflectionQ_real]
    linarith
  set L := Classical.choice (latticeReductionExists gf)
  rw [vhValueNeg_eq_of_reduction k h gInf hgInf gf L]
  rw [vhValue_eq_of_reduction k h _ hpos _ (conjReduction gf L)]
  congr 1
  show binaryRationalReal (reflectionQ * L.γ) * gInf =
    binaryRationalReal (reflectionQ * L.γ * reflectionQ) * (binaryRationalReal reflectionQ * gInf)
  simp only [map_mul]
  exact (conj_cancel _ _ _ hRRr).symm

/-- The finite reflection evaluated at `w` is the reflection over the completion at `w`. -/
theorem evM_map_rat (w : FinitePlace) (q : Matrix (Fin 2) (Fin 2) ℚ) :
    evM w (q.map (algebraMap ℚ FiniteAdeles)) = qv w q := by
  have h := evM_qFA w q 1
  unfold evM at h ⊢
  rw [Matrix.mul_one, Matrix.map_one (finiteEvaluation w) (map_zero _) (map_one _), mul_one] at h
  exact h

theorem qv_reflection (v : FinitePlace) :
    qv v reflectionQ.val = (reflectionGL (v.adicCompletion ℚ)).val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qv, reflectionGL]

theorem qv_reflection_sq (w : FinitePlace) :
    qv w reflectionQ.val * qv w reflectionQ.val = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qv, reflectionGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Local conjugation.** `R ι_v(A) R = ι_v(D A D)` for the reflection `D` at `v`. -/
theorem conj_ιGL (v : FinitePlace) (A : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    binaryRationalFinite reflectionQ * ιGL v A * binaryRationalFinite reflectionQ =
      ιGL v (reflectionGL (v.adicCompletion ℚ) * A * reflectionGL (v.adicCompletion ℚ)) := by
  have hRf : ∀ X : BinaryRationalGL, (binaryRationalFinite X).val =
      X.val.map (algebraMap ℚ FiniteAdeles) := fun X => rfl
  apply Units.ext
  apply ext_of_evM
  intro w
  simp only [Units.val_mul, hRf, ιGL_val]
  have hmul : ∀ X Y : Matrix (Fin 2) (Fin 2) FiniteAdeles,
      evM w (X * Y) = evM w X * evM w Y := fun X Y => by
    unfold evM
    exact Matrix.map_mul
  rw [hmul, hmul, evM_map_rat]
  by_cases hw : w = v
  · subst hw
    rw [evM_ιMat_self, evM_ιMat_self, qv_reflection]
  · rw [evM_ιMat_ne v w hw, evM_ιMat_ne v w hw, mul_one, qv_reflection_sq]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj
