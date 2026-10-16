module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Jets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.NormContinuity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothNormPower

theorem det_atInfinity {size : ℕ} (real : GeneralLinearGroup (Fin size) ℝ) :
    GeneralLinearGroup.det (atInfinity real) = realAdeleUnit (GeneralLinearGroup.det real) := by
  apply Units.ext
  apply Prod.ext
  · change (RingHom.fst ℝ FiniteAdeles) (pairMatrix real.val (1 : Matrix (Fin size) (Fin size) FiniteAdeles)).det = _
    rw [(RingHom.fst ℝ FiniteAdeles).map_det]
    rfl
  · change (RingHom.snd ℝ FiniteAdeles) (pairMatrix real.val (1 : Matrix (Fin size) (Fin size) FiniteAdeles)).det = 1
    rw [(RingHom.snd ℝ FiniteAdeles).map_det]
    change (1 : Matrix (Fin size) (Fin size) FiniteAdeles).det = 1
    exact Matrix.det_one

theorem normPower_det_atInfinity {size : ℕ} (real : GeneralLinearGroup (Fin size) ℝ) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity real)) exponent =
      Complex.exp (exponent * (Real.log real.val.det : ℂ)) := by
  rw [det_atInfinity]
  simp only [normPower, Norms.realUnit_norm, Real.log_abs]
  rfl

theorem determinant_smooth {size arity : ℕ} (index : Fin arity) :
    ContDiff ℝ ⊤ (fun matrices : SmoothJets.MatrixTuples size arity => (matrices index).det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem real_power_smooth {size arity : ℕ} (index : Fin arity) (exponent : ℂ) :
    Smooth (fun elements : Fin arity → GeneralLinearGroup (Fin size) ℝ =>
      normPower (GeneralLinearGroup.det (atInfinity (elements index))) exponent) := by
  have logarithm : ContDiffOn ℝ ⊤
      (fun matrices : SmoothJets.MatrixTuples size arity => Real.log (matrices index).det)
      (SmoothJets.domain size arity) :=
    (determinant_smooth index).contDiffOn.log (fun matrices membership => membership index)
  have formula : ContDiffOn ℝ ⊤
      (fun matrices : SmoothJets.MatrixTuples size arity =>
        Complex.exp (exponent * (Real.log (matrices index).det : ℂ)))
      (SmoothJets.domain size arity) :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn logarithm)).cexp
  apply formula.congr
  intro matrices membership
  dsimp only
  rw [normPower_det_atInfinity]
  unfold invertibleMatrix
  rw [dite_eq_left (membership index)]
  rfl

theorem adelic_power_smooth (argument : AdelicGL) (exponent : ℂ) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      normPower (GeneralLinearGroup.det (argument * atInfinity (real 0))) exponent) := by
  have smooth : Smooth (fun real : Fin 1 → RealGL3 =>
      normPower (GeneralLinearGroup.det argument) exponent *
        normPower (GeneralLinearGroup.det (atInfinity (real 0))) exponent) :=
    contDiffOn_const.mul (real_power_smooth (size := 3) (0 : Fin 1) exponent)
  convert smooth using 1
  funext matrices
  rw [map_mul, NormPower.normPower_mul_units]

theorem finiteLevel_compact (level : finiteLevel) : inMaximalCompact (atFinite level.val) := by
  constructor
  · rw [InducedContinuity.realGroup_atFinite]
    simp
  · rw [InducedContinuity.finiteGroup_atFinite]
    obtain ⟨integral, _, equality⟩ := level.property
    exact ⟨integral, equality⟩

theorem finiteLevel_power (level : finiteLevel) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atFinite level.val)) exponent = 1 := by
  simp only [normPower, InducedHeight.compact_det_norm _ (finiteLevel_compact level),
    NNReal.coe_one, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothNormPower
