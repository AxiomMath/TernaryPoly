module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.Mellin
public import Mathlib.Analysis.MellinInversion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellinProfile
open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellinNonvanishing

theorem heightUnit_one : heightUnit 1 (by norm_num) = 1 := by
  apply Units.ext
  rw [heightUnit_val]
  ext row column
  fin_cases row <;> fin_cases column <;> simp [heightMatrix]

theorem profile_one (data : CuspidalRepresentation) (vector : data.smooth)
    (point : IntegralBinaryGL) (right : BinaryRealGL) :
    profile data vector point right 1 = data.realize vector
      (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity right) := by
  rw [profile_eq data vector point right 1 (by norm_num), heightUnit_one, one_mul]

theorem profile_eq_zero_of_mellin_zero {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL)
    (vanishing : ∀ parameter, mellin (profile data.cusp vector point right) parameter = 0)
    (height : ℝ) (positive : 0 < height) : profile data.cusp vector point right height = 0 := by
  have equality : mellin (profile data.cusp vector point right) = fun _ => 0 := funext vanishing
  have integrable : Complex.VerticalIntegrable (mellin (profile data.cusp vector point right)) 0 := by
    rw [equality]
    exact integrable_zero _ _ _
  have inversion := mellinInv_mellin_eq 0 (profile data.cusp vector point right) positive
    (CuspMellin.convergent data vector fixed point right 0) integrable
    ((profile_continuousOn data.cusp vector point right).continuousAt (isOpen_Ioi.mem_nhds positive))
  rw [equality] at inversion
  simpa only [mellinInv, smul_zero, integral_zero] using inversion.symm

theorem eq_zero_of_mellin_zero {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (vanishing : ∀ point right parameter, mellin (profile data.cusp vector point right) parameter = 0) :
    vector = 0 := by
  apply data.cusp.injective
  funext adelicPoint
  obtain ⟨rational, integral, realPoint, factorization⟩ :=
    BinaryAdelicReduction.exists_rational_integral_real adelicPoint
  rw [map_zero, Pi.zero_apply, factorization, data.cusp.leftRational]
  rw [← profile_one]
  exact profile_eq_zero_of_mellin_zero data vector fixed integral realPoint
    (vanishing integral realPoint) 1 (by norm_num)

theorem exists_nonzero {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (nonzero : vector ≠ 0) :
    ∃ point : IntegralBinaryGL, ∃ right : BinaryRealGL, ∃ parameter : ℂ,
      mellin (profile data.cusp vector point right) parameter ≠ 0 := by
  by_contra vanishing
  push Not at vanishing
  exact nonzero (eq_zero_of_mellin_zero data vector fixed vanishing)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellinNonvanishing
