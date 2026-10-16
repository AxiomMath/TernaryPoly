module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BruhatCells

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BruhatSums

abbrev ClosedFlags := {flag : Flags .plane // flag ∉ Set.range BruhatCells.openFlag}

def openCellEquiv : (ℚ × ℚ) ≃ Set.range BruhatCells.openFlag :=
  Equiv.ofInjective BruhatCells.openFlag BruhatCells.openFlag_injective

theorem tsum_open_closed (function : Flags .plane → ℂ) (summable : Summable function) :
    (∑' coordinates : ℚ × ℚ, function (BruhatCells.openFlag coordinates)) +
      (∑' flag : ClosedFlags, function flag.val) = ∑' flag, function flag := by
  have openSum := openCellEquiv.tsum_eq
    (fun flag : Set.range BruhatCells.openFlag => function flag.val)
  change (∑' coordinates : ℚ × ℚ, function (BruhatCells.openFlag coordinates)) =
    ∑' flag : Set.range BruhatCells.openFlag, function flag.val at openSum
  rw [openSum]
  exact (summable.subtype (· ∈ Set.range BruhatCells.openFlag)).tsum_add_tsum_compl
    (summable.subtype (· ∉ Set.range BruhatCells.openFlag))

theorem eisensteinSummand_open {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (coordinates : ℚ × ℚ) :
    eisensteinSummand extension parameter argument (BruhatCells.openFlag coordinates) =
      standardIntegrand extension parameter argument
        (rationalAdele coordinates.1, rationalAdele coordinates.2) := by
  rw [BruhatCells.openFlag, RationalEisenstein.eisensteinSummand_mk data extension
    parameter induced, BruhatCells.openRepresentative_inv]
  change extension parameter
    (rationalGroup (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2) * argument) = _
  rw [map_mul, map_inv]
  change extension parameter
    ((Matrix.GeneralLinearGroup.map rationalAdele (weyl : RationalGL3))⁻¹ *
      Matrix.GeneralLinearGroup.map rationalAdele
        (lineUnipotent coordinates.1 coordinates.2) * argument) = _
  rw [map_weyl, LineDecomposition.map_lineUnipotent]
  rfl

theorem eisensteinSummand_open_shift {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (coordinates : ℚ × ℚ) (shift : Adeles × Adeles) :
    eisensteinSummand extension parameter
        (lineUnipotent shift.1 shift.2 * argument) (BruhatCells.openFlag coordinates) =
      standardIntegrand extension parameter argument
        ((rationalAdele coordinates.1, rationalAdele coordinates.2) + shift) := by
  rw [eisensteinSummand_open data extension parameter induced]
  unfold standardIntegrand
  rw [mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _), ← lineUnipotent_add]
  simp only [mul_assoc, Prod.fst_add, Prod.snd_add]

theorem eisenstein_open_summable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (value : ℂ)
    (sums : HasSum (eisensteinSummand extension parameter argument) value) :
    Summable (fun coordinates : ℚ × ℚ => standardIntegrand extension parameter argument
      (rationalAdele coordinates.1, rationalAdele coordinates.2)) := by
  have summable := sums.summable.comp_injective BruhatCells.openFlag_injective
  simpa only [Function.comp_def, eisensteinSummand_open data extension parameter induced] using
    summable

theorem eisenstein_sum_split {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL) (value : ℂ)
    (sums : HasSum (eisensteinSummand extension parameter argument) value) :
    value =
      (∑' coordinates : ℚ × ℚ, standardIntegrand extension parameter argument
        (rationalAdele coordinates.1, rationalAdele coordinates.2)) +
      (∑' flag : ClosedFlags, eisensteinSummand extension parameter argument flag.val) := by
  rw [← sums.tsum_eq, ← tsum_open_closed _ sums.summable]
  simp only [eisensteinSummand_open data extension parameter induced]

theorem continuation_sum_split {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension continuation) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re → ∀ argument,
      continuation parameter argument =
        (∑' coordinates : ℚ × ℚ, standardIntegrand extension parameter argument
          (rationalAdele coordinates.1, rationalAdele coordinates.2)) +
        (∑' flag : ClosedFlags, eisensteinSummand extension parameter argument flag.val) := by
  obtain ⟨threshold, sums⟩ := continues.2
  exact ⟨threshold, fun parameter membership argument =>
    eisenstein_sum_split data extension parameter (flat.1 parameter) argument
      (continuation parameter argument) (sums parameter membership argument)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BruhatSums
