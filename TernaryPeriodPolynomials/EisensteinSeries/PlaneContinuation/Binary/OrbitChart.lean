module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.OrbitStage
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProductStages
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.OrbitalMass

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
open scoped Matrix.Norms.Elementwise NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitChart

def block (frame : Rectangular ℝ) : BinaryMatrix :=
  fun row column => frame row.castSucc column

theorem block_contDiff : ContDiff ℝ ⊤ block := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  exact contDiff_apply_apply ℝ ℝ row.castSucc column

theorem determinant_contDiff : ContDiff ℝ ⊤ (fun frame => (block frame).det) := by
  simp only [Matrix.det_fin_two, block]
  fun_prop

def domain : Set (Rectangular ℝ) := {frame | 0 < (block frame).det}

theorem domain_isOpen : IsOpen domain := isOpen_lt continuous_const determinant_contDiff.continuous

theorem domain_fullRank : domain ⊆ {frame : Rectangular ℝ | FullRank frame} := by
  intro frame positive vanishing
  have zero := congrFun vanishing 2
  have formula : exterior frame 2 = (block frame).det := by
    simp [exterior, crossProduct, block, Matrix.det_fin_two, mul_comm]
  rw [formula] at zero
  exact (ne_of_gt positive) zero

theorem block_standard : block (columns (1 : PlaneMatrix)) = 1 := by
  apply Matrix.ext
  intro row column
  simp [block, columns, Matrix.one_apply, Fin.castSucc_inj]

theorem standard_mem : columns (1 : PlaneMatrix) ∈ domain := by
  change 0 < (block (columns (1 : PlaneMatrix))).det
  rw [block_standard, Matrix.det_one]
  exact zero_lt_one

theorem block_mul (frame : Rectangular ℝ) (binary : BinaryMatrix) :
    block (frame * binary) = block frame * binary := rfl

def inverseMatrix (frame : Rectangular ℝ) : PlaneMatrix := planeBlock (block frame)⁻¹ 1

theorem inverseMatrix_block (frame : Rectangular ℝ) :
    BinaryOrbitStage.block (inverseMatrix frame) = (block frame)⁻¹ := by
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> rfl

theorem inverseMatrix_block_nonzero (frame : Rectangular ℝ) (inside : frame ∈ domain) :
    (BinaryOrbitStage.block (inverseMatrix frame)).det ≠ 0 := by
  rw [inverseMatrix_block, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (ne_of_gt (show 0 < (block frame).det from inside))

theorem inverseBlock_contDiffAt (frame : Rectangular ℝ) (nonzero : (block frame).det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun value => (block value)⁻¹) frame := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  have adjugate : ContDiff ℝ ⊤ (fun value => (block value).adjugate) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;> simp [Matrix.adjugate_fin_two, block] <;> fun_prop
  exact (determinant_contDiff.contDiffAt.inv nonzero).smul adjugate.contDiffAt

theorem inverseMatrix_contDiffAt (frame : Rectangular ℝ) (inside : frame ∈ domain) :
    ContDiffAt ℝ ⊤ inverseMatrix frame := by
  have blockSmooth : ContDiff ℝ ⊤ (fun binary : BinaryMatrix => planeBlock binary 1) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;> simp [planeBlock] <;> fun_prop
  exact blockSmooth.contDiffAt.comp frame (inverseBlock_contDiffAt frame (ne_of_gt inside))

def height (frame : Rectangular ℝ) : ℝ := -Real.log (block frame).det

theorem height_contDiffAt (frame : Rectangular ℝ) (inside : frame ∈ domain) :
    ContDiffAt ℝ ⊤ height frame :=
  (determinant_contDiff.contDiffAt.log (ne_of_gt inside)).neg

theorem exists_cutoff :
    ∃ cutoff : Rectangular ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff ∧ HasCompactSupport cutoff ∧
      tsupport cutoff ⊆ domain ∧ Set.range cutoff ⊆ Set.Icc 0 1 ∧
      cutoff (columns (1 : PlaneMatrix)) = 1 := by
  obtain ⟨cutoff, supported, compact, smooth, range, value⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (domain_isOpen.mem_nhds standard_mem)
  exact ⟨cutoff, smooth, compact, supported, range, value⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryOrbitChart
