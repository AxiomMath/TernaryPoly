module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Coercive

@[expose] public section


/-! Genuine smooth zero-order operators for the symmetric connection energy. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open ContinuousAlternatingMap
open scoped ContDiff Matrix.Norms.Elementwise

instance formOperatorNormedAddCommGroup (n k l : ℕ) : NormedAddCommGroup (FormValue n k →L[ℝ] FormValue n l) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := FormValue n k) (F := FormValue n l)

instance formOperatorNormedSpace (n k l : ℕ) : NormedSpace ℝ (FormValue n k →L[ℝ] FormValue n l) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := FormValue n k) (F := FormValue n l)

/-- Insertion in the actual first alternating slot. -/
def insertion (n k : ℕ) (v : Coordinates) : FormValue n (k + 1) →L[ℝ] FormValue n k :=
  (curryLeftLI (𝕜 := ℝ) (E := Coordinates) (F := Coefficients n) (n := k)).toContinuousLinearMap.flip v

@[simp] theorem insertion_apply (n k : ℕ) (v : Coordinates) (a : FormValue n (k + 1)) :
    insertion n k v a = a.curryLeft v := rfl

def symmetricExteriorCLM (n k : ℕ) (x : Coordinates) : FormValue n k →L[ℝ] FormValue n (k + 1) :=
  ∑ d : Fin 5, (PolynomialFormCoordinates.symbol n k d).comp
    (coefficientFormMap (symmetricPart n x (Pi.single d 1)) k)

@[simp] theorem symmetricExteriorCLM_apply (n k : ℕ) (x : Coordinates) (a : FormValue n k) :
    symmetricExteriorCLM n k x a = symmetricExterior n k x a := by
  rw [symmetricExterior_symbol]
  rfl

def symmetricContractionCLM (n k : ℕ) (x : Coordinates) : FormValue n (k + 1) →L[ℝ] FormValue n k :=
  ∑ i : Fin 5, ∑ j : Fin 5, inverseGram x i j •
    (coefficientFormMap (symmetricPart n x (Pi.single i 1)) k).comp (insertion n k (Pi.single j 1))

@[simp] theorem symmetricContractionCLM_apply (n k : ℕ) (x : Coordinates) (a : FormValue n (k + 1)) :
    symmetricContractionCLM n k x a = symmetricContraction n k x a := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [symmetricContractionCLM, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, symmetricContraction_apply]
  rfl

theorem contDiffOn_coefficientFormMap (n k : ℕ) {L : Coordinates → Coefficients n →L[ℝ] Coefficients n}
    (hL : ContDiffOn ℝ ∞ L positiveCoordinates) :
    ContDiffOn ℝ ∞ (fun x => coefficientFormMap (E := Coordinates) (L x) k) positiveCoordinates := by
  convert! (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ Coordinates (Coefficients n) (Coefficients n)
    (Fin k)).contDiff.comp_contDiffOn hL using 1

theorem contDiffOn_symmetricExteriorCLM (n k : ℕ) :
    ContDiffOn ℝ ∞ (symmetricExteriorCLM n k) positiveCoordinates := by
  apply ContDiffOn.sum
  intro d _
  exact ContDiffOn.clm_comp (𝕜 := ℝ) (E := FormValue n k) (F := FormValue n k) (G := FormValue n (k + 1))
    (contDiffOn_const (c := PolynomialFormCoordinates.symbol n k d))
    (contDiffOn_coefficientFormMap n k (contDiffOn_symmetricPart n (Pi.single d 1)))

theorem contDiffOn_symmetricContractionCLM (n k : ℕ) :
    ContDiffOn ℝ ∞ (symmetricContractionCLM n k) positiveCoordinates := by
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp contDiffOn_inverseGram i) j).smul
    (ContDiffOn.clm_comp (𝕜 := ℝ) (E := FormValue n (k + 1)) (F := FormValue n k) (G := FormValue n k)
      (contDiffOn_coefficientFormMap n k (contDiffOn_symmetricPart n (Pi.single i 1)))
      (contDiffOn_const (c := insertion n k (Pi.single j 1))))

theorem contDiffOn_symmetricExterior (n k : ℕ) {w : Coordinates → FormValue n k}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (fun x => symmetricExterior n k x (w x)) positiveCoordinates := by
  simpa only [symmetricExteriorCLM_apply] using ContDiffOn.clm_apply (G := FormValue n (k + 1)) (contDiffOn_symmetricExteriorCLM n k) hw

theorem contDiffOn_symmetricContraction (n k : ℕ) {w : Coordinates → FormValue n (k + 1)}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) :
    ContDiffOn ℝ ∞ (fun x => symmetricContraction n k x (w x)) positiveCoordinates := by
  simpa only [symmetricContractionCLM_apply] using ContDiffOn.clm_apply (G := FormValue n k) (contDiffOn_symmetricContractionCLM n k) hw

theorem symmetricExterior_zero (n k : ℕ) (x : Coordinates) : symmetricExterior n k x 0 = 0 := by
  simpa only [symmetricExteriorCLM_apply] using (symmetricExteriorCLM n k x).map_zero

theorem symmetricContraction_zero (n k : ℕ) (x : Coordinates) : symmetricContraction n k x 0 = 0 := by
  simpa only [symmetricContractionCLM_apply] using (symmetricContractionCLM n k x).map_zero

end TernaryPoly.PolynomialFormGeometricEnergy
