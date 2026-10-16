module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.ParallelRules
public import TernaryPeriodPolynomials.DifferentialForm.Connection.ContractionTensorAlgebra

@[expose] public section


/-! The actual symmetric inverse-metric contraction is parallel for the full tensor connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy SymmetricSpaceCharts
open SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem differentiableAt_contractionBilinear (n k : ℕ) (w : Coordinates → FormValue n (k + 1))
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (v z : Coordinates)
    (hw : DifferentiableAt ℝ w x) :
    DifferentiableAt ℝ (fun y => contractionBilinear n k y (w y) v z) x := by
  have hL := (((contDiffOn_coefficientFormMap n k (contDiffOn_symmetricPart n v) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  convert! DifferentiableAt.clm_apply (𝕜 := ℝ) (E := Coordinates) (G := FormValue n k) (H := FormValue n k)
    (c := fun y => coefficientFormMap (symmetricPart n y v) k)
    (u := fun y => insertion n k z (w y)) (x := x)
    (by convert! hL using 1) (by convert! differentiableAt_insertion n k w x z hw using 1) using 1

theorem differentiableAt_inverseGram_entry (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (i j : Fin 5) : DifferentiableAt ℝ (fun y => inverseGram y i j) x := by
  exact (((contDiffOn_pi.mp (contDiffOn_pi.mp contDiffOn_inverseGram i) j x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))

theorem fderiv_inverseGram_entry (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (i j : Fin 5) :
    fderiv ℝ (fun y => inverseGram y i j) x u = fderiv ℝ inverseGram x u i j := by
  have hH := (((contDiffOn_inverseGram x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hi := differentiableAt_pi.mp hH i
  rw [fderiv_apply hi j, fderiv_apply hH i]
  rfl

theorem covariantFormDerivative_symmetricContraction (n k : ℕ)
    (w : Coordinates → FormValue n (k + 1)) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (hw : DifferentiableAt ℝ w x) :
    covariantFormDerivative n k (fun y => symmetricContraction n k y (w y)) x u =
      symmetricContraction n k x (covariantFormDerivative n (k + 1) w x u) := by
  let : IsBoundedSMul ℝ (FormValue n k) := by
    convert! (NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := FormValue n k)) using 1
  let B : Fin 5 → Fin 5 → Coordinates → FormValue n k :=
    fun i j y => contractionBilinear n k y (w y) (Pi.single i 1) (Pi.single j 1)
  have hB (i j : Fin 5) : DifferentiableAt ℝ (B i j) x :=
    differentiableAt_contractionBilinear n k w x hx _ _ hw
  have hH (i j : Fin 5) := differentiableAt_inverseGram_entry x hx i j
  have hprod (i j : Fin 5) : DifferentiableAt ℝ (fun y => inverseGram y i j • B i j y) x := by
    convert! DifferentiableAt.smul (𝕜 := ℝ) (F := FormValue n k)
      (c := fun y => inverseGram y i j) (f := B i j)
      (by convert! hH i j using 1) (by convert! hB i j using 1) using 1
  have hsum (i : Fin 5) : DifferentiableAt ℝ (fun y => ∑ j, inverseGram y i j • B i j y) x := by
    convert! DifferentiableAt.fun_sum (𝕜 := ℝ)
      (A := fun j y => inverseGram y i j • B i j y) (x := x) (u := Finset.univ)
      (fun j _ => by convert! hprod i j using 1) using 1
  change covariantFormDerivative n k (fun y => ∑ i, ∑ j, inverseGram y i j • B i j y) x u = _
  rw [covariantFormDerivative_sum n k _ x u hsum]
  simp_rw [covariantFormDerivative_sum n k _ x u (hprod _),
    covariantFormDerivative_smul n k _ _ x u (hH _ _) (hB _ _), fderiv_inverseGram_entry x hx u]
  simp only [B, covariantFormDerivative_contractionBilinear n k w x hx u _ _ hw,
    Finset.sum_add_distrib]
  have hc := bilinearContraction_connection_cancel (contractionBilinear n k x (w x)) x hx u
  unfold bilinearContraction at hc
  change _ = bilinearContraction (contractionBilinear n k x (covariantFormDerivative n (k + 1) w x u))
    (inverseGram x) (fun i => Pi.single i 1) (fun i => Pi.single i 1)
  unfold bilinearContraction
  apply ContinuousAlternatingMap.ext
  intro v
  have hcv := congrArg (fun a : FormValue n k => a v) hc
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at hcv ⊢
  simp only [_root_.smul_add, Finset.sum_add_distrib]
  have he : ∀ a b c d : Coefficients n, a + (b + c + d) = b + (a + c + d) := by
    intros; abel
  rw [he, hcv, add_zero]

end TernaryPoly.PolynomialFormConnection
