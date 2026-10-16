module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Pointwise

@[expose] public section


/-! Smooth dependence of the genuine exterior pairing in the fixed coordinate topology. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceRiemannian
open PolynomialCoefficientMetric
open scoped ContDiff Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E}

theorem contDiffOn_matrix_det {A : E → Matrix ι ι ℝ} (hA : ContDiffOn ℝ ∞ A s) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) s := by
  simp only [det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.mul contDiffOn_const
  apply contDiffOn_prod
  intro i _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hA (σ i)) i)

theorem contDiffOn_matrix_adjugate {A : E → Matrix ι ι ℝ} (hA : ContDiffOn ℝ ∞ A s) :
    ContDiffOn ℝ ∞ (fun x => (A x).adjugate) s := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  change ContDiffOn ℝ ∞ (fun x : E => (A x).adjugate i j) s
  simp only [adjugate_apply]
  apply contDiffOn_matrix_det
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro l
  by_cases h : k = j
  · subst k
    change ContDiffOn ℝ ∞ (fun x : E => (A x).updateRow j (Pi.single i 1) j l) s
    simpa only [Matrix.updateRow_self] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (Pi.single i (1 : ℝ) : ι → ℝ) l) s)
  · change ContDiffOn ℝ ∞ (fun x : E => (A x).updateRow j (Pi.single i 1) k l) s
    have he : (fun x : E => (A x).updateRow j (Pi.single i 1) k l) =
        (fun x : E => A x k l) := by
      funext x
      exact congrFun (Function.update_of_ne h (Pi.single i 1) (A x)) l
    rw [he]
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hA k) l

/-- No alternative norm on matrices is installed: this proves smoothness in
the same entrywise norm used by the coordinate atlas. -/
theorem contDiffOn_matrix_inverse {A : E → Matrix ι ι ℝ} (hA : ContDiffOn ℝ ∞ A s)
    (hinv : ∀ x ∈ s, IsUnit (A x)) : ContDiffOn ℝ ∞ (fun x => (A x)⁻¹) s := by
  have hd : ∀ x ∈ s, (A x).det ≠ 0 := fun x hx =>
    isUnit_iff_ne_zero.mp (((A x).isUnit_iff_isUnit_det).mp (hinv x hx))
  have h := ((contDiffOn_matrix_det hA).inv hd).smul (contDiffOn_matrix_adjugate hA)
  change ContDiffOn ℝ ∞ (fun x => (A x).det⁻¹ • (A x).adjugate) s at h
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv'] using h


theorem contDiffOn_inverseGram : ContDiffOn ℝ ∞ inverseGram positiveCoordinates :=
  contDiffOn_matrix_inverse contDiffOn_coordinateGram (fun x hx => (coordinateGram_posDef x hx).isUnit)

theorem contDiffOn_formPairing (n k : ℕ) (a b : FormValue n k) :
    ContDiffOn ℝ ∞ (fun x => formPairing n k x a b) positiveCoordinates := by
  simp only [formPairing_formula]
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.sum
  intro I _
  apply ContDiffOn.sum
  intro J _
  apply ContDiffOn.mul
  · apply contDiffOn_prod
    intro r _
    exact contDiffOn_pi.mp (contDiffOn_pi.mp contDiffOn_inverseGram (I r)) (J r)
  · exact ((contDiffOn_coordinateCoefficientMetric n).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const

/-- Finite coordinate evaluation is a linear injection. -/
def formCoordinatesLinear (n k : ℕ) :
    FormValue n k →ₗ[ℝ] ((Fin k → Fin 5) → Coefficients n) where
  toFun := formCoordinates
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

instance formValueFiniteDimensional (n k : ℕ) : FiniteDimensional ℝ (FormValue n k) :=
  FiniteDimensional.of_injective (formCoordinatesLinear n k) (formCoordinates_injective n k)

instance formValueNormedAddCommGroup (n k : ℕ) : NormedAddCommGroup (FormValue n k) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

/-- Keep the form topology equal to the original operator-norm topology. -/
instance formValueTopologicalSpace (n k : ℕ) : TopologicalSpace (FormValue n k) :=
  (formValueNormedAddCommGroup n k).toMetricSpace.toUniformSpace.toTopologicalSpace

instance formDualNormedAddCommGroup (n k : ℕ) : NormedAddCommGroup (FormValue n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := FormValue n k) (F := ℝ)

instance formDualNormedSpace (n k : ℕ) : NormedSpace ℝ (FormValue n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := FormValue n k) (F := ℝ)

/-- A continuous bilinear form for the original de Rham norm, with no change of topology. -/
def formContinuousBilin (n k : ℕ) (x : Coordinates) : FormValue n k →L[ℝ] FormValue n k →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap.toLinearMap).comp (formBilinear n k x)).toContinuousLinearMap

@[simp] theorem formContinuousBilin_apply (n k : ℕ) (x : Coordinates) (a b : FormValue n k) :
    formContinuousBilin n k x a b = formPairing n k x a b := rfl

instance formBilinearNormedAddCommGroup (n k : ℕ) :
    NormedAddCommGroup (FormValue n k →L[ℝ] FormValue n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := FormValue n k) (F := FormValue n k →L[ℝ] ℝ)

instance formBilinearNormedSpace (n k : ℕ) :
    NormedSpace ℝ (FormValue n k →L[ℝ] FormValue n k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := FormValue n k) (F := FormValue n k →L[ℝ] ℝ)

theorem contDiffOn_formContinuousBilin (n k : ℕ) :
    ContDiffOn ℝ ∞ (formContinuousBilin n k) positiveCoordinates := by
  apply (contDiffOn_clm_apply (𝕜 := ℝ) (D := Coordinates) (E := FormValue n k)
    (F := FormValue n k →L[ℝ] ℝ)).mpr
  intro a
  apply (contDiffOn_clm_apply (𝕜 := ℝ) (D := Coordinates) (E := FormValue n k) (F := ℝ)).mpr
  intro b
  exact contDiffOn_formPairing n k a b

/-- Pairing actual varying smooth forms is smooth wherever the positive coordinates are valid. -/
theorem contDiffOn_formPairing_functions (n k : ℕ) {s : Set Coordinates}
    (hs : s ⊆ positiveCoordinates) {a b : Coordinates → FormValue n k}
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s) :
    ContDiffOn ℝ ∞ (fun x => formPairing n k x (a x) (b x)) s :=
  (((contDiffOn_formContinuousBilin n k).mono hs).clm_apply ha).clm_apply hb

end TernaryPoly.PolynomialFormMetric
