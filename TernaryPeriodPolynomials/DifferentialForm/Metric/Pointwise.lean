module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Evaluation
public import TernaryPeriodPolynomials.DifferentialForm.Metric.Contraction

@[expose] public section


/-! The actual positive coefficient-valued exterior metric in every degree. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceRiemannian
open PolynomialCoefficientMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The genuine cotangent Gram matrix, inverse to the trace tangent metric. -/
def inverseGram (x : Coordinates) : Matrix (Fin 5) (Fin 5) ℝ := (coordinateGram x)⁻¹

theorem inverseGram_posDef (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (inverseGram x).PosDef := (coordinateGram_posDef x hx).inv

/-- The coefficient bilinear form in the actual positive coordinate chart. -/
def coordinateCoefficientBilin (n : ℕ) (x : Coordinates) :
    Coefficients n →ₗ[ℝ] Coefficients n →ₗ[ℝ] ℝ :=
  matrixBilinear n (determinantNormalize (reconstruct x))

@[simp] theorem coordinateCoefficientBilin_apply (n : ℕ) (x : Coordinates) (p q : Coefficients n) :
    coordinateCoefficientBilin n x p q = coordinateCoefficientMetric n x p q := rfl

theorem coordinateCoefficientBilin_positive (n : ℕ) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (p : Coefficients n) (hp : p ≠ 0) :
    0 < coordinateCoefficientBilin n x p p :=
  matrixPairing_positive _ (determinantNormalize_positive _ hx) p.val
    (fun hz => hp (Subtype.ext hz))

theorem coordinateCoefficientBilin_symm (n : ℕ) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (p q : Coefficients n) :
    coordinateCoefficientBilin n x p q = coordinateCoefficientBilin n x q p :=
  matrixPairing_symmetric _
    (Matrix.isHermitian_iff_isSymm.mp (determinantNormalize_positive _ hx).isHermitian) p.val q.val

/-- The ordered-tuple contraction, with the exact exterior normalization 1/k!. -/
def formPairing (n k : ℕ) (x : Coordinates) (a b : FormValue n k) : ℝ :=
  (k.factorial : ℝ)⁻¹ * matrixContraction (coordinateCoefficientBilin n x)
    (tensorMatrix k (inverseGram x)) (formCoordinates a) (formCoordinates b)

theorem formPairing_formula (n k : ℕ) (x : Coordinates) (a b : FormValue n k) :
    formPairing n k x a b = (k.factorial : ℝ)⁻¹ *
      ∑ I : Fin k → Fin 5, ∑ J : Fin k → Fin 5,
        (∏ r, inverseGram x (I r) (J r)) *
          coordinateCoefficientMetric n x (a (fun r => Pi.single (I r) 1))
            (b (fun r => Pi.single (J r) 1)) := rfl

@[simp] theorem formPairing_zero_left (n k : ℕ) (x : Coordinates) (b : FormValue n k) :
    formPairing n k x 0 b = 0 := by
  simp [formPairing, matrixContraction, formCoordinates]

@[simp] theorem formPairing_zero_right (n k : ℕ) (x : Coordinates) (a : FormValue n k) :
    formPairing n k x a 0 = 0 := by
  simp [formPairing, matrixContraction, formCoordinates]

theorem formPairing_positive (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n k) (ha : a ≠ 0) : 0 < formPairing n k x a a := by
  apply mul_pos (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos k))
  apply matrixContraction_positive _ (coordinateCoefficientBilin_positive n x hx)
    _ (tensorMatrix_posDef k _ (inverseGram_posDef x hx))
  intro hz
  exact ha (formCoordinates_injective n k (hz.trans (formCoordinates_zero n k).symm))

theorem formPairing_nonneg (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n k) : 0 ≤ formPairing n k x a a := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (formPairing_positive n k x hx a ha).le

theorem formPairing_self_eq_zero (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n k) : formPairing n k x a a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    exact (ne_of_gt (formPairing_positive n k x hx a ha)) h
  · rintro rfl; simp

theorem formPairing_symm (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a b : FormValue n k) : formPairing n k x a b = formPairing n k x b a := by
  unfold formPairing
  congr 1
  apply matrixContraction_symm _ (coordinateCoefficientBilin_symm n x hx)
  exact Matrix.isHermitian_iff_isSymm.mp (tensorMatrix_posDef k _ (inverseGram_posDef x hx)).isHermitian

theorem formPairing_add_left (n k : ℕ) (x : Coordinates) (a b c : FormValue n k) :
    formPairing n k x (a + b) c = formPairing n k x a c + formPairing n k x b c := by
  simp [formPairing, matrixContraction, formCoordinates, mul_add, Finset.sum_add_distrib]

theorem formPairing_smul_left (n k : ℕ) (x : Coordinates) (t : ℝ) (a b : FormValue n k) :
    formPairing n k x (t • a) b = t * formPairing n k x a b := by
  simp [formPairing, matrixContraction, formCoordinates, Finset.mul_sum, mul_left_comm]

theorem formPairing_add_right (n k : ℕ) (x : Coordinates) (a b c : FormValue n k) :
    formPairing n k x a (b + c) = formPairing n k x a b + formPairing n k x a c := by
  simp [formPairing, matrixContraction, formCoordinates, mul_add, Finset.sum_add_distrib]

theorem formPairing_smul_right (n k : ℕ) (x : Coordinates) (t : ℝ) (a b : FormValue n k) :
    formPairing n k x a (t • b) = t * formPairing n k x a b := by
  simp [formPairing, matrixContraction, formCoordinates, Finset.mul_sum, mul_left_comm]

/-- The actual exterior pairing bundled bilinearly. -/
def formBilinear (n k : ℕ) (x : Coordinates) : FormValue n k →ₗ[ℝ] FormValue n k →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := formPairing n k x a
      map_add' := formPairing_add_right n k x a
      map_smul' := fun t b => formPairing_smul_right n k x t a b }
  map_add' a b := by ext c; exact formPairing_add_left n k x a b c
  map_smul' t a := by ext b; exact formPairing_smul_left n k x t a b

end TernaryPoly.PolynomialFormMetric
