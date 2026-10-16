module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.ThreeLevel

@[expose] public section


/-!
# The finite adelic line Iwasawa decomposition, trivial at three

The involution `θ(x) = J (x⁻¹)ᵀ J` (`J` the antidiagonal permutation) exchanges the plane and line
parabolics and preserves integral matrices. It transports the plane decomposition
`GL₃(𝔸_f) = P(𝔸_f) GL₃(Ẑ)` to the line parabolic. When the three-component lies in the local
level, the line factor can be chosen trivial at three and the compact factor in `finiteLevel`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.HeckeEigen

variable {R : Type*} [CommRing R]

/-- The antidiagonal permutation matrix. -/
def antiJ : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem antiJ_mul_self : (antiJ : Matrix (Fin 3) (Fin 3) R) * antiJ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [antiJ, Matrix.mul_apply, Fin.sum_univ_three]

theorem antiJ_transpose : (antiJ : Matrix (Fin 3) (Fin 3) R)ᵀ = antiJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [antiJ]

theorem conj_inv_aux (A B : Matrix (Fin 3) (Fin 3) R) (h : B * A = 1) :
    antiJ * Aᵀ * antiJ * (antiJ * Bᵀ * antiJ) = 1 := by
  calc antiJ * Aᵀ * antiJ * (antiJ * Bᵀ * antiJ) = antiJ * (Aᵀ * (antiJ * antiJ) * Bᵀ) * antiJ := by
        simp only [Matrix.mul_assoc]
    _ = antiJ * (B * A)ᵀ * antiJ := by rw [antiJ_mul_self, Matrix.mul_one, Matrix.transpose_mul]
    _ = 1 := by rw [h, Matrix.transpose_one, Matrix.mul_one, antiJ_mul_self]

/-- `θ(x) = J (x⁻¹)ᵀ J`. -/
def theta (x : GL3 R) : GL3 R :=
  ⟨antiJ * (x⁻¹).valᵀ * antiJ, antiJ * x.valᵀ * antiJ,
    conj_inv_aux _ _ (by rw [Units.mul_inv]), conj_inv_aux _ _ (by rw [Units.inv_mul])⟩

theorem theta_val (x : GL3 R) : (theta x).val = antiJ * (x⁻¹).valᵀ * antiJ := rfl

theorem theta_inv_val (x : GL3 R) : (theta x)⁻¹.val = antiJ * x.valᵀ * antiJ := rfl

theorem theta_mul (x y : GL3 R) : theta (x * y) = theta x * theta y := by
  apply Units.ext
  rw [Units.val_mul, theta_val, theta_val, theta_val, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]
  calc antiJ * ((x⁻¹).valᵀ * (y⁻¹).valᵀ) * antiJ =
      antiJ * ((x⁻¹).valᵀ * (antiJ * antiJ) * (y⁻¹).valᵀ) * antiJ := by
        rw [antiJ_mul_self, Matrix.mul_one]
    _ = antiJ * (x⁻¹).valᵀ * antiJ * (antiJ * (y⁻¹).valᵀ * antiJ) := by
        simp only [Matrix.mul_assoc]

theorem theta_theta (x : GL3 R) : theta (theta x) = x := by
  apply Units.ext
  rw [theta_val, theta_inv_val, Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose,
    Matrix.transpose_transpose]
  calc antiJ * (antiJ * (x.val * antiJ)) * antiJ = (antiJ * antiJ) * x.val * (antiJ * antiJ) := by
        simp only [Matrix.mul_assoc]
    _ = x.val := by rw [antiJ_mul_self, Matrix.one_mul, Matrix.mul_one]

theorem antiJ_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (antiJ : Matrix (Fin 3) (Fin 3) R).map φ = antiJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [antiJ]

theorem antiJ_conj_apply (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (antiJ * M * antiJ : Matrix (Fin 3) (Fin 3) R) i j = M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [antiJ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem theta_map {S : Type*} [CommRing S] (φ : R →+* S) (x : GL3 R) :
    GeneralLinearGroup.map φ (theta x) = theta (GeneralLinearGroup.map φ x) := by
  apply Units.ext
  change ((theta x).val).map φ = (theta (GeneralLinearGroup.map φ x)).val
  rw [theta_val, theta_val, ← map_inv, Matrix.map_mul, Matrix.map_mul, antiJ_map φ]
  rfl

theorem theta_plane {x : GL3 R} (hx : x ∈ planeParabolic R) : theta x ∈ lineParabolic R := by
  have hi := inPlane_inv hx
  refine ⟨?_, ?_⟩
  · rw [theta_val, antiJ_conj_apply]
    exact hi.2
  · rw [theta_val, antiJ_conj_apply]
    exact hi.1

/-- **The finite adelic line Iwasawa decomposition.** -/
theorem finiteGL_line_compact_factorization (x : FiniteGL) :
    ∃ p : FiniteGL, p ∈ lineParabolic FiniteAdeles ∧
      ∃ κ : GeneralLinearGroup (Fin 3) IntegralAdeles, x = p * GeneralLinearGroup.map integralEmbedding κ := by
  obtain ⟨p, κ, h⟩ := finiteGL_parabolic_compact_factorization (theta x)
  refine ⟨theta p.val, theta_plane p.property, theta κ, ?_⟩
  rw [theta_map, ← theta_mul, ← h, theta_theta]

theorem generalLinearGroup_map_line {S : Type*} [CommRing S] (φ : R →+* S) {x : GL3 R}
    (hx : x ∈ lineParabolic R) : GeneralLinearGroup.map φ x ∈ lineParabolic S := by
  constructor
  · rw [GeneralLinearGroup.map_apply, hx.1, map_zero]
  · rw [GeneralLinearGroup.map_apply, hx.2, map_zero]

theorem finiteAtThree_line {m : LocalThreeGL} (hm : m ∈ lineParabolic ℚ_[3]) :
    finiteAtThree m ∈ lineParabolic FiniteAdeles := by
  constructor
  · change (0 : FiniteAdeles) + finiteAtThreeScalar (m.val 1 0 - finiteThree 0) = 0
    simp only [hm.1, map_zero, sub_self, finiteAtThreeScalar_zero, zero_add]
  · change (0 : FiniteAdeles) + finiteAtThreeScalar (m.val 2 0 - finiteThree 0) = 0
    simp only [hm.2, map_zero, sub_self, finiteAtThreeScalar_zero, zero_add]

/-- When the local component at three is in the level, the finite line factor can be chosen to
be one there. -/
theorem finiteGL_line_level_factorization (matrix : FiniteGL)
    (three : InLocalThreeLevel (GeneralLinearGroup.map finiteThree matrix)) :
    ∃ (parabolic : FiniteGL) (compact : finiteLevel), parabolic ∈ lineParabolic FiniteAdeles ∧
      GeneralLinearGroup.map finiteThree parabolic = 1 ∧ matrix = parabolic * compact.val := by
  obtain ⟨parabolic, hpar, compact, factors⟩ := finiteGL_line_compact_factorization matrix
  have original_three := three
  obtain ⟨integer, _, integer_eq⟩ := three
  rw [padicThreeEmbedding_matrix] at integer_eq
  let local_lift := integer * (GeneralLinearGroup.map integralThree compact)⁻¹
  have local_lift_eq : GeneralLinearGroup.map padicThreeEmbedding local_lift =
      GeneralLinearGroup.map finiteThree parabolic := by
    dsimp only [local_lift]
    rw [map_mul, map_inv, finiteThree_integralMatrix, integer_eq, factors, map_mul,
      mul_inv_cancel_right]
  let correction := finiteAtThree (GeneralLinearGroup.map finiteThree parabolic)
  have correction_integral : correction ∈ finiteIntegralGLLevel 3 := by
    change finiteAtThree (GeneralLinearGroup.map finiteThree parabolic) ∈ _
    rw [← local_lift_eq]
    exact finiteAtThree_integral local_lift
  have correction_line : correction ∈ lineParabolic FiniteAdeles :=
    finiteAtThree_line (generalLinearGroup_map_line finiteThree hpar)
  let new_compact := correction * GeneralLinearGroup.map integralEmbedding compact
  have compact_integral : new_compact ∈ finiteIntegralGLLevel 3 :=
    (finiteIntegralGLLevel 3).mul_mem correction_integral ⟨compact, rfl⟩
  have compact_three : GeneralLinearGroup.map finiteThree new_compact =
      GeneralLinearGroup.map finiteThree matrix := by
    dsimp only [new_compact, correction]
    rw [map_mul, finiteAtThree_three, ← map_mul, ← factors]
  have compact_level : new_compact ∈ finiteLevel :=
    finiteLevel_of_integral_of_three new_compact compact_integral (compact_three ▸ original_three)
  refine ⟨parabolic * correction⁻¹, ⟨new_compact, compact_level⟩,
    (lineParabolic FiniteAdeles).mul_mem hpar ((lineParabolic FiniteAdeles).inv_mem correction_line),
    ?_, ?_⟩
  · rw [map_mul, map_inv]
    dsimp only [correction]
    rw [finiteAtThree_three, mul_inv_cancel]
  · change matrix = (parabolic * correction⁻¹) *
      (correction * GeneralLinearGroup.map integralEmbedding compact)
    rw [mul_assoc, inv_mul_cancel_left]
    exact factors

end TernaryPeriodPolynomials.HeckeEigen
