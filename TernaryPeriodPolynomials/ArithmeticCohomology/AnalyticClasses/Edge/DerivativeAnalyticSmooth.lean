module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeAnalyticCalculus

@[expose] public section


/-!
# Smoothness of the ingredients of the real good-line transfer

Scalar tests of the coefficient action of a smoothly varying real matrix are smooth. Hence the
scalar tests `ℓ(ρ_U(x) μ(y) P)` of the canonical cochain are smooth functions of the radical
coordinates `(x, y)`. The matrices of the radical elements and of the diagonal flow of the real
good-line stabilizer are smooth, and the radical coordinate and Levi point of `k · lineMatrix q`
are smooth jointly in the matrix `k` and in the parameters of `q`. The orthogonal matrices form a
compact set, and `k · lineMatrix q` has positive corner for every orthogonal factor of the
Gram–Schmidt decomposition.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {order : WithTop ℕ∞}

/-! ### Matrix-valued smooth maps -/

theorem contDiff_matrix_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M : X → Matrix (Fin 3) (Fin 3) ℝ} (hM : ContDiff ℝ order M) (i j : Fin 3) :
    ContDiff ℝ order (fun x => M x i j) :=
  contDiff_pi.mp (contDiff_pi.mp hM i) j

theorem contDiff_matrix_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M N : X → Matrix (Fin 3) (Fin 3) ℝ} (hM : ContDiff ℝ order M) (hN : ContDiff ℝ order N) :
    ContDiff ℝ order (fun x => M x * N x) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => (contDiff_matrix_entry hM i l).mul (contDiff_matrix_entry hN l j)

theorem contDiff_det3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M : X → Matrix (Fin 3) (Fin 3) ℝ} (hM : ContDiff ℝ order M) :
    ContDiff ℝ order (fun x => (M x).det) := by
  have e := contDiff_matrix_entry hM
  simp only [Matrix.det_fin_three]
  exact ((((((e 0 0).mul (e 1 1)).mul (e 2 2)).sub (((e 0 0).mul (e 1 2)).mul (e 2 1))).sub
    (((e 0 1).mul (e 1 0)).mul (e 2 2))).add (((e 0 1).mul (e 1 2)).mul (e 2 0))).add
    (((e 0 2).mul (e 1 0)).mul (e 2 1)) |>.sub (((e 0 2).mul (e 1 1)).mul (e 2 0))

/-! ### Scalar tests of the coefficient action -/

/-- **Scalar tests of the coefficient action of a smoothly varying real matrix are smooth**, as
soon as the inverse matrix varies smoothly. -/
theorem contDiff_functional_realCoefficient {degree : ℕ} (M : P → RealGL3)
    (inverse : ContDiff ℝ order (fun p => ((M p)⁻¹).val)) (v : HomogeneousPoly degree)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ContDiff ℝ order
      (fun p => functional (realCoefficientComponent degree trivialCharacter (M p) v)) := by
  simp only [realCoefficientComponent_trivial]
  rw [← contDiffOn_univ]
  apply ternary_homogeneousAction_functional_contDiffOn
  · have equal : (fun p => ((GeneralLinearGroup.det
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (M p)) : ℂˣ) : ℂ)⁻¹) =
        fun p => ((((M p)⁻¹).val.det : ℝ) : ℂ) := by
      funext p
      rw [← Units.val_inv_eq_inv_val, ← map_inv, ← map_inv, GeneralLinearGroup.val_det_apply,
        GeneralLinearGroup.val_map_apply]
      exact (RingHom.map_det (algebraMap ℝ ℂ) _).symm
    rw [equal]
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_det3 inverse)).contDiffOn
  · intro row column
    have equal : (fun p => ((GeneralLinearGroup.map (algebraMap ℝ ℂ) (M p))⁻¹ : GL3).val row
        column) = fun p => ((((M p)⁻¹).val row column : ℝ) : ℂ) := by
      funext p
      rw [← map_inv]
      rfl
    rw [equal]
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_matrix_entry inverse row column)).contDiffOn

theorem contDiff_realPlaneRadicalMatrix_inv :
    ContDiff ℝ order (fun x : Fin 2 → ℝ =>
      ((realPlaneRadicalMatrix (Multiplicative.ofAdd x))⁻¹).val) := by
  have equal : (fun x : Fin 2 → ℝ => ((realPlaneRadicalMatrix (Multiplicative.ofAdd x))⁻¹).val) =
      fun x => !![1, 0, -x 0; 0, 1, -x 1; 0, 0, 1] := rfl
  rw [equal]
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one] <;>
    first
    | exact contDiff_const
    | exact (contDiff_apply ℝ ℝ (0 : Fin 2)).neg
    | exact (contDiff_apply ℝ ℝ (1 : Fin 2)).neg

/-- Scalar tests of the upper radical action are smooth in the radical coordinate. -/
theorem contDiff_functional_upperRadical {degree : ℕ} (v : HomogeneousPoly degree)
    (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    ContDiff ℝ order (fun x : Fin 2 → ℝ =>
      functional ((realUpperRadicalRep degree).ρ (Multiplicative.ofAdd x) v)) := by
  exact contDiff_functional_realCoefficient _ contDiff_realPlaneRadicalMatrix_inv v functional

/-- Scalar tests of `μ(y) b` are smooth in `y`. -/
theorem contDiff_functional_upperBinaryValue (b : Binary.HomogeneousPoly (n + 1))
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ContDiff ℝ order (fun y : Fin 2 → ℝ =>
      functional (realUpperBinaryValue n (Multiplicative.ofAdd y) b)) := by
  have equal : (fun y : Fin 2 → ℝ => functional (realUpperBinaryValue n (Multiplicative.ofAdd y) b))
      = fun y => functional (homogeneousLastDivide n (binaryHomogeneousLift (n + 1) b)) -
        (functional ∘ₗ homogeneousLastDivide n)
          ((realUpperRadicalRep (n + 1)).ρ (Multiplicative.ofAdd y)
            (binaryHomogeneousLift (n + 1) b)) := by
    funext y
    change functional (homogeneousLastDivide n (binaryHomogeneousLift (n + 1) b -
      (realUpperRadicalRep (n + 1)).ρ (Multiplicative.ofAdd y)
        (binaryHomogeneousLift (n + 1) b))) = _
    rw [map_sub, map_sub, LinearMap.comp_apply]
  rw [equal]
  exact contDiff_const.sub (contDiff_functional_upperRadical _ _)

/-- The scalar test `ℓ(ρ_U(x) μ(y) b)` of the canonical cochain. -/
def radicalValue (n : ℕ) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (b : Binary.HomogeneousPoly (n + 1)) (x y : Fin 2 → ℝ) : ℂ :=
  functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd x)
    (realUpperBinaryValue n (Multiplicative.ofAdd y) b))

/-- **The scalar tests of the canonical cochain are smooth in the radical coordinates.** -/
theorem contDiff_radicalValue (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (b : Binary.HomogeneousPoly (n + 1)) :
    ContDiff ℝ order (fun xy : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      radicalValue n functional b xy.1 xy.2) := by
  have equal : (fun xy : (Fin 2 → ℝ) × (Fin 2 → ℝ) => radicalValue n functional b xy.1 xy.2) =
      fun xy => ∑ k, (homogeneousBasis n).coord k
          (realUpperBinaryValue n (Multiplicative.ofAdd xy.2) b) *
        functional ((realUpperRadicalRep n).ρ (Multiplicative.ofAdd xy.1)
          (homogeneousBasis n k)) := by
    funext xy
    exact functional_eq_basis_sum (functional ∘ₗ (realUpperRadicalRep n).ρ _) _
  rw [equal]
  exact ContDiff.sum fun k _ =>
    ((contDiff_functional_upperBinaryValue b _).comp contDiff_snd).mul
      ((contDiff_functional_upperRadical _ _).comp contDiff_fst)

/-! ### Matrices of the real good-line stabilizer -/

theorem lineMatrix_radical_val (Y : Fin 2 → ℝ) :
    (lineMatrix (lineRadicalElement Y)).val = !![1, 0, 0; 0, 1, 0; Y 0, Y 1, 1] := by
  rw [lineMatrix_lineRadicalElement]
  rfl

theorem lineMatrix_diagonal_val (s : ℝ) :
    (lineMatrix (lineLeviElement (diagonalFlow s))).val =
      !![Real.exp s, 0, 0; 0, Real.exp (-s), 0; 0, 0, 1] := by
  rw [lineMatrix_lineLeviElement]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, diagonalFlow, diagonalFlowMatrix_val]

theorem contDiff_lineMatrix_radical :
    ContDiff ℝ order (fun Y : Fin 2 → ℝ => (lineMatrix (lineRadicalElement Y)).val) := by
  simp only [lineMatrix_radical_val]
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one] <;>
    first
    | exact contDiff_const
    | exact contDiff_apply ℝ ℝ (0 : Fin 2)
    | exact contDiff_apply ℝ ℝ (1 : Fin 2)

theorem contDiff_lineMatrix_diagonal :
    ContDiff ℝ order (fun s : ℝ => (lineMatrix (lineLeviElement (diagonalFlow s))).val) := by
  simp only [lineMatrix_diagonal_val]
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one] <;>
    first
    | exact contDiff_const
    | exact Real.contDiff_exp
    | exact Real.contDiff_exp.comp contDiff_neg

theorem lineMatrix_mul_val (a b : LineGroup) :
    (lineMatrix (a * b)).val = (lineMatrix a).val * (lineMatrix b).val := by
  rw [map_mul, Units.val_mul]

/-- The last column of `lineMatrix q` is the last unit vector. -/
theorem lineMatrix_last_column (q : LineGroup) (i : Fin 3) :
    (lineMatrix q).val i 2 = if i = 2 then 1 else 0 := by
  rw [lineMatrix_apply, Units.val_mul]
  fin_cases i <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, lineRadicalMatrix, lowerPlaneUnipotent, planeLevi,
      planeBlock]

theorem mul_lineMatrix_corner (k : Matrix (Fin 3) (Fin 3) ℝ) (q : LineGroup) :
    (k * (lineMatrix q).val) 2 2 = k 2 2 := by
  simp [Matrix.mul_apply, lineMatrix_last_column]

theorem gsOrth_mul_lineMatrix_corner_pos (u : ℝ × ℝ) (q : LineGroup) :
    0 < (gsOrth u * lineMatrix q).val 2 2 := by
  rw [Units.val_mul, mul_lineMatrix_corner, gsOrth_val]
  simp only [gsOrthMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
  exact div_pos one_pos (gsRadius_pos u)

/-! ### Orthogonal matrices -/

/-- The orthogonal `3 × 3` real matrices. -/
def orthogonalMatrices : Set (Matrix (Fin 3) (Fin 3) ℝ) := Units.val '' realOrthogonalSet

theorem orthogonalMatrices_isCompact : IsCompact orthogonalMatrices :=
  realOrthogonalSet_isCompact.image Units.continuous_val

theorem gsOrth_val_mem (u : ℝ × ℝ) : (gsOrth u).val ∈ orthogonalMatrices :=
  ⟨gsOrth u, gsOrth_mem u, rfl⟩

theorem det_ne_zero_of_mem_orthogonal {k : Matrix (Fin 3) (Fin 3) ℝ}
    (hk : k ∈ orthogonalMatrices) : k.det ≠ 0 := by
  obtain ⟨g, _, rfl⟩ := hk
  exact g.isUnit.map Matrix.detMonoidHom |>.ne_zero

theorem det_mul_lineMatrix_ne_zero {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k ∈ orthogonalMatrices)
    (q : LineGroup) : (k * (lineMatrix q).val).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero (det_ne_zero_of_mem_orthogonal hk)
    ((lineMatrix q).isUnit.map Matrix.detMonoidHom |>.ne_zero)

/-! ### The radical coordinate and the Levi point of moved stabilizer elements -/

/-- The radical coordinate of `k · L(p)`, as a function of the pair `(k, p)`. -/
def movedRadical (L : P → Matrix (Fin 3) (Fin 3) ℝ) (x : Matrix (Fin 3) (Fin 3) ℝ × P) :
    Fin 2 → ℝ :=
  symmetricRadical (x.1 * L x.2)

/-- The Levi point of `k · L(p)`, as a function of the pair `(k, p)`. -/
def movedPoint (L : P → Matrix (Fin 3) (Fin 3) ℝ) (x : Matrix (Fin 3) (Fin 3) ℝ × P) : ℂ :=
  symmetricPoint (x.1 * L x.2)

theorem contDiff_moved_matrix {L : P → Matrix (Fin 3) (Fin 3) ℝ} (hL : ContDiff ℝ order L) :
    ContDiff ℝ order (fun x : Matrix (Fin 3) (Fin 3) ℝ × P => x.1 * L x.2) :=
  contDiff_matrix_mul contDiff_fst (hL.comp contDiff_snd)

theorem contDiffAt_movedRadical {m : WithTop ℕ∞} {L : P → Matrix (Fin 3) (Fin 3) ℝ}
    (hL : ContDiff ℝ m L) {x : Matrix (Fin 3) (Fin 3) ℝ × P} (hx : (x.1 * L x.2).det ≠ 0) :
    ContDiffAt ℝ m (movedRadical L) x :=
  (contDiffAt_symmetricRadical_of m hx).comp x (contDiff_moved_matrix hL).contDiffAt

theorem contDiffAt_movedPoint {m : WithTop ℕ∞} {L : P → Matrix (Fin 3) (Fin 3) ℝ}
    (hL : ContDiff ℝ m L) {x : Matrix (Fin 3) (Fin 3) ℝ × P} (hx : (x.1 * L x.2).det ≠ 0) :
    ContDiffAt ℝ m (movedPoint L) x :=
  (contDiffAt_symmetricPoint_of m hx).comp x (contDiff_moved_matrix hL).contDiffAt

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem movedPoint_im_pos {L : P → Matrix (Fin 3) (Fin 3) ℝ} {x : Matrix (Fin 3) (Fin 3) ℝ × P}
    (hx : (x.1 * L x.2).det ≠ 0) : 0 < (movedPoint L x).im :=
  symmetricPoint_im_pos hx

/-- The radical part of the relative vertex is the radical coordinate of `k(u) · lineMatrix q`. -/
theorem relativeVertex_left (u : ℝ × ℝ) (q : LineGroup) :
    (relativeVertex u q).left.toAdd = symmetricRadical ((gsOrth u).val * (lineMatrix q).val) := by
  rw [relativeVertex, gsPlaneVertex_radical (gsOrth_mul_lineMatrix_corner_pos u q), Units.val_mul]

/-- The point of the Levi part of the relative vertex is the Levi point of `k(u) · lineMatrix q`. -/
theorem basePoint_relativeVertex_right (u : ℝ × ℝ) (q : LineGroup) :
    basePoint (relativeVertex u q).right =
      symmetricPoint ((gsOrth u).val * (lineMatrix q).val) := by
  rw [basePoint, relativeVertex, gsPlaneVertex_point (gsOrth_mul_lineMatrix_corner_pos u q),
    Units.val_mul]

end TernaryPeriodPolynomials.AnalyticClasses
