module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.SourceCentralScalar
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothTransport

@[expose] public section


/-!
# The determinant-normalized source

For a plane source cocycle `c` put `ν(y) = |det y|^{-1/3} y` and `c' = c ∘ ν` (vertexwise).
Since positive central scalings of all vertices do not change `c` and `ν` is multiplicative up to
such scalars, `c'` is again a plane source cocycle. It agrees with `c` on vertices of determinant
`±1` (in particular on all the good-line and Gram–Schmidt vertices), and it is invariant under
positive scalings of the individual vertices. This removes the corner (central) direction of the
plane parabolic: `c'` on a simplex of plane-parabolic matrices only depends on the simplex of their
corner-one normalizations, i.e. on the real plane group `ℝ² ⋊ GL₂(ℝ)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The positive scale `|det A|^{-1/3}` of a real matrix. -/
def matrixDetScale (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.exp (-(Real.log A.det) / 3)

theorem matrixDetScale_pos (A : Matrix (Fin 3) (Fin 3) ℝ) : 0 < matrixDetScale A := Real.exp_pos _

/-- The determinant scale as a positive real unit. -/
def detScale (y : RealGL3) : ℝˣ := Units.mk0 (matrixDetScale y.val) (matrixDetScale_pos _).ne'

theorem detScale_val (y : RealGL3) : (detScale y : ℝ) = matrixDetScale y.val := rfl

theorem detScale_pos (y : RealGL3) : 0 < (detScale y : ℝ) := matrixDetScale_pos _

theorem det_ne_zero_real (y : RealGL3) : y.val.det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit |>.ne_zero

theorem matrixDetScale_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    matrixDetScale (A * B) = matrixDetScale A * matrixDetScale B := by
  unfold matrixDetScale
  rw [← Real.exp_add, Matrix.det_mul, Real.log_mul hA hB]
  ring_nf

theorem detScale_mul (y z : RealGL3) : detScale (y * z) = detScale y * detScale z := by
  apply Units.ext
  simp only [detScale_val, Units.val_mul]
  exact matrixDetScale_mul _ _ (det_ne_zero_real y) (det_ne_zero_real z)

theorem detScale_of_abs_det (y : RealGL3) (unit : |y.val.det| = 1) : detScale y = 1 := by
  apply Units.ext
  rw [detScale_val, matrixDetScale, ← Real.log_abs, unit, Real.log_one]
  simp

/-- The determinant normalization `ν(y) = |det y|^{-1/3} y`. -/
def detNormalize (y : RealGL3) : RealGL3 := GeneralLinearGroup.scalar (Fin 3) (detScale y) * y

theorem detNormalize_of_abs_det (y : RealGL3) (unit : |y.val.det| = 1) : detNormalize y = y := by
  rw [detNormalize, detScale_of_abs_det y unit, map_one, one_mul]

theorem detNormalize_mul (h y : RealGL3) :
    detNormalize (h * y) =
      GeneralLinearGroup.scalar (Fin 3) (detScale h) * (h * detNormalize y) := by
  unfold detNormalize
  rw [detScale_mul, map_mul, mul_assoc, ← mul_assoc h, ← GeneralLinearGroup.scalar_commute,
    mul_assoc]

theorem scalar_val_three (unit : ℝˣ) :
    (GeneralLinearGroup.scalar (Fin 3) unit).val = Matrix.scalar (Fin 3) (unit : ℝ) := by
  rw [GeneralLinearGroup.coe_scalar]

theorem matrixDetScale_scalar (unit : ℝˣ) (positive : 0 < (unit : ℝ)) :
    matrixDetScale (Matrix.scalar (Fin 3) (unit : ℝ)) = (unit : ℝ)⁻¹ := by
  rw [matrixDetScale, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Real.log_pow]
  rw [show -(((3 : ℕ) : ℝ) * Real.log (unit : ℝ)) / 3 = -Real.log (unit : ℝ) by push_cast; ring,
    Real.exp_neg, Real.exp_log positive]

theorem detScale_scalar_mul (unit : ℝˣ) (positive : 0 < (unit : ℝ)) (y : RealGL3) :
    detScale (GeneralLinearGroup.scalar (Fin 3) unit * y) = unit⁻¹ * detScale y := by
  rw [detScale_mul]
  congr 1
  apply Units.ext
  rw [detScale_val, scalar_val_three, matrixDetScale_scalar unit positive, Units.val_inv_eq_inv_val]

/-- **Positive scalings of a vertex do not change its normalization.** -/
theorem detNormalize_scalar_mul (unit : ℝˣ) (positive : 0 < (unit : ℝ)) (y : RealGL3) :
    detNormalize (GeneralLinearGroup.scalar (Fin 3) unit * y) = detNormalize y := by
  unfold detNormalize
  rw [detScale_scalar_mul unit positive, ← mul_assoc, ← map_mul]
  congr 3
  rw [mul_comm, mul_inv_cancel_left]

variable {n : ℕ}

/-- The determinant-normalized source. -/
def normalizedSource (source : SourceCochain n) : SourceCochain n :=
  fun vertices argument => source (fun index => detNormalize (vertices index)) argument

theorem normalizedSource_apply (source : SourceCochain n) (vertices : Fin 3 → RealGL3)
    (argument : AdelicGL) :
    normalizedSource source vertices argument =
      source (fun index => detNormalize (vertices index)) argument := rfl

theorem normalizedSource_eq_of_abs_det (source : SourceCochain n) (vertices : Fin 3 → RealGL3)
    (unit : ∀ index, |(vertices index).val.det| = 1) (argument : AdelicGL) :
    normalizedSource source vertices argument = source vertices argument := by
  rw [normalizedSource_apply]
  congr 1
  funext index
  exact detNormalize_of_abs_det _ (unit index)

theorem normalizedSource_scalar (source : SourceCochain n) (vertices : Fin 3 → RealGL3)
    (scalars : Fin 3 → ℝˣ) (positive : ∀ index, 0 < (scalars index : ℝ)) (argument : AdelicGL) :
    normalizedSource source
        (fun index => GeneralLinearGroup.scalar (Fin 3) (scalars index) * vertices index) argument =
      normalizedSource source vertices argument := by
  simp only [normalizedSource_apply, detNormalize_scalar_mul _ (positive _)]

/-- The matrix-level normalization. -/
def matrixDetNormalize (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrixDetScale A • A

theorem matrixDetNormalize_det_ne_zero {A : Matrix (Fin 3) (Fin 3) ℝ} (h : A.det ≠ 0) :
    (matrixDetNormalize A).det ≠ 0 := by
  rw [matrixDetNormalize, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (matrixDetScale_pos A).ne') h

theorem invertibleMatrix_matrixDetNormalize {A : Matrix (Fin 3) (Fin 3) ℝ} (h : A.det ≠ 0) :
    invertibleMatrix (matrixDetNormalize A) = detNormalize (invertibleMatrix A) := by
  apply Units.ext
  rw [HeckeTranslate.SmoothTransport.invertibleMatrix_val (matrixDetNormalize_det_ne_zero h),
    detNormalize, Units.val_mul, scalar_val_three, detScale_val,
    HeckeTranslate.SmoothTransport.invertibleMatrix_val h, matrixDetNormalize,
    Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]

theorem matrixDetNormalize_contDiffOn :
    ContDiffOn ℝ ⊤ matrixDetNormalize {A : Matrix (Fin 3) (Fin 3) ℝ | A.det ≠ 0} := by
  have hdet : ContDiff ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det) := by
    simp only [Matrix.det_fin_three]
    fun_prop
  have hlog : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => Real.log A.det)
      {A : Matrix (Fin 3) (Fin 3) ℝ | A.det ≠ 0} :=
    hdet.contDiffOn.log (fun _ membership => membership)
  have hscale : ContDiffOn ℝ ⊤ matrixDetScale {A : Matrix (Fin 3) (Fin 3) ℝ | A.det ≠ 0} :=
    Real.contDiff_exp.comp_contDiffOn ((hlog.neg).div_const 3)
  exact hscale.smul contDiffOn_id

/-- The vertex map normalizing all but the last vertex. -/
def vertexDetNormalize {k : ℕ} (x : Fin (k + 1) → RealGL3) : Fin (k + 1) → RealGL3 :=
  fun i => if i = Fin.last k then x i else detNormalize (x i)

/-- The matrix-level vertex normalization. -/
def matrixVertexDetNormalize {k : ℕ} (A : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ) :
    Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun i => if i = Fin.last k then A i else matrixDetNormalize (A i)

/-- **Smoothness is preserved by normalizing all but the last vertex.** -/
theorem Smooth.comp_vertexDetNormalize {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : (Fin (k + 1) → RealGL3) → E) (hF : Smooth F) :
    Smooth (fun x => F (vertexDetNormalize x)) := by
  rw [Smooth] at hF ⊢
  have hmap : ContDiffOn ℝ ⊤ (matrixVertexDetNormalize (k := k))
      {A : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0} := by
    apply contDiffOn_pi.mpr
    intro i
    by_cases hi : i = Fin.last k
    · simp only [matrixVertexDetNormalize, hi, ite_true]
      exact (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (Fin.last k)).contDiffOn
    · simp only [matrixVertexDetNormalize, hi, ite_false]
      exact matrixDetNormalize_contDiffOn.comp
        (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) i).contDiffOn (fun A hA => hA i)
  have hmapsTo : Set.MapsTo (matrixVertexDetNormalize (k := k))
      {A : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0}
      {A : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0} := by
    intro A hA i
    by_cases hi : i = Fin.last k
    · simp only [matrixVertexDetNormalize, hi, ite_true]
      exact hA _
    · simp only [matrixVertexDetNormalize, hi, ite_false]
      exact matrixDetNormalize_det_ne_zero (hA i)
  refine (hF.comp hmap hmapsTo).congr (fun A hA => ?_)
  simp only [Function.comp]
  congr 1
  funext i
  by_cases hi : i = Fin.last k
  · simp only [vertexDetNormalize, matrixVertexDetNormalize, hi, ite_true]
  · simp only [vertexDetNormalize, matrixVertexDetNormalize, hi, ite_false,
      invertibleMatrix_matrixDetNormalize (hA i)]

/-- **The determinant-normalized source is a plane source cocycle.** -/
theorem normalizedSource_cocycle (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source) :
    IsSourceCocycle data .plane (normalizedSource source) := by
  refine ⟨fun x m => cocycle.1 _ m, ?_, ?_, ?_⟩
  · intro m a
    obtain ⟨v, smooth, realizes⟩ := cocycle.2.1 m a
    refine ⟨fun x => v (vertexDetNormalize x), Smooth.comp_vertexDetNormalize _ smooth, ?_⟩
    intro x A
    rw [realizes]
    have last : vertexDetNormalize x (Fin.last 3) = x (Fin.last 3) := by
      simp [vertexDetNormalize]
    have first : (fun i : Fin 3 => vertexDetNormalize x i.castSucc) =
        fun i => detNormalize (x i.castSucc) := by
      funext i
      simp only [vertexDetNormalize, Fin.castSucc_ne_last i, ite_false]
    rw [last, first]
    rfl
  · intro h x g
    rw [normalizedSource_apply, normalizedSource_apply]
    simp only [detNormalize_mul]
    rw [source_scalar_invariant data trivial source cocycle (detScale h) (detScale_pos h)
      (fun index => h * detNormalize (x index)), cocycle.2.2.1]
  · intro x g
    have tuple (i j k : Fin 4) :
        (fun index => detNormalize ((![x i, x j, x k] : Fin 3 → RealGL3) index)) =
          ![detNormalize (x i), detNormalize (x j), detNormalize (x k)] := by
      funext index
      fin_cases index <;> rfl
    simp only [normalizedSource_apply, tuple]
    exact cocycle.2.2.2 (fun i => detNormalize (x i)) g

theorem normalizedSource_diagonal (source : SourceCochain n)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0) :
    ∀ vertex argument, normalizedSource source (fun _ => vertex) argument = 0 :=
  fun vertex argument => diagonal (detNormalize vertex) argument

end TernaryPeriodPolynomials.AnalyticClasses
