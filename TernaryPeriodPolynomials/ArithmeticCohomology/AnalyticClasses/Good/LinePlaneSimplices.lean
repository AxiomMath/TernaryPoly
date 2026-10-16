module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DetNormalizedSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineGramSchmidt
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneOpenProjection

@[expose] public section


/-!
# Gram–Schmidt vertices as points of the real plane group

A plane-parabolic matrix `p` with positive corner is a positive scalar multiple of the image of a
unique element of the real plane group `ℝ² ⋊ GL₂(ℝ)` (corner one): `planeNormalize p`. The
determinant-normalized source does not see positive scalings of single vertices, so on simplices of
Gram–Schmidt vertices it is the source on simplices of the real plane group, which are governed by
Codexiom's real-plane machinery. The normalization is equivariant for the Levi elements
`planeLevi B 1`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The positive scale normalizing the corner of a matrix to one. -/
def cornerScale (p : RealGL3) : ℝˣ :=
  if h : p.val 2 2 ≠ 0 then Units.mk0 (|p.val 2 2|⁻¹) (inv_ne_zero (abs_ne_zero.mpr h)) else 1

theorem cornerScale_val {p : RealGL3} (h : p.val 2 2 ≠ 0) :
    (cornerScale p : ℝ) = |p.val 2 2|⁻¹ := by
  rw [cornerScale, dite_eq_left h]
  rfl

theorem cornerScale_pos (p : RealGL3) : 0 < (cornerScale p : ℝ) := by
  by_cases h : p.val 2 2 ≠ 0
  · rw [cornerScale_val h]
    exact inv_pos.mpr (abs_pos.mpr h)
  · rw [cornerScale, dite_eq_right h]
    exact one_pos

theorem scalar_mul_val_apply (unit : ℝˣ) (p : RealGL3) (i j : Fin 3) :
    (GeneralLinearGroup.scalar (Fin 3) unit * p).val i j = (unit : ℝ) * p.val i j := by
  rw [Units.val_mul, scalar_val_three, Matrix.scalar_apply, Matrix.diagonal_mul]

/-- The real-plane point of a plane-parabolic matrix. -/
def planeNormalize (p : RealGL3) : RealPlaneGroup :=
  realPlaneOpenProjection (GeneralLinearGroup.scalar (Fin 3) (cornerScale p) * p)

theorem realPlaneMatrix_planeNormalize {p : RealGL3} (hp : p ∈ planeParabolic ℝ)
    (positive : 0 < p.val 2 2) :
    realPlaneMatrix (planeNormalize p) = GeneralLinearGroup.scalar (Fin 3) (cornerScale p) * p := by
  have h20 : p.val 2 0 = 0 := hp.1
  have h21 : p.val 2 1 = 0 := hp.2
  have scale := cornerScale_val positive.ne'
  rw [abs_of_pos positive] at scale
  set q := GeneralLinearGroup.scalar (Fin 3) (cornerScale p) * p with hq
  have q20 : q.val 2 0 = 0 := by rw [hq, scalar_mul_val_apply, h20, mul_zero]
  have q21 : q.val 2 1 = 0 := by rw [hq, scalar_mul_val_apply, h21, mul_zero]
  have q22 : q.val 2 2 = 1 := by rw [hq, scalar_mul_val_apply, scale, inv_mul_cancel₀ positive.ne']
  apply Units.ext
  rw [planeNormalize, ← hq, realPlaneOpenProjection_matrix q (by rw [q22]; exact one_ne_zero)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [q20, q21, q22]

theorem planeNormalize_levi (B : BinaryRealGL) {p : RealGL3} (positive : 0 < p.val 2 2) :
    planeNormalize (planeLevi B 1 * p) = SemidirectProduct.inr B * planeNormalize p := by
  have corner : (planeLevi B 1 * p).val 2 2 = p.val 2 2 := by
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    simp [planeLevi, planeBlock]
  have scaleEq : cornerScale (planeLevi B 1 * p) = cornerScale p := by
    simp only [cornerScale, corner]
  unfold planeNormalize
  rw [scaleEq, ← mul_assoc, GeneralLinearGroup.scalar_commute, mul_assoc,
    ← realPlaneMatrix_inr]
  apply realPlaneOpenProjection_equivariant
  rw [scalar_mul_val_apply]
  exact mul_ne_zero (cornerScale_pos p).ne' positive.ne'

/-- The real-plane point of the Gram–Schmidt vertex. -/
def gsPlaneVertex (y : RealGL3) : RealPlaneGroup := planeNormalize (gsVertex y)

theorem gsPlaneVertex_levi (B : BinaryRealGL) (y : RealGL3)
    (positive : 0 < (gsVertex y).val 2 2) :
    gsPlaneVertex (planeLevi B 1 * y) = SemidirectProduct.inr B * gsPlaneVertex y := by
  unfold gsPlaneVertex
  rw [gsVertex_plane_mul (planeLevi_mem B 1), planeNormalize_levi B positive]

theorem abs_det_gsVertex (y : RealGL3) : |(gsVertex y).val.det| = |y.val.det| := by
  rw [gsVertex, Units.val_mul, Matrix.det_mul, abs_mul]
  have orthogonal := gsOrth_inv_orthogonal (gsChart y)
  have square : ((gsOrth (gsChart y))⁻¹.val.det) ^ 2 = 1 := by
    have := congrArg Matrix.det orthogonal
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [sq]
    exact this
  have unit : |((gsOrth (gsChart y))⁻¹.val.det)| = 1 := by
    rcases sq_eq_one_iff.mp square with h | h <;> rw [h] <;> norm_num
  rw [unit, mul_one]

variable {n : ℕ}

/-- **The normalized source on Gram–Schmidt vertices is the source on real-plane simplices.** -/
theorem normalizedSource_gsVertex (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (V : Fin 3 → RealGL3) (hp : ∀ i, gsVertex (V i) ∈ planeParabolic ℝ)
    (positive : ∀ i, 0 < (gsVertex (V i)).val 2 2) :
    sourcePlaneCuspidalValues data (normalizedSource source)
        (normalizedSource_cocycle data trivial source cocycle) (fun i => gsVertex (V i)) 1 =
      sourcePlaneCuspidalValues data (normalizedSource source)
        (normalizedSource_cocycle data trivial source cocycle)
        (fun i => realPlaneMatrix (gsPlaneVertex (V i))) 1 := by
  apply Subtype.ext
  funext argument
  rw [sourcePlaneCuspidalValues_apply, sourcePlaneCuspidalValues_apply]
  congr 1
  have vertices : (fun i => realPlaneMatrix (gsPlaneVertex (V i))) =
      fun i => GeneralLinearGroup.scalar (Fin 3) (cornerScale (gsVertex (V i))) *
        gsVertex (V i) := by
    funext i
    exact realPlaneMatrix_planeNormalize (hp i) (positive i)
  rw [vertices, normalizedSource_scalar _ _ _ (fun i => cornerScale_pos _)]

/-- **The source and the normalized source agree on unimodular vertices.** -/
theorem sourcePlaneCuspidalValues_normalized (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (V : Fin 3 → RealGL3)
    (unit : ∀ i, |(V i).val.det| = 1) (base : AdelicGL) :
    sourcePlaneCuspidalValues data source cocycle V base =
      sourcePlaneCuspidalValues data (normalizedSource source)
        (normalizedSource_cocycle data trivial source cocycle) V base := by
  apply Subtype.ext
  funext argument
  rw [sourcePlaneCuspidalValues_apply, sourcePlaneCuspidalValues_apply,
    normalizedSource_eq_of_abs_det _ _ unit]

end TernaryPeriodPolynomials.AnalyticClasses
