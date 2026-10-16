module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.ThreeLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm

@[expose] public section


/-!
# Plane-induced sections as cusp-representation-valued functions

For a plane-induced section `f` (an `IsInduced D .plane cohomologicalPoint` function) and a point
`h`, the restriction `A ↦ |det A|^{-e} f(planeLevi A 1 · h)` is a cusp function of `D.cusp`;
`planeVec D f h` is the unique smooth vector realizing it. We record its behaviour under left
multiplication by plane-parabolic elements and right multiplication by `finiteLevel`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.HeckeEigen

theorem np_mul (t u : Adelesˣ) (z : ℂ) : normPower (t * u) z = normPower t z * normPower u z := by
  have ht : (adeleNorm t : ℝ) ≠ 0 := ne_of_gt (adeleNorm_pos t)
  have hu : (adeleNorm u : ℝ) ≠ 0 := ne_of_gt (adeleNorm_pos u)
  simp only [normPower, map_mul, NNReal.coe_mul, Real.log_mul ht hu,
    Complex.ofReal_add, mul_add, Complex.exp_add]

theorem np_neg (t : Adelesˣ) (z : ℂ) : normPower t z * normPower t (-z) = 1 := by
  simp only [normPower, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero]

theorem np_one (z : ℂ) : normPower 1 z = 1 := by
  simp [normPower]

theorem np_of_norm_one {t : Adelesˣ} (ht : adeleNorm t = 1) (z : ℂ) : normPower t z = 1 := by
  simp [normPower, ht]

theorem planeLevi_one_one : planeLevi (1 : BinaryAdelicGL) (1 : Adelesˣ) = 1 :=
  (planeLeviHom Adeles).map_one

variable {n : ℕ} (D : InducingData n)

/-- The plane cohomological exponent `(n+3)/2 + (1/2 + s/3)` at `s = -3/2`. -/
def planeExp (n : ℕ) : ℂ := ((n : ℂ) + 3) / 2 + inductionExponent .plane cohomologicalPoint

/-- The cusp function attached to a plane-induced section at a point. -/
def planeCusp (n : ℕ) (f : AdelicGL → ℂ) (h : AdelicGL) : BinaryAdelicGL → ℂ :=
  fun A => normPower (GeneralLinearGroup.det A) (-planeExp n) * f (planeLevi A 1 * h)

theorem planeCusp_mem {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (h : AdelicGL) : planeCusp n f h ∈ cuspFunctions D.cusp :=
  hf.2.2.2.2.2 h

open Classical in
/-- The smooth vector realizing `planeCusp n f h`. -/
def planeVec (f : AdelicGL → ℂ) (h : AdelicGL) : D.cusp.smooth :=
  if hm : planeCusp n f h ∈ cuspFunctions D.cusp then (LinearMap.mem_range.mp hm).choose else 0

variable {D}

theorem realize_planeVec {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (h : AdelicGL) : D.cusp.realize (planeVec D f h) = planeCusp n f h := by
  have hm := planeCusp_mem D hf h
  rw [planeVec, dite_eq_left hm]
  exact (LinearMap.mem_range.mp hm).choose_spec

theorem planeVec_eq {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (h : AdelicGL) (w : D.cusp.smooth) (hw : D.cusp.realize w = planeCusp n f h) :
    planeVec D f h = w :=
  D.cusp.injective ((realize_planeVec hf h).trans hw.symm)

theorem planeVec_value {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (h : AdelicGL) : f h = D.cusp.realize (planeVec D f h) 1 := by
  rw [realize_planeVec hf h, planeCusp, map_one, np_one, one_mul, planeLevi_one_one, one_mul]

theorem planeVec_level {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (h : AdelicGL) (k : finiteLevel) : planeVec D f (h * atFinite k.val) = planeVec D f h := by
  apply planeVec_eq hf
  rw [realize_planeVec hf]
  funext A
  simp only [planeCusp]
  rw [← mul_assoc, hf.2.1 k]

theorem plane_parabolic_identity (A B : BinaryAdelicGL) (a b : Adeles) (s : Adelesˣ) :
    planeLevi A 1 * (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1)) =
      planeUnipotent (A.val 0 0 * a + A.val 0 1 * b) (A.val 1 0 * a + A.val 1 1 * b) *
        (planeLevi 1 s * planeLevi (A * B) 1) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] <;> ring

/-- **Left plane-parabolic equivariance of the realizing vectors.** -/
theorem planeVec_parabolic {f : AdelicGL → ℂ} (hf : IsInduced D .plane cohomologicalPoint f)
    (a b : Adeles) (s : Adelesˣ) (B : BinaryAdelicGL) (h : AdelicGL) :
    planeVec D f (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) * h) =
      (D.chi.toMonoidHom s * normPower s (-2 * inductionExponent .plane cohomologicalPoint) *
        normPower (GeneralLinearGroup.det B) (planeExp n)) •
      ⟨D.cusp.π B (planeVec D f h), D.cusp.smooth_stable B _ (planeVec D f h).property⟩ := by
  apply planeVec_eq hf
  funext A
  rw [map_smul, Pi.smul_apply, D.cusp.equivariant, realize_planeVec hf, smul_eq_mul]
  simp only [planeCusp]
  have h1 : planeLevi A 1 * (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1) * h) =
      planeUnipotent (A.val 0 0 * a + A.val 0 1 * b) (A.val 1 0 * a + A.val 1 1 * b) *
        (planeLevi 1 s * (planeLevi (A * B) 1 * h)) := by
    rw [← mul_assoc, plane_parabolic_identity, mul_assoc, mul_assoc]
  rw [h1, hf.2.2.2.1, hf.2.2.2.2.1, map_mul, np_mul]
  have key := np_neg (GeneralLinearGroup.det B) (planeExp n)
  linear_combination (D.chi.toMonoidHom s *
    normPower s (-2 * inductionExponent .plane cohomologicalPoint) *
    normPower (GeneralLinearGroup.det A) (-planeExp n) *
    f (planeLevi (A * B) 1 * h)) * key

end TernaryPeriodPolynomials.HeckeEigen
