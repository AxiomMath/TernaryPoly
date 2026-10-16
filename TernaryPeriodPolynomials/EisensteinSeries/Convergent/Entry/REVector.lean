module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REEuler
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSphericalPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.AdelicSplit
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.IdeleDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.LatticeMeasure

@[expose] public section


/-!
# R-e: Spherical plane vectors at the opposite matrices

`entryRz` (realization of an arbitrary Hilbert vector), the class-number-one lemma `character_finite_eq_one` (a character trivial on integral units is trivial on all finite ideles), and `finitePlaneVector_planeOpposite`: the plane vector at `w⁻¹u(a,b)π` is `|det B|^b · π(B) v`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem normPower_ne_zero' (t : Adelesˣ) (z : ℂ) : normPower t z ≠ 0 := Complex.exp_ne_zero _

theorem normPower_zero' (t : Adelesˣ) : normPower t 0 = 1 := by simp [normPower]

open Classical in
/-- The realization of a vector of the Hilbert space, zero off the smooth vectors. -/
def entryRz (σ : CuspidalRepresentation) (w : σ.H) (x : BinaryAdelicGL) : ℂ :=
  if h : w ∈ σ.smooth then σ.realize ⟨w, h⟩ x else 0

section Rz

variable {σ : CuspidalRepresentation}

theorem entryRz_of_mem {w : σ.H} (hw : w ∈ σ.smooth) (x : BinaryAdelicGL) :
    entryRz σ w x = σ.realize ⟨w, hw⟩ x := by
  unfold entryRz
  rw [dite_eq_left hw]

theorem entryRz_pi {w : σ.H} (hw : w ∈ σ.smooth) (g x : BinaryAdelicGL) :
    entryRz σ (σ.π g w) x = entryRz σ w (x * g) := by
  rw [entryRz_of_mem (σ.smooth_stable g w hw), entryRz_of_mem hw]
  exact σ.equivariant g ⟨w, hw⟩ x

theorem entryRz_smul {w : σ.H} (hw : w ∈ σ.smooth) (c : ℂ) (x : BinaryAdelicGL) :
    entryRz σ (c • w) x = c * entryRz σ w x := by
  rw [entryRz_of_mem (σ.smooth.smul_mem c hw), entryRz_of_mem hw]
  have h : (⟨c • w, σ.smooth.smul_mem c hw⟩ : σ.smooth) = c • (⟨w, hw⟩ : σ.smooth) :=
    Subtype.ext rfl
  rw [h, map_smul, Pi.smul_apply, smul_eq_mul]

end Rz

/-- A character trivial on the integral units is trivial on all finite ideles (class number one). -/
theorem character_finite_eq_one (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) (t : FiniteAdelesˣ) :
    χ.toMonoidHom (Norm.finiteAdeleUnit t) = 1 := by
  obtain ⟨q, hq, u, rfl⟩ :=
    TernaryPeriodPolynomials.EisensteinRegularization.Helpers.finiteIdele_rational_integral_decomposition t
  have integral : χ.toMonoidHom (Norm.finiteAdeleUnit (Units.map integralEmbedding.toMonoidHom u)) = 1 := by
    rw [finiteAdeleUnit_integral]
    exact hχ u
  have rational : χ.toMonoidHom (Norm.finiteAdeleUnit (FiniteLatticeMeasure.rationalScale q)) = 1 := by
    have split := FiniteLatticeMeasure.rational_decomposition q
    have eq1 := χ.rational q
    have positive : 0 < ((Units.map (algebraMap ℚ ℝ).toMonoidHom q : ℝˣ) : ℝ) := by
      change 0 < (algebraMap ℚ ℝ q.val)
      simpa using hq
    have eq2 : χ.toMonoidHom (realAdeleUnit (Units.map (algebraMap ℚ ℝ).toMonoidHom q) *
        Norm.finiteAdeleUnit (FiniteLatticeMeasure.rationalScale q)) = 1 :=
      (congrArg χ.toMonoidHom split).symm.trans eq1
    rwa [map_mul, χ.positiveReal _ positive, one_mul] at eq2
  rw [FiniteLatticeMeasure.finiteUnit_mul, map_mul]
  exact (congrArg₂ (· * ·) rational integral).trans (mul_one 1)

theorem planeBlockGL_val_apply {R : Type*} [CommRing R] (p : GeneralLinearGroup (Fin 3) R)
    (hp : p ∈ planeParabolic R) (i j : Fin 2) :
    (planeBlockGL p hp).val i j = p.val i.castSucc j.castSucc := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The plane vector at the opposite matrix `w⁻¹ u(a,b) π` is the determinant weight times the translate by the
`GL₂` block. -/
theorem finitePlaneVector_planeOpposite (σ : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) (v : FiniteAdeles × FiniteAdeles) :
    finitePlaneVector σ χ 0 b (planeOppositeStandardMatrix v.1 v.2) vec =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (entryBlock v))) b •
        σ.π (atFinite (entryBlock v)) vec := by
  let c := finitePadicPlaneCoordinates v.1 v.2
  have hg := finitePlaneInductionCoordinates_parabolic _ c
  have hp := (planeInductionParabolic c.first c.second c.scalar c.block).property
  rw [finitePlaneVector_eq χ 0 b hχ hsph hp c.compact hg]
  have hscalar : planeCornerUnit (planeInductionParabolic c.first c.second c.scalar c.block).val hp = c.scalar :=
    Units.ext (planeInduction_scalar_entry c.first c.second c.scalar c.block)
  have hblock : planeBlockGL (planeInductionParabolic c.first c.second c.scalar c.block).val hp = c.block := by
    apply Units.ext
    exact Matrix.ext fun i j => (planeBlockGL_val_apply _ hp i j).trans
      (planeInduction_block_entry c.first c.second c.scalar c.block i j)
  have hχ' := character_finite_eq_one χ hχ
  unfold finitePlaneFactor
  rw [hscalar, hblock, hχ', normPower_zero', one_mul, one_mul]
  rfl

theorem entryRz_planeOpposite (σ : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {vec : σ.H} (hvec : vec ∈ σ.smooth) (hsph : vec ∈ sphericalSubspace σ) (v : FiniteAdeles × FiniteAdeles)
    (y : BinaryAdelicGL) :
    entryRz σ (finitePlaneVector σ χ 0 b (planeOppositeStandardMatrix v.1 v.2) vec) y =
      normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det (entryBlock v))) b *
        entryRz σ vec (y * atFinite (entryBlock v)) := by
  rw [finitePlaneVector_planeOpposite σ χ b hχ hsph, entryRz_smul (σ.smooth_stable _ _ hvec), entryRz_pi hvec]

theorem planeCornerUnit_planeLevi'' {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R)
    (d : Rˣ) (h : planeLevi A d ∈ planeParabolic R) : planeCornerUnit (planeLevi A d) h = d :=
  Units.ext rfl

theorem planeBlockGL_planeLevi'' {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R)
    (d : Rˣ) (h : planeLevi A d ∈ planeParabolic R) : planeBlockGL (planeLevi A d) h = A := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem finitePlaneFactor_planeLevi' (χ : RankOneCharacter) (a b : ℂ)
    (A : GeneralLinearGroup (Fin 2) FiniteAdeles) (d : FiniteAdelesˣ) :
    finitePlaneFactor χ a b (planeLevi A d) (planeLevi_mem A d) =
      χ.toMonoidHom (Norm.finiteAdeleUnit d) * normPower (Norm.finiteAdeleUnit d) a *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det A)) b := by
  unfold finitePlaneFactor
  rw [planeCornerUnit_planeLevi'', planeBlockGL_planeLevi'']

/-- The antidiagonal permutation matrix. -/
def permMatrix (R : Type*) [CommRing R] : GL3 R :=
  ⟨!![0,0,1;0,1,0;1,0,0], !![0,0,1;0,1,0;1,0,0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem permMatrix_mul_self (R : Type*) [CommRing R] : permMatrix R * permMatrix R = 1 := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [permMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem permMatrix_map : GeneralLinearGroup.map integralEmbedding (permMatrix IntegralAdeles) =
    permMatrix FiniteAdeles := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [permMatrix, GeneralLinearGroup.map_apply]

theorem weyl_inv_lineUnipotent_perm {R : Type*} [CommRing R] (a b : R) :
    weyl⁻¹ * lineUnipotent a b * permMatrix R = planeOppositeStandardMatrix a b := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, lineUnipotent, upperUnipotent, permMatrix, planeOppositeStandardMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem weyl_inv_lineUnipotent_eq (a b : FiniteAdeles) :
    weyl⁻¹ * lineUnipotent a b =
      planeOppositeStandardMatrix a b * GeneralLinearGroup.map integralEmbedding (permMatrix IntegralAdeles) := by
  rw [permMatrix_map, ← weyl_inv_lineUnipotent_perm, mul_assoc, permMatrix_mul_self, mul_one]

theorem finitePlaneVector_entry (σ : CuspidalRepresentation) (χ : RankOneCharacter) (b : ℂ)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1)
    {vec : σ.H} (hsph : vec ∈ sphericalSubspace σ) (v : FiniteAdeles × FiniteAdeles)
    (κ : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finitePlaneVector σ χ 0 b (weyl⁻¹ * lineUnipotent v.1 v.2 * GeneralLinearGroup.map integralEmbedding κ) vec =
      finitePlaneVector σ χ 0 b (planeOppositeStandardMatrix v.1 v.2) vec := by
  rw [weyl_inv_lineUnipotent_eq, mul_assoc, ← map_mul, finitePlaneVector_mul_integral χ 0 b hχ hsph]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
