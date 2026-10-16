module

public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions.Height
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal ENNReal


noncomputable section

namespace TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers

theorem finiteNorm_pos (t : FiniteAdelesˣ) : 0 < (finiteNorm t : ℝ) := by
  exact_mod_cast addEquivAddHaarChar_pos (ContinuousAddEquiv.mulLeft t)

theorem adeleNorm_pos (t : Adelesˣ) : 0 < (adeleNorm t : ℝ) := by
  exact_mod_cast addEquivAddHaarChar_pos (ContinuousAddEquiv.mulLeft t)

theorem integralVectors_preserved (k : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (vector : Fin 3 → FiniteAdeles) (hv : vector ∈ integralVectors) :
    (GeneralLinearGroup.map integralEmbedding k).val.mulVec vector ∈ integralVectors := by
  classical
  have hv' : ∀ row, ∃ entry, integralEmbedding entry = vector row := by
    intro row
    exact hv row (Set.mem_univ row)
  choose entries he using hv'
  intro row _
  refine ⟨∑ column, k.val row column * entries column, ?_⟩
  simp only [map_sum, map_mul, mulVec, dotProduct, GeneralLinearGroup.map_apply]
  simp only [he]

theorem integralVectors_image (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finiteMatrixEquiv (GeneralLinearGroup.map integralEmbedding k) '' integralVectors =
      integralVectors := by
  apply Set.Subset.antisymm
  · rintro _ ⟨vector, hv, rfl⟩
    exact integralVectors_preserved k vector hv
  · intro vector hv
    refine ⟨(finiteMatrixEquiv (GeneralLinearGroup.map integralEmbedding k)).symm vector,
      ?_, (finiteMatrixEquiv _).apply_symm_apply vector⟩
    exact integralVectors_preserved k⁻¹ vector hv

theorem rowLattice_right_integral (g : FiniteGL)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    rowLattice (g * GeneralLinearGroup.map integralEmbedding k) = rowLattice g := by
  have he : (finiteMatrixEquiv (g * GeneralLinearGroup.map integralEmbedding k) :
      (Fin 3 → FiniteAdeles) → (Fin 3 → FiniteAdeles)) =
      finiteMatrixEquiv g ∘ finiteMatrixEquiv (GeneralLinearGroup.map integralEmbedding k) := by
    funext vector
    change (g.val * (GeneralLinearGroup.map integralEmbedding k).val).mulVec vector =
      g.val.mulVec ((GeneralLinearGroup.map integralEmbedding k).val.mulVec vector)
    exact (mulVec_mulVec _ _ _).symm
  unfold rowLattice
  rw [he, Set.image_comp, integralVectors_image]

theorem rowMass_right_integral (g : FiniteGL)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    rowMass (g * GeneralLinearGroup.map integralEmbedding k) = rowMass g := by
  simp only [rowMass, rowLattice_right_integral]

theorem rowLattice_one : rowLattice (1 : FiniteGL) = Set.range integralEmbedding := by
  ext value
  rw [rowLattice_mem]
  change (∃ vector ∈ integralVectors,
    ((1 : Matrix (Fin 3) (Fin 3) FiniteAdeles).mulVec vector) 2 = value) ↔ _
  simp only [one_mulVec]
  constructor
  · rintro ⟨vector, hv, he⟩
    have hv' := hv 2 (Set.mem_univ 2)
    simpa only [← he] using hv'
  · rintro ⟨entry, rfl⟩
    refine ⟨fun _ => integralEmbedding entry, ?_, ?_⟩
    · intro row _
      exact ⟨entry, rfl⟩
    · rfl

theorem rowMass_integral (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    rowMass (GeneralLinearGroup.map integralEmbedding k) = 1 := by
  rw [← one_mul (GeneralLinearGroup.map integralEmbedding k), rowMass_right_integral]
  simp [rowMass, rowLattice_one, Measure.real, finiteMeasure_integralLattice]

theorem finiteNorm_det_integral (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    finiteNorm (GeneralLinearGroup.det (GeneralLinearGroup.map integralEmbedding k)) = 1 := by
  rw [GeneralLinearGroup.map_det, finiteNorm_integral]

def rowSquare (g : RealGL3) : ℝ := ∑ column, g.val 2 column ^ 2

theorem rowSquare_pos (g : RealGL3) : 0 < rowSquare g := by
  have hnonneg : 0 ≤ rowSquare g := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_contra hpos
  have hzero : rowSquare g = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  have hrow : ∀ column, g.val 2 column = 0 := by
    intro column
    have hle : g.val 2 column ^ 2 ≤ rowSquare g :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ column)
    nlinarith [sq_nonneg (g.val 2 column)]
  have he := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2) g.val_inv
  simp only [mul_apply, hrow, zero_mul, Finset.sum_const_zero, one_apply_eq] at he
  norm_num at he

theorem rowSquare_scalar (g other : RealGL3) (scalar : ℝ)
    (he : ∀ column, other.val 2 column = scalar * g.val 2 column) :
    rowSquare other = scalar ^ 2 * rowSquare g := by
  simp only [rowSquare, he, mul_pow, Finset.mul_sum]

theorem rowSquare_orthogonal (g : RealGL3) (hg : g.val.transpose * g.val = 1) :
    rowSquare g = 1 := by
  have ht : g.val.transpose = g.inv := by
    calc
      g.val.transpose = g.val.transpose * (g.val * g.inv) := by rw [g.val_inv, mul_one]
      _ = g.inv := by rw [← mul_assoc, hg, one_mul]
  have he := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2)
    (show g.val * g.val.transpose = 1 by rw [ht, g.val_inv])
  simpa only [rowSquare, mul_apply, transpose_apply, ← sq, one_apply_eq] using he

theorem determinant_orthogonal (g : RealGL3) (hg : g.val.transpose * g.val = 1) :
    |(GeneralLinearGroup.det g).val| = 1 := by
  have he := congrArg Matrix.det hg
  rw [det_mul, det_transpose, det_one] at he
  change |g.val.det| = 1
  nlinarith [sq_abs g.val.det, abs_nonneg g.val.det]

def heightValue (g : AdelicGL) : ℝ :=
  Real.log (adeleNorm (GeneralLinearGroup.det g) : ℝ) -
    (3 / 2 : ℝ) * Real.log (rowSquare (realGroup g)) -
    3 * Real.log (rowMass (finiteGroup g))

theorem height_left (p g : AdelicGL) (t : Adelesˣ)
    (he : ∀ column, (p * g).val 2 column = t.val * g.val 2 column) :
    heightValue (p * g) = Real.log (adeleNorm (GeneralLinearGroup.det p) : ℝ) -
      3 * Real.log (adeleNorm t : ℝ) + heightValue g := by
  have hr : ∀ column, (realGroup (p * g)).val 2 column =
      (realPart t).val * (realGroup g).val 2 column := by
    intro column
    exact congrArg Prod.fst (he column)
  have hf : ∀ column, (finiteGroup (p * g)).val 2 column =
      (finitePart t).val * (finiteGroup g).val 2 column := by
    intro column
    exact congrArg Prod.snd (he column)
  have ht : (realPart t).val ≠ 0 := Units.ne_zero _
  have hlog : Real.log (adeleNorm t : ℝ) = Real.log (realPart t).val +
      Real.log (finiteNorm (finitePart t) : ℝ) := by
    rw [adeleNorm_parts, Real.log_mul (abs_ne_zero.mpr ht)
      (ne_of_gt (finiteNorm_pos _)), Real.log_abs]
  unfold heightValue
  rw [map_mul, map_mul, NNReal.coe_mul,
    Real.log_mul (ne_of_gt (adeleNorm_pos _)) (ne_of_gt (adeleNorm_pos _)),
    rowSquare_scalar _ _ _ hr,
    Real.log_mul (pow_ne_zero _ ht) (ne_of_gt (rowSquare_pos _)), Real.log_pow,
    rowMass_scalar _ _ _ hf,
    Real.log_mul (ne_of_gt (finiteNorm_pos _)) (ne_of_gt (rowMass_pos _)), hlog]
  ring

theorem planeLevi_det {R : Type*} [CommRing R]
    (A : GeneralLinearGroup (Fin 2) R) (t : Rˣ) :
    GeneralLinearGroup.det (planeLevi A t) = GeneralLinearGroup.det A * t := by
  apply Units.ext
  change (planeBlock A.val t.val).det = A.val.det * t.val
  simp [planeBlock, det_fin_three, det_fin_two]
  ring

theorem planeUnipotent_det {R : Type*} [CommRing R] (a b : R) :
    GeneralLinearGroup.det (planeUnipotent a b) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.det, planeUnipotent, det_fin_three]

theorem height_unipotent (a b : Adeles) (g : AdelicGL) :
    heightValue (planeUnipotent a b * g) = heightValue g := by
  have he : ∀ column, (planeUnipotent a b * g).val 2 column =
      (1 : Adelesˣ).val * g.val 2 column := by
    intro column
    simp [planeUnipotent, mul_apply, Fin.sum_univ_three]
  rw [height_left _ _ 1 he, planeUnipotent_det]
  simp

theorem height_scalar (t : Adelesˣ) (g : AdelicGL) :
    heightValue (planeLevi 1 t * g) = -2 * Real.log (adeleNorm t : ℝ) +
      heightValue g := by
  have he : ∀ column, (planeLevi 1 t * g).val 2 column = t.val * g.val 2 column := by
    intro column
    simp [planeLevi, planeBlock, mul_apply, Fin.sum_univ_three]
  rw [height_left _ _ t he, planeLevi_det, map_one, one_mul]
  ring

theorem height_binary (A : BinaryAdelicGL) (g : AdelicGL) :
    heightValue (planeLevi A 1 * g) =
      Real.log (adeleNorm (GeneralLinearGroup.det A) : ℝ) + heightValue g := by
  have he : ∀ column, (planeLevi A 1 * g).val 2 column =
      (1 : Adelesˣ).val * g.val 2 column := by
    intro column
    simp [planeLevi, planeBlock, mul_apply, Fin.sum_univ_three]
  rw [height_left _ _ 1 he, planeLevi_det, mul_one]
  simp

theorem realGroup_atInfinity (g : RealGL3) : realGroup (atInfinity g) = g := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem finiteGroup_atInfinity (g : RealGL3) : finiteGroup (atInfinity g) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem realGroup_atFinite (g : FiniteGL) : realGroup (atFinite g) = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem finiteGroup_atFinite (g : FiniteGL) : finiteGroup (atFinite g) = g := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem height_right_integral (g : AdelicGL)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    heightValue (g * atFinite (GeneralLinearGroup.map integralEmbedding k)) =
      heightValue g := by
  have hnorm : adeleNorm (GeneralLinearGroup.det
      (atFinite (GeneralLinearGroup.map integralEmbedding k))) = 1 := by
    apply NNReal.coe_injective
    rw [adeleNorm_parts, realPart_det, finitePart_det,
      realGroup_atFinite, finiteGroup_atFinite, map_one,
      finiteNorm_det_integral]
    simp
  simp only [heightValue, map_mul, hnorm, mul_one, realGroup_atFinite,
    finiteGroup_atFinite, rowMass_right_integral]

theorem height_level (k : finiteLevel) (g : AdelicGL) :
    heightValue (g * atFinite k.val) = heightValue g := by
  obtain ⟨integral, _, he⟩ := k.property
  rw [← he]
  exact height_right_integral g integral

theorem height_compact (k : AdelicGL) (hk : inMaximalCompact k) : heightValue k = 0 := by
  obtain ⟨hreal, integral, hfinite⟩ := hk
  have hnorm : (adeleNorm (GeneralLinearGroup.det k) : ℝ) = 1 := by
    rw [adeleNorm_parts, realPart_det, finitePart_det,
      determinant_orthogonal _ hreal, ← hfinite, finiteNorm_det_integral]
    simp
  simp only [heightValue, hnorm, rowSquare_orthogonal _ hreal, ← hfinite,
    rowMass_integral, Real.log_one, mul_zero, sub_zero]

theorem height_infinity (base : AdelicGL) (real : RealGL3) :
    heightValue (base * atInfinity real) =
      Real.log (GeneralLinearGroup.det (realGroup base * real)).val +
      Real.log (finiteNorm (GeneralLinearGroup.det (finiteGroup base)) : ℝ) -
      (3 / 2 : ℝ) * Real.log (rowSquare (realGroup base * real)) -
      3 * Real.log (rowMass (finiteGroup base)) := by
  unfold heightValue
  rw [adeleNorm_parts, realPart_det, finitePart_det]
  simp only [map_mul, realGroup_atInfinity, finiteGroup_atInfinity, mul_one]
  rw [Real.log_mul (abs_ne_zero.mpr (Units.ne_zero _))
    (ne_of_gt (finiteNorm_pos _)), Real.log_abs]

theorem height_smooth (base : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 => heightValue (base * atInfinity (real 0))) := by
  let domain : Set (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) :=
    {matrices | ∀ index, (matrices index).det ≠ 0}
  have determinant_smooth : ContDiff ℝ ⊤
      (fun matrices : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
        ((realGroup base).val * matrices 0).det) := by
    simp only [det_fin_three, mul_apply, Fin.sum_univ_three]
    fun_prop
  have square_smooth : ContDiff ℝ ⊤
      (fun matrices : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
        ∑ column, ((realGroup base).val * matrices 0) 2 column ^ 2) := by
    simp only [mul_apply, Fin.sum_univ_three]
    fun_prop
  have matrix_value : ∀ matrices ∈ domain,
      (invertibleMatrix (matrices 0)).val = matrices 0 := by
    intro matrices membership
    simp [invertibleMatrix, membership 0]
  have determinant_nonzero : ∀ matrices ∈ domain,
      ((realGroup base).val * matrices 0).det ≠ 0 := by
    intro matrices membership
    rw [det_mul]
    exact mul_ne_zero (Units.ne_zero (GeneralLinearGroup.det (realGroup base)))
      (membership 0)
  have square_nonzero : ∀ matrices ∈ domain,
      (∑ column, ((realGroup base).val * matrices 0) 2 column ^ 2) ≠ 0 := by
    intro matrices membership
    have positivity := rowSquare_pos (realGroup base * invertibleMatrix (matrices 0))
    simpa only [rowSquare, GeneralLinearGroup.coe_mul, matrix_value matrices membership]
      using ne_of_gt positivity
  have smooth_expression : ContDiffOn ℝ ⊤
      (fun matrices : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
        Real.log ((realGroup base).val * matrices 0).det +
        Real.log (finiteNorm (GeneralLinearGroup.det (finiteGroup base)) : ℝ) -
        (3 / 2 : ℝ) * Real.log
          (∑ column, ((realGroup base).val * matrices 0) 2 column ^ 2) -
        3 * Real.log (rowMass (finiteGroup base))) domain :=
    (((determinant_smooth.contDiffOn.log determinant_nonzero).add contDiffOn_const).sub
      (contDiffOn_const.mul (square_smooth.contDiffOn.log square_nonzero))).sub
      (contDiffOn_const : ContDiffOn ℝ ⊤
        (fun _ : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
          3 * Real.log (rowMass (finiteGroup base))) domain)
  unfold Smooth
  apply smooth_expression.congr
  intro matrices membership
  dsimp only
  rw [height_infinity]
  simp only [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_mul,
    matrix_value matrices membership, rowSquare]

def planeHeight : PlaneHeight where
  height := heightValue
  smooth := height_smooth
  level := height_level
  unipotent := height_unipotent
  scalar := height_scalar
  binary := height_binary
  compact := height_compact

end TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers
