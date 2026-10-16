module

public import TernaryPeriodPolynomials.Building.PlaneFlatExtensions.Helpers
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Group.OpenMapping

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise NNReal ENNReal


noncomputable section

namespace TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers

def finiteNorm (t : FiniteAdelesˣ) : ℝ≥0 :=
  addEquivAddHaarChar (ContinuousAddEquiv.mulLeft t)

def realPart (t : Adelesˣ) : ℝˣ := Units.map (RingHom.fst ℝ FiniteAdeles) t

def finitePart (t : Adelesˣ) : FiniteAdelesˣ :=
  Units.map (RingHom.snd ℝ FiniteAdeles) t

theorem finiteNorm_image (t : FiniteAdelesˣ) (subset : Set FiniteAdeles) :
    finiteMeasure ((fun x => t.val * x) '' subset) =
      (finiteNorm t : ℝ≥0∞) * finiteMeasure subset := by
  have he := addEquivAddHaarChar_smul_preimage finiteMeasure
    (X := (ContinuousAddEquiv.mulLeft t) '' subset) (ContinuousAddEquiv.mulLeft t)
  have hp : (ContinuousAddEquiv.mulLeft t) ⁻¹'
      (ContinuousAddEquiv.mulLeft t) '' subset = subset :=
    Set.preimage_image_eq _ (ContinuousAddEquiv.mulLeft t).injective
  rw [hp] at he
  exact he.symm

theorem real_unit_image (t : ℝˣ) (subset : Set ℝ) :
    volume ((fun x => t.val * x) '' subset) =
      ENNReal.ofReal |t.val| * volume subset := by
  have he := (ContinuousAddEquiv.mulLeft t).toAddEquiv.toEquiv.image_eq_preimage_symm
    subset
  change volume ((ContinuousAddEquiv.mulLeft t).toAddEquiv.toEquiv '' subset) = _
  rw [he]
  change volume ((fun x => (t⁻¹).val * x) ⁻¹' subset) = _
  rw [Units.val_inv_eq_inv_val]
  rw [Real.volume_preimage_mul_left (inv_ne_zero (Units.ne_zero t))]
  congr 2
  exact congrArg abs (inv_inv t.val)

theorem adeleNorm_parts (t : Adelesˣ) :
    (adeleNorm t : ℝ) = |(realPart t).val| * (finiteNorm (finitePart t) : ℝ) := by
  let subset : Set Adeles := Set.Icc (0 : ℝ) 1 ×ˢ Set.range integralEmbedding
  have hmass : adeleMeasure subset = 1 := by
    simp [subset, adeleMeasure, Measure.prod_prod, Real.volume_Icc,
      finiteMeasure_integralLattice]
  have himage : (ContinuousAddEquiv.mulLeft t) '' subset =
      ((fun x => (realPart t).val * x) '' Set.Icc (0 : ℝ) 1) ×ˢ
      ((fun x => (finitePart t).val * x) '' Set.range integralEmbedding) := by
    ext value
    constructor
    · rintro ⟨input, ⟨hr, hf⟩, rfl⟩
      exact ⟨⟨input.1, hr, rfl⟩, ⟨input.2, hf, rfl⟩⟩
    · rintro ⟨⟨realInput, hr, her⟩, ⟨finiteInput, hf, hef⟩⟩
      refine ⟨(realInput, finiteInput), ⟨hr, hf⟩, ?_⟩
      exact Prod.ext her hef
  have he := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := (ContinuousAddEquiv.mulLeft t) '' subset) (ContinuousAddEquiv.mulLeft t)
  have hp : (ContinuousAddEquiv.mulLeft t) ⁻¹'
      (ContinuousAddEquiv.mulLeft t) '' subset = subset :=
    Set.preimage_image_eq _ (ContinuousAddEquiv.mulLeft t).injective
  rw [hp, hmass, himage] at he
  change (adeleNorm t : ℝ≥0∞) * 1 = _ at he
  rw [adeleMeasure, Measure.prod_prod, real_unit_image, finiteNorm_image,
    Real.volume_Icc, finiteMeasure_integralLattice] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [mul_one, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (abs_nonneg _)] using ht

theorem finiteNorm_integral (t : IntegralAdelesˣ) :
    finiteNorm (Units.map integralEmbedding t) = 1 := by
  have himage : (fun x => (Units.map integralEmbedding t).val * x) ''
      Set.range integralEmbedding = Set.range integralEmbedding := by
    ext value
    constructor
    · rintro ⟨value, ⟨input, rfl⟩, rfl⟩
      exact ⟨t.val * input, map_mul integralEmbedding _ _⟩
    · rintro ⟨input, rfl⟩
      refine ⟨integralEmbedding (t.inv * input), ⟨_, rfl⟩, ?_⟩
      change integralEmbedding t.val * integralEmbedding (t.inv * input) = _
      rw [← map_mul, ← mul_assoc, t.val_inv, one_mul]
  have he := finiteNorm_image (Units.map integralEmbedding t)
    (Set.range integralEmbedding)
  rw [himage, finiteMeasure_integralLattice, mul_one] at he
  exact ENNReal.coe_injective he.symm

theorem realPart_det (g : AdelicGL) :
    realPart (GeneralLinearGroup.det g) = GeneralLinearGroup.det (realGroup g) :=
  (GeneralLinearGroup.map_det _ _).symm

theorem finitePart_det (g : AdelicGL) :
    finitePart (GeneralLinearGroup.det g) = GeneralLinearGroup.det (finiteGroup g) :=
  (GeneralLinearGroup.map_det _ _).symm

def finiteMatrixEquiv (g : FiniteGL) : (Fin 3 → FiniteAdeles) ≃ₜ+
    (Fin 3 → FiniteAdeles) where
  toFun := g.val.mulVec
  invFun := g.inv.mulVec
  left_inv vector := by
    rw [mulVec_mulVec, g.inv_val, one_mulVec]
  right_inv vector := by
    rw [mulVec_mulVec, g.val_inv, one_mulVec]
  map_add' := mulVec_add g.val
  continuous_toFun := by
    apply continuous_pi
    intro row
    unfold mulVec dotProduct
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro row
    unfold mulVec dotProduct
    fun_prop

def integralVectors : Set (Fin 3 → FiniteAdeles) :=
  Set.pi Set.univ (fun _ => Set.range integralEmbedding)

def rowLattice (g : FiniteGL) : Set FiniteAdeles :=
  Function.eval 2 '' (finiteMatrixEquiv g '' integralVectors)

theorem integralVectors_compact : IsCompact integralVectors := by
  have he : integralVectors = {vector | ∀ row, vector row ∈
      Set.range integralEmbedding} := by
    ext vector
    simp [integralVectors]
  rw [he]
  exact isCompact_pi_infinite (fun (_ : Fin 3) => integralLattice_isCompact)

theorem integralVectors_open : IsOpen integralVectors := by
  exact isOpen_set_pi Set.finite_univ (fun _ _ => integralLattice_isOpen)

theorem rowLattice_compact (g : FiniteGL) : IsCompact (rowLattice g) :=
  (integralVectors_compact.image (finiteMatrixEquiv g).continuous).image (continuous_apply 2)

theorem rowLattice_open (g : FiniteGL) : IsOpen (rowLattice g) :=
  isOpenMap_eval 2 _ ((finiteMatrixEquiv g).toHomeomorph.isOpenMap _ integralVectors_open)

theorem rowLattice_nonempty (g : FiniteGL) : (rowLattice g).Nonempty := by
  apply Set.Nonempty.image
  apply Set.Nonempty.image
  refine ⟨0, ?_⟩
  intro row _
  exact ⟨0, map_zero integralEmbedding⟩

def rowMass (g : FiniteGL) : ℝ := finiteMeasure.real (rowLattice g)

theorem rowMass_pos (g : FiniteGL) : 0 < rowMass g := by
  exact ENNReal.toReal_pos (ne_of_gt ((rowLattice_open g).measure_pos finiteMeasure
    (rowLattice_nonempty g))) (rowLattice_compact g).measure_lt_top.ne

theorem rowLattice_mem (g : FiniteGL) (value : FiniteAdeles) :
    value ∈ rowLattice g ↔ ∃ vector ∈ integralVectors,
      ∑ row : Fin 3, g.val 2 row * vector row = value := by
  simp only [rowLattice, Set.mem_image, finiteMatrixEquiv, Function.eval]
  constructor
  · rintro ⟨image, ⟨vector, hvector, rfl⟩, he⟩
    exact ⟨vector, hvector, he⟩
  · rintro ⟨vector, hvector, he⟩
    exact ⟨g.val.mulVec vector, ⟨vector, hvector, rfl⟩, he⟩

theorem rowLattice_of_row_eq (g other : FiniteGL)
    (he : g.val 2 = other.val 2) : rowLattice g = rowLattice other := by
  ext value
  simp only [rowLattice_mem, he]

theorem rowLattice_scalar (g other : FiniteGL) (t : FiniteAdelesˣ)
    (he : ∀ row, other.val 2 row = t.val * g.val 2 row) :
    rowLattice other = (fun x => t.val * x) '' rowLattice g := by
  ext value
  simp only [rowLattice_mem, Set.mem_image]
  constructor
  · rintro ⟨vector, hv, hvalue⟩
    refine ⟨∑ row, g.val 2 row * vector row, ⟨vector, hv, rfl⟩, ?_⟩
    simpa only [he, mul_assoc, ← Finset.mul_sum] using hvalue
  · rintro ⟨value, ⟨vector, hv, rfl⟩, rfl⟩
    refine ⟨vector, hv, ?_⟩
    simp only [he, mul_assoc, ← Finset.mul_sum]

theorem rowMass_scalar (g other : FiniteGL) (t : FiniteAdelesˣ)
    (he : ∀ row, other.val 2 row = t.val * g.val 2 row) :
    rowMass other = (finiteNorm t : ℝ) * rowMass g := by
  unfold rowMass Measure.real
  rw [rowLattice_scalar g other t he, finiteNorm_image, ENNReal.toReal_mul,
    ENNReal.coe_toReal]

end TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers
