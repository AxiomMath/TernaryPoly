module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ExtremalSpherical

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspFiniteLevelValues (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) : Submodule ℂ cusp.H where
  carrier := {vector | ∀ element : level, cusp.π (atFinite element.val) vector = vector}
  zero_mem' := by intro element; exact map_zero _
  add_mem' {first second} first_mem second_mem := by
    intro element
    rw [map_add, first_mem, second_mem]
  smul_mem' scalar vector member := by
    intro element
    rw [map_smul, member]

theorem cuspFiniteLevelValues_isClosed (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    IsClosed (cuspFiniteLevelValues cusp level : Set cusp.H) := by
  change IsClosed {vector : cusp.H | ∀ element : level, cusp.π (atFinite element.val) vector = vector}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun element : level =>
    isClosed_eq (cuspUnitaryOperator cusp (atFinite element.val)).continuous continuous_id)

instance cuspFiniteLevelValues_completeSpace (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    CompleteSpace (cuspFiniteLevelValues cusp level) :=
  (cuspFiniteLevelValues_isClosed cusp level).completeSpace_coe

def cuspFiniteProjection (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) : cusp.H →L[ℂ] cusp.H :=
  (cuspFiniteLevelValues cusp level).starProjection

theorem cuspFiniteProjection_mem (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (vector : cusp.H) :
    cuspFiniteProjection cusp level vector ∈ cuspFiniteLevelValues cusp level := by
  change (cuspFiniteLevelValues cusp level).starProjection vector ∈ cuspFiniteLevelValues cusp level
  have member : (cuspFiniteLevelValues cusp level).starProjection vector ∈
      (cuspFiniteLevelValues cusp level).starProjection.toLinearMap.range := ⟨vector, rfl⟩
  rwa [Submodule.range_starProjection] at member

theorem cuspFiniteProjection_eq_self (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : cusp.H) (member : vector ∈ cuspFiniteLevelValues cusp level) :
    cuspFiniteProjection cusp level vector = vector :=
  Submodule.starProjection_eq_self_iff.mpr member

theorem cuspFiniteLevelValues_real (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (matrix : BinaryRealGL) (vector : cusp.H) (member : vector ∈ cuspFiniteLevelValues cusp level) :
    cusp.π (atInfinity matrix) vector ∈ cuspFiniteLevelValues cusp level := by
  intro element
  change (cusp.π (atFinite element.val) * cusp.π (atInfinity matrix)) vector = _
  rw [← map_mul, (atInfinity_commute_atFinite matrix element.val).symm.eq,
    map_mul, Module.End.mul_apply, member]

theorem cuspFiniteLevelValues_real_map (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (matrix : BinaryRealGL) :
    (cuspFiniteLevelValues cusp level).map (cusp.π (atInfinity matrix)) = cuspFiniteLevelValues cusp level := by
  apply le_antisymm
  · rintro _ ⟨vector, member, rfl⟩
    exact cuspFiniteLevelValues_real cusp level matrix vector member
  · intro vector member
    refine ⟨cusp.π (atInfinity matrix⁻¹) vector, cuspFiniteLevelValues_real cusp level matrix⁻¹ vector member, ?_⟩
    change (cusp.π (atInfinity matrix) * cusp.π (atInfinity matrix⁻¹)) vector = vector
    rw [← map_mul, ← atInfinity_mul, mul_inv_cancel, atInfinity_one, map_one]
    rfl

theorem cuspFiniteProjection_real (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (matrix : BinaryRealGL) (vector : cusp.H) :
    cuspFiniteProjection cusp level (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (cuspFiniteProjection cusp level vector) := by
  have naturality := Submodule.starProjection_map_apply
    (cuspUnitaryIsometryEquiv cusp (atInfinity matrix)) (cuspFiniteLevelValues cusp level)
    (cuspUnitaryIsometryEquiv cusp (atInfinity matrix) vector)
  rw [LinearIsometryEquiv.symm_apply_apply] at naturality
  have map_eq : (cuspFiniteLevelValues cusp level).map
      (cuspUnitaryIsometryEquiv cusp (atInfinity matrix)).toLinearEquiv.toLinearMap =
      cuspFiniteLevelValues cusp level := cuspFiniteLevelValues_real_map cusp level matrix
  simp only [map_eq] at naturality
  exact naturality

theorem cuspFiniteProjection_inner (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (first second : cusp.H) :
    inner ℂ (cuspFiniteProjection cusp level first) second = inner ℂ first (cuspFiniteProjection cusp level second) :=
  Submodule.inner_starProjection_left_eq_right _ _ _

theorem cuspFiniteProjection_smooth (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (level_open : IsOpen (level : Set BinaryFiniteGL)) (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (vector : cusp.H) (smooth : vector ∈ cusp.smooth) : cuspFiniteProjection cusp level vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact _).mpr
  constructor
  · have regular := ((cusp.smooth_exact vector).mp smooth).1
    have projected : Smooth (fun point : Fin 1 → BinaryRealGL =>
        cuspFiniteProjection cusp level (cusp.π (atInfinity (point 0)) vector)) :=
      (cuspFiniteProjection cusp level).restrictScalars ℝ |>.contDiff.comp_contDiffOn regular
    have equality : (fun point : Fin 1 → BinaryRealGL => cuspFiniteProjection cusp level (cusp.π (atInfinity (point 0)) vector)) =
        (fun point : Fin 1 → BinaryRealGL => cusp.π (atInfinity (point 0)) (cuspFiniteProjection cusp level vector)) := by
      funext point
      exact cuspFiniteProjection_real cusp level (point 0) vector
    rwa [equality] at projected
  · exact ⟨level, level_open, level_compact, cuspFiniteProjection_mem cusp level vector⟩

theorem cuspFiniteProjection_raising (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cusp.H) (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspRaisingVector cusp weight (cuspFiniteProjection cusp level vector) =
      cuspFiniteProjection cusp level (cuspRaisingVector cusp weight vector) :=
  cuspRaisingVector_intertwiner cusp _ (cuspFiniteProjection_real cusp level) weight vector regular

theorem cuspFiniteProjection_lowering (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cusp.H) (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspLoweringVector cusp weight (cuspFiniteProjection cusp level vector) =
      cuspFiniteProjection cusp level (cuspLoweringVector cusp weight vector) :=
  cuspLoweringVector_intertwiner cusp _ (cuspFiniteProjection_real cusp level) weight vector regular

end TernaryPeriodPolynomials.SphericalDetection.Helpers
