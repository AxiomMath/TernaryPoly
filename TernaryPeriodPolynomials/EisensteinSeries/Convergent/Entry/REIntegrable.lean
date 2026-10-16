module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RESets
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteGlobalIntegrability

@[expose] public section


/-!
# R-e: Continuity, majorant and integrability of the entry integrand

`entryIntegrand_continuous` (locally constant in the finite matrix), `entryWeight_integrable` (the determinant weight is integrable on `𝔸_f²` for `3 < Re e`, via the place-`3` Fubini join and the library's away-three weight integral transported by `awayThreeEquiv`), `entryIntegrand_integrable`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The entry integrand as a function of the finite plane matrix, via a chosen Iwasawa decomposition. -/
def entryFun (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ)
    (h : FiniteGL) : ℂ :=
  normPower (GeneralLinearGroup.det (atFinite (m * (finitePlaneInductionCoordinates h).block))) e *
    cusp.realize vector (atFinite (m * (finitePlaneInductionCoordinates h).block))

theorem normPower_det_atFinite_mul (m B : BinaryFiniteGL) (e : ℂ) :
    normPower (GeneralLinearGroup.det (atFinite (m * B))) e =
      normPower (GeneralLinearGroup.det (atFinite m)) e * normPower (finiteAdeleUnit (GeneralLinearGroup.det B)) e := by
  rw [atFinite_mul, map_mul, binary_det_atFinite, binary_det_atFinite]
  exact normPower_mul _ _ e

theorem entryValue_independent (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (h : FiniteGL)
    (first second : FinitePlaneInductionCoordinates h) :
    normPower (GeneralLinearGroup.det (atFinite (m * first.block))) e *
        cusp.realize vector (atFinite (m * first.block)) =
      normPower (GeneralLinearGroup.det (atFinite (m * second.block))) e *
        cusp.realize vector (atFinite (m * second.block)) := by
  obtain ⟨integral, equality⟩ := finitePlaneInductionBlocks_exists_integral h first second
  have weight := finitePlaneInductionBlocks_normPower h first second e
  have real : cusp.realize vector (atFinite (m * second.block)) =
      cusp.realize vector (atFinite (m * first.block)) := by
    rw [equality, ← mul_assoc]
    exact cuspSpherical_realize_right cusp vector spherical _ _
  rw [real, normPower_det_atFinite_mul, normPower_det_atFinite_mul, weight]

theorem entryFun_right (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (h : FiniteGL)
    (compact : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    entryFun cusp vector m e (h * GeneralLinearGroup.map integralEmbedding compact) =
      entryFun cusp vector m e h :=
  entryValue_independent cusp vector spherical m e _ (finitePlaneInductionCoordinates _)
    (finitePlaneInductionCoordinates_right (finitePlaneInductionCoordinates h) compact)

theorem entryFun_continuous (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) :
    Continuous (entryFun cusp vector m e) := by
  apply continuous_iff_continuousAt.mpr
  intro matrix
  apply Filter.EventuallyEq.continuousAt
  have near : ∀ᶠ other in nhds matrix, matrix⁻¹ * other ∈ finiteIntegralGLLevel 3 :=
    (continuous_const.mul continuous_id).continuousAt.eventually
      ((finiteIntegralGLLevel_isOpen 3).mem_nhds (by
        change matrix⁻¹ * matrix ∈ finiteIntegralGLLevel 3
        rw [inv_mul_cancel]
        exact (finiteIntegralGLLevel 3).one_mem))
  filter_upwards [near] with other member
  obtain ⟨compact, equality⟩ := member
  have factors : other = matrix * GeneralLinearGroup.map integralEmbedding compact := by
    rw [equality, mul_inv_cancel_left]
  rw [factors, entryFun_right cusp vector spherical]

theorem entryIntegrand_eq_fun (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ)
    (v : FiniteAdeles × FiniteAdeles) :
    entryIntegrand cusp vector m e v = entryFun cusp vector m e (planeOppositeStandardMatrix v.1 v.2) :=
  entryValue_independent cusp vector spherical m e _ (finitePadicPlaneCoordinates v.1 v.2)
    (finitePlaneInductionCoordinates _)

theorem entryIntegrand_continuous (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) :
    Continuous (entryIntegrand cusp vector m e) := by
  have equality : entryIntegrand cusp vector m e = fun v : FiniteAdeles × FiniteAdeles =>
      entryFun cusp vector m e (planeOppositeStandardMatrix v.1 v.2) :=
    funext (entryIntegrand_eq_fun cusp vector spherical m e)
  rw [equality]
  exact (entryFun_continuous cusp vector spherical m e).comp planeOppositeStandardMatrix_continuous

theorem awayPlaceThree_mem (b : FiniteAwayPlace placeThree) : b.val ∈ FiniteAwayThree := by
  change threeCompletionEquiv (finiteEvaluation placeThree b.val) = 0
  rw [show finiteEvaluation placeThree b.val = 0 from b.property, map_zero]

def awayThreeAddEquiv : FiniteAwayThree ≃+ FiniteAwayPlace placeThree where
  toFun a := ⟨a.val, finiteAwayThree_evaluation_zero a⟩
  invFun b := ⟨b.val, awayPlaceThree_mem b⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem awayThreeAddEquiv_apply (a : FiniteAwayThree) :
    awayThreeAddEquiv a = ⟨a.val, finiteAwayThree_evaluation_zero a⟩ := rfl

/-- The away-from-three adeles are the away-from-the-place-three adeles. -/
def awayThreeEquiv : FiniteAwayThree ≃ₜ+ FiniteAwayPlace placeThree where
  toAddEquiv := awayThreeAddEquiv
  continuous_toFun := continuous_subtype_val.subtype_mk (fun a => finiteAwayThree_evaluation_zero a)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun b => awayPlaceThree_mem b)

theorem awayThreeEquiv_apply (a : FiniteAwayThree) :
    awayThreeEquiv a = ⟨a.val, finiteAwayThree_evaluation_zero a⟩ := rfl

theorem awayThreeEquiv_val (a : FiniteAwayThree) : (awayThreeEquiv a).val = a.val :=
  congrArg Subtype.val (awayThreeEquiv_apply a)

theorem awayThreeEquiv_preimage_unit :
    awayThreeEquiv ⁻¹' (finiteAwayPlaceUnitCompact placeThree : Set (FiniteAwayPlace placeThree)) =
      Subtype.val ⁻¹' Set.range integralEmbedding := by
  ext a
  exact Iff.of_eq (congrArg (· ∈ Set.range integralEmbedding) (awayThreeEquiv_val a))

theorem awayThreeEquiv_measurePreserving :
    MeasurePreserving awayThreeEquiv finiteAwayThreeMeasure (finiteAwayPlaceMeasure placeThree) := by
  have mapped_haar : (Measure.map awayThreeEquiv finiteAwayThreeMeasure).IsAddHaarMeasure :=
    awayThreeEquiv.isAddHaarMeasure_map finiteAwayThreeMeasure
  have measurable : Measurable (awayThreeEquiv : FiniteAwayThree → FiniteAwayPlace placeThree) :=
    awayThreeEquiv.continuous.measurable
  have normalized : Measure.map awayThreeEquiv finiteAwayThreeMeasure
      (finiteAwayPlaceUnitCompact placeThree : Set (FiniteAwayPlace placeThree)) = 1 := by
    rw [Measure.map_apply measurable (finiteAwayPlaceUnitCompact placeThree).isCompact.isClosed.measurableSet,
      awayThreeEquiv_preimage_unit]
    exact finiteAwayThreeMeasure_normalized
  refine ⟨measurable, ?_⟩
  have unique := Measure.addHaarMeasure_unique (Measure.map awayThreeEquiv finiteAwayThreeMeasure)
    (finiteAwayPlaceUnitCompact placeThree)
  rw [normalized, one_smul] at unique
  exact unique

/-- The absolute value of the determinant weight of the block. -/
def entryWeight (e : ℂ) (v : FiniteAdeles × FiniteAdeles) : ℝ :=
  ‖normPower (GeneralLinearGroup.det (atFinite (entryBlock v))) e‖

theorem entryWeight_join (e : ℂ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      entryWeight e (finitePadicRadicalJoin place (localPair, awayPair)) =
        padicPositiveWeight e localPair * entryWeight e (awayPair.1.val, awayPair.2.val) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  unfold entryWeight entryBlock
  rw [finitePadicRadicalJoin_apply]
  dsimp only
  rw [finitePadicPlaneCoordinates_split_block, atFinite_mul, map_mul, normPower_mul, norm_mul,
    normPower_det_finiteAtPadicGL]
  exact mul_comm _ _

theorem entryWeight_away_integrable (e : ℂ) (convergent : 3 < e.re) :
    Integrable (fun a : FiniteAwayPlace placeThree × FiniteAwayPlace placeThree =>
      entryWeight e (a.1.val, a.2.val))
      ((finiteAwayPlaceMeasure placeThree).prod (finiteAwayPlaceMeasure placeThree)) := by
  have base := goodLinePositiveWeight_integrable e convergent
  have preserving := awayThreeEquiv_measurePreserving.prod awayThreeEquiv_measurePreserving
  have embedding : MeasurableEmbedding (Prod.map awayThreeEquiv awayThreeEquiv) :=
    (awayThreeEquiv.toHomeomorph.prodCongr awayThreeEquiv.toHomeomorph).measurableEmbedding
  rw [← preserving.integrable_comp_emb embedding]
  refine base.congr (Eventually.of_forall fun pair => ?_)
  change goodLinePositiveWeight e pair = entryWeight e ((awayThreeEquiv pair.1).val, (awayThreeEquiv pair.2).val)
  rw [awayThreeEquiv_val, awayThreeEquiv_val]
  rfl

theorem entryWeight_integrable (e : ℂ) (convergent : 3 < e.re) :
    Integrable (entryWeight e) (finiteMeasure.prod finiteMeasure) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv placeThree).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv placeThree).property⟩
  have local_integrable := padicPositiveWeight_integrable (finitePadicMeasure placeThree)
    (finitePadicMeasure_normalized placeThree) e (by linarith)
  have product := local_integrable.mul_prod (entryWeight_away_integrable e convergent)
  rw [← (finitePadicRadicalJoin_measurePreserving placeThree).integrable_comp_emb
    (finitePadicRadicalJoin placeThree).measurableEmbedding]
  refine product.congr (Eventually.of_forall fun pair => ?_)
  exact (entryWeight_join e placeThree pair.1 pair.2).symm

theorem entryIntegrand_norm_le (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ)
    (bound : ℝ) (bounded : ∀ x, ‖cusp.realize vector x‖ ≤ bound) (v : FiniteAdeles × FiniteAdeles) :
    ‖entryIntegrand cusp vector m e v‖ ≤
      entryWeight e v * (‖normPower (GeneralLinearGroup.det (atFinite m)) e‖ * bound) := by
  unfold entryIntegrand entryWeight
  rw [norm_mul, normPower_det_atFinite_mul, norm_mul, ← binary_det_atFinite]
  have nonneg : 0 ≤ ‖normPower (GeneralLinearGroup.det (atFinite m)) e‖ *
      ‖normPower (GeneralLinearGroup.det (atFinite (entryBlock v))) e‖ := by positivity
  calc ‖normPower (GeneralLinearGroup.det (atFinite m)) e‖ *
        ‖normPower (GeneralLinearGroup.det (atFinite (entryBlock v))) e‖ *
        ‖cusp.realize vector (atFinite (m * entryBlock v))‖
      ≤ ‖normPower (GeneralLinearGroup.det (atFinite m)) e‖ *
        ‖normPower (GeneralLinearGroup.det (atFinite (entryBlock v))) e‖ * bound :=
        mul_le_mul_of_nonneg_left (bounded _) nonneg
    _ = _ := by ring

theorem entryIntegrand_integrable (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (convergent : 3 < e.re) :
    Integrable (entryIntegrand cusp vector m e) (finiteMeasure.prod finiteMeasure) := by
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  refine ((entryWeight_integrable e convergent).mul_const
    (‖normPower (GeneralLinearGroup.det (atFinite m)) e‖ * bound)).mono'
    (entryIntegrand_continuous cusp vector spherical m e).aestronglyMeasurable ?_
  exact Eventually.of_forall (entryIntegrand_norm_le cusp vector m e bound bounded)

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
