module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.NormalConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ScalarSummability

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardJointContinuity

instance adelicGL_firstCountable : FirstCountableTopology AdelicGL := by
  let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) Adeles) :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → Adeles))
  let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) Adeles)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.firstCountableTopology
  exact Units.isClosedEmbedding_embedProduct.isEmbedding.isInducing.firstCountableTopology

def eisensteinSum (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ) (argument : AdelicGL) : ℂ :=
  ∑' flag : Flags .plane, eisensteinSummand extension parameter argument flag

def constantTerm (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ) (argument : AdelicGL) : ℂ :=
  ∫ coordinates in additiveDomain ×ˢ additiveDomain,
    eisensteinSum extension parameter (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure

theorem eisensteinSum_measurable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    @Measurable (ℂ × AdelicGL) ℂ (borel (ℂ × AdelicGL)) inferInstance
      (fun pair => eisensteinSum extension pair.1 pair.2) := by
  let : MeasurableSpace (ℂ × AdelicGL) := borel (ℂ × AdelicGL)
  let : BorelSpace (ℂ × AdelicGL) := ⟨rfl⟩
  exact Measurable.tsum (fun flag => (NormalConvergence.summand_joint_continuous data extension flat flag).measurable)

theorem constantTerm_eq_standard {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    constantTerm extension parameter argument =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure :=
  ScalarSummability.eisenstein_constantTerm data extension flat bound bounded parameter halfPlane argument
    (eisensteinSum extension parameter)
    (fun argument => (CompactMajorant.summable data extension flat bound bounded parameter halfPlane argument).hasSum)

theorem constantTerm_continuousAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (argument : AdelicGL) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ContinuousAt (fun pair : ℂ × AdelicGL => constantTerm extension pair.1 pair.2) (parameter, argument) := by
  let lower := (-(degree : ℝ) / 2 + parameter.re) / 2
  let upper := parameter.re + 1
  have lowerHalfPlane : -(degree : ℝ) / 2 < lower := by dsimp [lower]; linarith
  have upperHalfPlane : -(degree : ℝ) / 2 < upper := by dsimp [upper]; linarith
  obtain ⟨set, compact, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds argument
  have stripNeighborhood : {z : ℂ | lower ≤ z.re ∧ z.re ≤ upper} ∈ 𝓝 parameter := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
          (show lower < parameter.re ∧ parameter.re < upper by
            constructor <;> dsimp [lower, upper] <;> linarith))
    intro value membership
    exact ⟨membership.1.le, membership.2.le⟩
  let translate : (Adeles × Adeles) × AdelicGL → AdelicGL :=
    fun pair => lineUnipotent pair.1.1 pair.1.2 * pair.2
  have translateContinuous : Continuous translate :=
    (InducedContinuity.lineUnipotent_continuous.comp continuous_fst).mul continuous_snd
  let translated := translate ''
    ((InducedContinuity.additiveCompact ×ˢ InducedContinuity.additiveCompact) ×ˢ set)
  have translatedCompact : IsCompact translated :=
    ((InducedContinuity.additiveCompact_isCompact.prod InducedContinuity.additiveCompact_isCompact).prod
      compact).image translateContinuous
  obtain ⟨majorant, _, summable, dominates⟩ := NormalConvergence.strip_compact_majorant data extension flat
    bound bounded lower upper lowerHalfPlane upperHalfPlane translated translatedCompact
  have near : {z : ℂ | lower ≤ z.re ∧ z.re ≤ upper} ×ˢ set ∈ 𝓝 (parameter, argument) :=
    prod_mem_nhds stripNeighborhood neighborhood
  apply continuousAt_of_dominated (bound := fun _ : Adeles × Adeles => ∑' flag, majorant flag)
  · filter_upwards [near] with pair membership
    exact ((CompactMajorant.continuous data extension flat bound bounded pair.1
      (lowerHalfPlane.trans_le membership.1.1)).comp
        (InducedContinuity.lineUnipotent_continuous.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [near] with pair membership
    filter_upwards [ae_restrict_mem (FundamentalDomain.additiveDomain_measurable.prod
      FundamentalDomain.additiveDomain_measurable)] with coordinates coordinateMembership
    have translatedMembership : lineUnipotent coordinates.1 coordinates.2 * pair.2 ∈ translated :=
      ⟨(coordinates, pair.2), ⟨Set.prod_mono InducedContinuity.additiveDomain_subset_compact
        InducedContinuity.additiveDomain_subset_compact coordinateMembership, membership.2⟩, rfl⟩
    have estimate := dominates (pair.1, lineUnipotent coordinates.1 coordinates.2 * pair.2)
      ⟨membership.1, translatedMembership⟩
    exact (summable.of_norm_bounded estimate).hasSum.norm_le_of_bounded summable.hasSum estimate
  · exact integrable_const _
  · apply Eventually.of_forall
    intro coordinates
    have mapContinuous : Continuous (fun pair : ℂ × AdelicGL =>
        (pair.1, lineUnipotent coordinates.1 coordinates.2 * pair.2)) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    exact (NormalConvergence.continuousAt_halfPlane data extension flat bound bounded parameter
      (lineUnipotent coordinates.1 coordinates.2 * argument) halfPlane).comp
        (f := fun pair : ℂ × AdelicGL => (pair.1, lineUnipotent coordinates.1 coordinates.2 * pair.2))
        (x := (parameter, argument))
        mapContinuous.continuousAt

theorem standard_continuousAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (argument : AdelicGL) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ContinuousAt (fun pair : ℂ × AdelicGL =>
      ∫ coordinates, standardIntegrand extension pair.1 pair.2 coordinates ∂radicalMeasure) (parameter, argument) := by
  apply (constantTerm_continuousAt data extension flat bound bounded parameter argument halfPlane).congr_of_eventuallyEq
  have near : {pair : ℂ × AdelicGL | -(degree : ℝ) / 2 < pair.1.re} ∈ 𝓝 (parameter, argument) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).mem_nhds halfPlane
  filter_upwards [near] with pair membership
  exact (constantTerm_eq_standard data extension flat bound bounded pair.1 membership pair.2).symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardJointContinuity
