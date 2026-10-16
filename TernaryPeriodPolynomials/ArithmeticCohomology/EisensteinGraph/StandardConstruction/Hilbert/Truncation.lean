module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.CompactMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.VectorCompactIntegral

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertTruncation

def cellIntegral {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (rational : ℚ × ℚ) : data.cusp.H :=
  ∫ coordinates in additiveDomain ×ˢ additiveDomain,
    HilbertStandard.integrand data parameter (extension parameter) (flat.1 parameter) argument
      (FundamentalDomain.rationalPair rational + coordinates) ∂radicalMeasure

theorem cells_sum {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    (∑' rational : ℚ × ℚ, cellIntegral data extension flat parameter argument rational) =
      HilbertStandard.value data parameter (extension parameter) (flat.1 parameter) argument :=
  (FundamentalDomain.radicalDomain_fundamental.integral_eq_tsum''
    (HilbertStandard.integrand data parameter (extension parameter) (flat.1 parameter) argument)
    (HilbertStandard.integrand_integrable data parameter (extension parameter) (flat.1 parameter) halfPlane argument)).symm

theorem cellIntegral_joint_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (rational : ℚ × ℚ) :
    Continuous (fun pair : ℂ × AdelicGL => cellIntegral data extension flat pair.1 pair.2 rational) := by
  apply VectorCompactIntegral.continuous_integralOn radicalMeasure
    (additiveDomain ×ˢ additiveDomain)
    (InducedContinuity.additiveCompact ×ˢ InducedContinuity.additiveCompact)
    (FundamentalDomain.additiveDomain_measurable.prod FundamentalDomain.additiveDomain_measurable)
    (Set.prod_mono InducedContinuity.additiveDomain_subset_compact InducedContinuity.additiveDomain_subset_compact)
    (InducedContinuity.additiveCompact_isCompact.prod InducedContinuity.additiveCompact_isCompact)
    (fun (pair : ℂ × AdelicGL) coordinates =>
      HilbertStandard.integrand data pair.1 (extension pair.1) (flat.1 pair.1) pair.2
        (FundamentalDomain.rationalPair rational + coordinates))
  apply (HilbertFlat.joint_continuous data extension flat).comp
    (f := fun pair : (ℂ × AdelicGL) × (Adeles × Adeles) =>
      (pair.1.1, (weyl : AdelicGL)⁻¹ *
        lineUnipotent (FundamentalDomain.rationalPair rational + pair.2).1
          (FundamentalDomain.rationalPair rational + pair.2).2 * pair.1.2))
  exact (continuous_fst.fst).prodMk
    ((continuous_const.mul (InducedContinuity.lineUnipotent_continuous.comp
      (continuous_const.add continuous_snd))).mul continuous_fst.snd)

theorem cell_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ majorant : (ℚ × ℚ) → ℝ, (∀ rational, 0 ≤ majorant rational) ∧ Summable majorant ∧
      ∀ pair ∈ {parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set,
      ∀ rational, ‖cellIntegral data extension flat pair.1 pair.2 rational‖ ≤ majorant rational := by
  let translate : (Adeles × Adeles) × AdelicGL → AdelicGL :=
    fun pair => lineUnipotent pair.1.1 pair.1.2 * pair.2
  have translateContinuous : Continuous translate :=
    (InducedContinuity.lineUnipotent_continuous.comp continuous_fst).mul continuous_snd
  let translated := translate ''
    ((InducedContinuity.additiveCompact ×ˢ InducedContinuity.additiveCompact) ×ˢ set)
  have translatedCompact : IsCompact translated :=
    ((InducedContinuity.additiveCompact_isCompact.prod InducedContinuity.additiveCompact_isCompact).prod
      compact).image translateContinuous
  obtain ⟨majorant, nonnegative, summable, dominates⟩ := HilbertCompactMajorant.strip_compact_majorant
    data extension flat lower upper lowerHalfPlane upperHalfPlane translated translatedCompact
  refine ⟨fun rational => majorant (BruhatCells.openFlag rational),
    fun rational => nonnegative _, summable.comp_injective BruhatCells.openFlag_injective, ?_⟩
  intro pair membership rational
  have estimate := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain))
    (C := majorant (BruhatCells.openFlag rational))
    (f := fun coordinates => HilbertStandard.integrand data pair.1 (extension pair.1) (flat.1 pair.1)
      pair.2 (FundamentalDomain.rationalPair rational + coordinates))
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at estimate
  apply estimate
  filter_upwards [ae_restrict_mem (FundamentalDomain.additiveDomain_measurable.prod
    FundamentalDomain.additiveDomain_measurable)] with coordinates coordinateMembership
  have bound := dominates (pair.1, lineUnipotent coordinates.1 coordinates.2 * pair.2)
    ⟨membership.1, (coordinates, pair.2),
      ⟨Set.prod_mono InducedContinuity.additiveDomain_subset_compact
        InducedContinuity.additiveDomain_subset_compact coordinateMembership, membership.2⟩, rfl⟩
    (BruhatCells.openFlag rational)
  simpa only [HilbertHeight.normSummand_open_shift, HilbertStandard.integrand,
    FundamentalDomain.rationalPair, Prod.fst_add, Prod.snd_add] using bound

theorem uniformOn_strip_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    TendstoUniformlyOn
      (fun finite : Finset (ℚ × ℚ) => fun pair : ℂ × AdelicGL =>
        ∑ rational ∈ finite, cellIntegral data extension flat pair.1 pair.2 rational)
      (fun pair => HilbertStandard.value data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      atTop ({parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set) := by
  obtain ⟨majorant, _, summable, dominates⟩ := cell_majorant data extension flat
    lower upper lowerHalfPlane upperHalfPlane set compact
  have uniform := tendstoUniformlyOn_tsum summable
    (fun rational pair membership => dominates pair membership rational)
  apply uniform.congr_right
  intro pair membership
  exact cells_sum data extension flat pair.1 (lowerHalfPlane.trans_le membership.1.1) pair.2

theorem continuousOn_strip_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ContinuousOn
      (fun pair : ℂ × AdelicGL => HilbertStandard.value data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      ({parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set) := by
  obtain ⟨majorant, _, summable, dominates⟩ := cell_majorant data extension flat
    lower upper lowerHalfPlane upperHalfPlane set compact
  have continuous := continuousOn_tsum
    (fun rational => (cellIntegral_joint_continuous data extension flat rational).continuousOn)
    summable (fun rational pair membership => dominates pair membership rational)
  apply continuous.congr
  intro pair membership
  exact (cells_sum data extension flat pair.1 (lowerHalfPlane.trans_le membership.1.1) pair.2).symm

theorem standard_joint_continuousAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ContinuousAt
      (fun pair : ℂ × AdelicGL => HilbertStandard.value data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      (parameter, argument) := by
  let lower : ℝ := (-(degree : ℝ) / 2 + parameter.re) / 2
  let upper : ℝ := parameter.re + 1
  have lowerHalfPlane : -(degree : ℝ) / 2 < lower := by dsimp [lower]; linarith
  have upperHalfPlane : -(degree : ℝ) / 2 < upper := by dsimp [upper]; linarith
  obtain ⟨set, compact, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds argument
  apply (continuousOn_strip_compact data extension flat lower upper lowerHalfPlane upperHalfPlane set compact).continuousAt
  apply prod_mem_nhds _ neighborhood
  apply Filter.mem_of_superset
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show lower < parameter.re ∧ parameter.re < upper by
          constructor <;> dsimp [lower, upper] <;> linarith))
  intro value membership
  exact ⟨membership.1.le, membership.2.le⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertTruncation
