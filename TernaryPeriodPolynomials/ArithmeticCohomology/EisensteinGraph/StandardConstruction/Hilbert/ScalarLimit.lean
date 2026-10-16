module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FixedRealizationLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.SupMajorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.CellRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.StandardSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertScalarLimit

theorem open_shift_argument (argument : AdelicGL) (rational : ℚ × ℚ) (shift : Adeles × Adeles) :
    rationalGroup (BruhatCells.openRepresentative rational)⁻¹ *
      (lineUnipotent shift.1 shift.2 * argument) =
    weyl⁻¹ * lineUnipotent (FundamentalDomain.rationalPair rational + shift).1
      (FundamentalDomain.rationalPair rational + shift).2 * argument := by
  rw [BruhatCells.openRepresentative_inv, map_mul, map_inv]
  change (GeneralLinearGroup.map rationalAdele (weyl : RationalGL3))⁻¹ *
    GeneralLinearGroup.map rationalAdele (lineUnipotent rational.1 rational.2) *
      (lineUnipotent shift.1 shift.2 * argument) = _
  rw [map_weyl, LineDecomposition.map_lineUnipotent,
    mul_assoc (weyl⁻¹ : AdelicGL), ← mul_assoc (lineUnipotent _ _), ← lineUnipotent_add]
  simp only [mul_assoc, FundamentalDomain.rationalPair, Prod.fst_add, Prod.snd_add]

theorem cell_scalar_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    ∃ majorant : (ℚ × ℚ) → ℝ, (∀ rational, 0 ≤ majorant rational) ∧ Summable majorant ∧
      ∀ rational, cuspSupNorm (HilbertCellRealization.cellVector data extension flat parameter argument rational) ≤
        majorant rational := by
  obtain ⟨majorant, nonnegative, summable, bounded⟩ :=
    CuspSupMajorant.domain_majorant data parameter (extension parameter) (flat.1 parameter) halfPlane argument
  refine ⟨fun rational => majorant (BruhatCells.openFlag rational), fun _ => nonnegative _,
    summable.comp_injective BruhatCells.openFlag_injective, ?_⟩
  intro rational
  apply cuspSupNorm_le
  intro test
  rw [HilbertCellRealization.cellVector_realizes]
  have estimate := norm_integral_le_of_norm_le_const
    (μ := radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain))
    (C := majorant (BruhatCells.openFlag rational))
    (f := fun coordinates => data.cusp.realize
      (CuspLift.vector data .plane parameter (extension parameter) (flat.1 parameter)
        (weyl⁻¹ * lineUnipotent (FundamentalDomain.rationalPair rational + coordinates).1
          (FundamentalDomain.rationalPair rational + coordinates).2 * argument)) test)
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at estimate
  apply estimate
  filter_upwards [ae_restrict_mem
    (FundamentalDomain.additiveDomain_measurable.prod FundamentalDomain.additiveDomain_measurable)]
    with coordinates membership
  have bound := bounded coordinates membership (BruhatCells.openRepresentative rational)
  rw [open_shift_argument] at bound
  exact (realize_le_cuspSupNorm _ test).trans bound

theorem scalar_cells_summable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Summable (fun rational => boundedRealization data.cusp
      (HilbertCellRealization.cellVector data extension flat parameter argument rational)) := by
  obtain ⟨majorant, _, summable, bounded⟩ := cell_scalar_majorant data extension flat parameter halfPlane argument
  exact summable.of_norm_bounded bounded

def scalarValue {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) : lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  ∑' rational, boundedRealization data.cusp
    (HilbertCellRealization.cellVector data extension flat parameter argument rational)

theorem scalarValue_apply {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (test : BinaryAdelicGL) :
    scalarValue data extension flat parameter argument test =
      ∫ coordinates, ScalarBinaryIntegral.cuspIntegrand data parameter (extension parameter)
        (flat.1 parameter) test argument coordinates ∂radicalMeasure := by
  have integrable := ScalarBinaryIntegral.cuspIntegrand_integrable_of_standard data parameter
    (extension parameter) (flat.1 parameter) test argument
    (CompactScalarConvergence.standard_integrable data extension flat parameter halfPlane (lineLevi 1 test * argument))
  have evaluation := (lp.evalCLM ℂ (fun _ : BinaryAdelicGL => ℂ) ⊤ test).map_tsum
    (scalar_cells_summable data extension flat parameter halfPlane argument)
  change scalarValue data extension flat parameter argument test =
    ∑' rational, data.cusp.realize (HilbertCellRealization.cellVector data extension flat parameter argument rational) test
    at evaluation
  rw [evaluation]
  simp_rw [HilbertCellRealization.cellVector_realizes]
  exact (FundamentalDomain.radicalDomain_fundamental.integral_eq_tsum'' _ integrable).symm

theorem scalarValue_normalized {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (test : BinaryAdelicGL) :
    scalarValue data extension flat parameter argument test =
      normPower (GeneralLinearGroup.det test) (-binaryInductionExponent degree .line parameter) *
        ∫ coordinates, standardIntegrand extension parameter (lineLevi 1 test * argument) coordinates
          ∂radicalMeasure := by
  rw [scalarValue_apply data extension flat parameter halfPlane]
  have formula := ScalarBinaryIntegral.integral_lineLevi_normalized data parameter
    (extension parameter) (flat.1 parameter) test argument
  change (∫ coordinates, standardIntegrand extension parameter (lineLevi 1 test * argument) coordinates
    ∂radicalMeasure) = _ at formula
  rw [formula, ParabolicInvariance.normPower_neg_mul]

theorem scalarValue_fixed {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (unit : LineOrbitLevel.level argument) (test : BinaryAdelicGL) :
    scalarValue data extension flat parameter argument (test * atFinite unit.val) =
      scalarValue data extension flat parameter argument test := by
  obtain ⟨levelElement, translation⟩ := LineOrbitLevel.level_translate argument unit
  have determinantNorm := LineOrbitLevel.level_det_norm_one argument unit
  have normalizer : normPower (GeneralLinearGroup.det (test * atFinite unit.val))
      (-binaryInductionExponent degree .line parameter) =
        normPower (GeneralLinearGroup.det test) (-binaryInductionExponent degree .line parameter) := by
    rw [map_mul, NormPower.normPower_mul_units]
    simp [normPower, determinantNorm]
  have product : lineLevi 1 (test * atFinite unit.val) * argument =
      lineLevi 1 test * argument * atFinite levelElement.val := by
    have multiplication : lineLevi 1 (test * atFinite unit.val) =
        lineLevi 1 test * lineLevi 1 (atFinite unit.val) := by
      simpa only [Prod.mk_mul_mk, one_mul, lineLeviHom, MonoidHom.coe_mk, OneHom.coe_mk]
        using (lineLeviHom Adeles).map_mul (1, test) (1, atFinite unit.val)
    rw [multiplication, mul_assoc, translation, mul_assoc]
  rw [scalarValue_normalized data extension flat parameter halfPlane,
    scalarValue_normalized data extension flat parameter halfPlane, normalizer, product]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with coordinates
  unfold standardIntegrand
  rw [← mul_assoc, (flat.1 parameter).2.1 levelElement]

theorem hilbert_cells_summable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Summable (HilbertTruncation.cellIntegral data extension flat parameter argument) := by
  obtain ⟨majorant, _, summable, bounded⟩ := HilbertTruncation.cell_majorant data extension flat
    parameter.re parameter.re halfPlane halfPlane {argument} isCompact_singleton
  exact summable.of_norm_bounded (fun rational =>
    bounded (parameter, argument) ⟨⟨le_rfl, le_rfl⟩, by simp⟩ rational)

/-- At every maximal-compact base argument, the actual full Hilbert integral
realizes all scalar standard integrals. Finite-mode continuity identifies the
two limits after averaging at the proved common finite level. -/
theorem compact_value_realizes {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re)
    (argument : AdelicGL) (compact : inMaximalCompact argument) (test : BinaryAdelicGL) :
    data.cusp.realize (HilbertStandardSmooth.vector data parameter (extension parameter)
      (flat.1 parameter) halfPlane argument) test =
      ∫ coordinates, ScalarBinaryIntegral.cuspIntegrand data parameter (extension parameter)
        (flat.1 parameter) test argument coordinates ∂radicalMeasure := by
  classical
  let family : Finset (ℚ × ℚ) → data.cusp.smooth := fun finite =>
    ∑ rational ∈ finite, HilbertCellRealization.cellVector data extension flat parameter argument rational
  let vector := HilbertStandardSmooth.vector data parameter (extension parameter) (flat.1 parameter) halfPlane argument
  let target := scalarValue data extension flat parameter argument
  have vectorFixed : vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace
      data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence := by
    intro unit
    exact HilbertFixedStandard.value_fixed data parameter (extension parameter) (flat.1 parameter) argument
      ⟨unit.val, LineOrbitLevel.principal_le_level_of_compact argument compact unit.property⟩
  have targetFixed : ∀ unit : TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence, ∀ point,
      target (point * atFinite unit.val) = target point := by
    intro unit point
    exact scalarValue_fixed data extension flat parameter halfPlane argument
      ⟨unit.val, LineOrbitLevel.principal_le_level_of_compact argument compact unit.property⟩ point
  have hilbertLimit : Tendsto (fun finite => (family finite).val) atTop (𝓝 vector.val) := by
    have sums := (hilbert_cells_summable data extension flat parameter halfPlane argument).hasSum
    rw [HilbertTruncation.cells_sum data extension flat parameter halfPlane argument] at sums
    have equality (finite : Finset (ℚ × ℚ)) : (family finite).val =
        ∑ rational ∈ finite, HilbertTruncation.cellIntegral data extension flat parameter argument rational := by
      change data.cusp.smooth.subtype (∑ rational ∈ finite,
        HilbertCellRealization.cellVector data extension flat parameter argument rational) = _
      rw [map_sum]
      rfl
    simp_rw [equality]
    exact sums
  have scalarLimit : Tendsto (fun finite => boundedRealization data.cusp (family finite)) atTop (𝓝 target) := by
    have sums := (scalar_cells_summable data extension flat parameter halfPlane argument).hasSum
    change Tendsto (fun finite => ∑ rational ∈ finite, boundedRealization data.cusp
      (HilbertCellRealization.cellVector data extension flat parameter argument rational)) atTop (𝓝 target) at sums
    simpa only [family, map_sum] using sums
  have equality := FixedRealizationLimit.principal_limit_unique atTop data family vector vectorFixed
    target targetFixed hilbertLimit scalarLimit
  exact (congrArg (fun value : lp (fun _ : BinaryAdelicGL => ℂ) ⊤ => value test) equality.symm).trans
    (scalarValue_apply data extension flat parameter halfPlane argument test)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertScalarLimit
