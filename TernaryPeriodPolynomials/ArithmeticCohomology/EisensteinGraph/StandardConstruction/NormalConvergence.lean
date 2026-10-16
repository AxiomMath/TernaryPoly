module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.Majorant
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatJointContinuity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.NormalConvergence

theorem strip_compact_majorant {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ∃ majorant : Flags .plane → ℝ, (∀ flag, 0 ≤ majorant flag) ∧ Summable majorant ∧
      ∀ pair ∈ {parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set, ∀ flag,
        ‖eisensteinSummand extension pair.1 pair.2 flag‖ ≤ majorant flag := by
  obtain ⟨lowerMajorant, lowerNonnegative, lowerSummable, lowerBounded⟩ :=
    CompactMajorant.scalar_majorant data extension flat bound bounded
      (lower : ℂ) lowerHalfPlane set compact
  obtain ⟨upperMajorant, upperNonnegative, upperSummable, upperBounded⟩ :=
    CompactMajorant.scalar_majorant data extension flat bound bounded
      (upper : ℂ) upperHalfPlane set compact
  refine ⟨fun flag => lowerMajorant flag + upperMajorant flag,
    fun flag => add_nonneg (lowerNonnegative flag) (upperNonnegative flag),
    lowerSummable.add upperSummable, ?_⟩
  intro pair membership flag
  exact (FlatNormStrip.summand_strip_bound data extension flat pair.2 flag lower upper pair.1
    membership.1.1 membership.1.2).trans
      (add_le_add (lowerBounded pair.2 membership.2 flag) (upperBounded pair.2 membership.2 flag))

theorem summand_joint_continuous {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (flag : Flags .plane) :
    Continuous (fun pair : ℂ × AdelicGL => eisensteinSummand extension pair.1 pair.2 flag) :=
  (FlatJointContinuity.joint_continuous data extension flat).comp
    (continuous_fst.prodMk (continuous_const.mul continuous_snd))

theorem uniformOn_strip_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    TendstoUniformlyOn
      (fun finite : Finset (Flags .plane) => fun pair : ℂ × AdelicGL =>
        ∑ flag ∈ finite, eisensteinSummand extension pair.1 pair.2 flag)
      (fun pair => ∑' flag : Flags .plane, eisensteinSummand extension pair.1 pair.2 flag)
      atTop ({parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set) := by
  obtain ⟨majorant, _, summable, dominates⟩ := strip_compact_majorant data extension flat bound bounded
    lower upper lowerHalfPlane upperHalfPlane set compact
  exact tendstoUniformlyOn_tsum summable (fun flag pair membership => dominates pair membership flag)

theorem continuousOn_strip_compact {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 < lower)
    (upperHalfPlane : -(degree : ℝ) / 2 < upper)
    (set : Set AdelicGL) (compact : IsCompact set) :
    ContinuousOn (fun pair : ℂ × AdelicGL => ∑' flag : Flags .plane,
      eisensteinSummand extension pair.1 pair.2 flag)
      ({parameter : ℂ | lower ≤ parameter.re ∧ parameter.re ≤ upper} ×ˢ set) := by
  obtain ⟨majorant, _, summable, dominates⟩ := strip_compact_majorant data extension flat bound bounded
    lower upper lowerHalfPlane upperHalfPlane set compact
  exact continuousOn_tsum (fun flag => (summand_joint_continuous data extension flat flag).continuousOn)
    summable (fun flag pair membership => dominates pair membership flag)

theorem continuousAt_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound)
    (parameter : ℂ) (argument : AdelicGL) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    ContinuousAt (fun pair : ℂ × AdelicGL => ∑' flag : Flags .plane,
      eisensteinSummand extension pair.1 pair.2 flag) (parameter, argument) := by
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
  apply (continuousOn_strip_compact data extension flat bound bounded lower upper
    lowerHalfPlane upperHalfPlane set compact).continuousAt
  exact prod_mem_nhds stripNeighborhood neighborhood

theorem continuousOn_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (bound : ℝ)
    (bounded : ∀ compactElement, inMaximalCompact compactElement → ∀ binary,
      ‖data.cusp.realize (CuspLift.vector data .plane cohomologicalPoint
        (extension cohomologicalPoint) (flat.1 cohomologicalPoint) compactElement) binary‖ ≤ bound) :
    ContinuousOn (fun pair : ℂ × AdelicGL => ∑' flag : Flags .plane,
      eisensteinSummand extension pair.1 pair.2 flag)
      {pair | -(degree : ℝ) / 2 < pair.1.re} :=
  fun pair membership => (continuousAt_halfPlane data extension flat bound bounded
    pair.1 pair.2 membership).continuousWithinAt

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.NormalConvergence
