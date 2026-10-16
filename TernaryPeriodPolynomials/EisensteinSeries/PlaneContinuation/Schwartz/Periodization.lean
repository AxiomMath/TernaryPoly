module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.AffineBounds

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzPeriodization

noncomputable def integerVector (integer : Coordinate → ℤ) : RealSpace :=
  WithLp.toLp 2 (fun coordinate => (integer coordinate : ℝ))

noncomputable def latticeVector (integer : Coordinate → ℤ) : integerLattice :=
  ⟨integerVector integer, integerVector_mem_lattice integer⟩

theorem latticeVector_injective : Function.Injective latticeVector := by
  intro first second equality
  funext coordinate
  exact Int.cast_injective (congrArg (fun vector : integerLattice => vector.val coordinate) equality)

theorem integerVector_add (first second : Coordinate → ℤ) :
    integerVector (first + second) = integerVector first + integerVector second := by
  ext coordinate
  exact Int.cast_add _ _

theorem integerVector_zero : integerVector 0 = 0 := by
  ext coordinate
  exact Int.cast_zero

noncomputable def periodization (function : SchwartzMap RealSpace ℂ) (offset : RealSpace) : ℂ :=
  ∑' integer : Coordinate → ℤ, function (offset + integerVector integer)

theorem exists_majorant (function : SchwartzMap RealSpace ℂ) (compact : Set RealSpace) (compactIs : IsCompact compact) :
    ∃ majorant : (Coordinate → ℤ) → ℝ, Summable majorant ∧ (∀ integer, 0 ≤ majorant integer) ∧
      ∀ offset ∈ compact, ∀ integer, ‖function (offset + integerVector integer)‖ ≤ majorant integer := by
  obtain ⟨majorant, summableMajorant, nonnegative, bounded⟩ :=
    SchwartzAffineBounds.exists_translate_majorant integerLattice function compact compactIs
  exact ⟨fun integer => majorant (latticeVector integer), summableMajorant.comp_injective latticeVector_injective,
    fun integer => nonnegative (latticeVector integer), fun offset membership integer => bounded offset membership (latticeVector integer)⟩

theorem summable_norm (function : SchwartzMap RealSpace ℂ) (offset : RealSpace) :
    Summable (fun integer : Coordinate → ℤ => ‖function (offset + integerVector integer)‖) := by
  obtain ⟨majorant, summableMajorant, _, bounded⟩ := exists_majorant function {offset} isCompact_singleton
  exact summableMajorant.of_nonneg_of_le (fun _ => norm_nonneg _) (bounded offset (Set.mem_singleton offset))

theorem summable (function : SchwartzMap RealSpace ℂ) (offset : RealSpace) :
    Summable (fun integer : Coordinate → ℤ => function (offset + integerVector integer)) :=
  (summable_norm function offset).of_norm

theorem continuousOn_compact (function : SchwartzMap RealSpace ℂ) (compact : Set RealSpace) (compactIs : IsCompact compact) :
    ContinuousOn (periodization function) compact := by
  obtain ⟨majorant, summableMajorant, _, bounded⟩ := exists_majorant function compact compactIs
  exact continuousOn_tsum (fun integer => (function.continuous.comp (continuous_id.add continuous_const)).continuousOn)
    summableMajorant (fun integer offset membership => bounded offset membership integer)

theorem continuous (function : SchwartzMap RealSpace ℂ) : Continuous (periodization function) := by
  apply continuous_iff_continuousAt.mpr
  intro offset
  obtain ⟨compact, compactIs, neighborhood⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds offset
  exact (continuousOn_compact function compact compactIs).continuousAt neighborhood

theorem integer_invariant (function : SchwartzMap RealSpace ℂ) (offset : RealSpace) (integer : Coordinate → ℤ) :
    periodization function (offset + integerVector integer) = periodization function offset := by
  unfold periodization
  calc
    ∑' other : Coordinate → ℤ, function (offset + integerVector integer + integerVector other) =
        ∑' other : Coordinate → ℤ, function (offset + integerVector (integer + other)) := by
      apply tsum_congr
      intro other
      rw [integerVector_add, add_assoc]
    _ = ∑' other : Coordinate → ℤ, function (offset + integerVector other) :=
      (Equiv.addLeft integer).tsum_eq (fun other => function (offset + integerVector other))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzPeriodization
