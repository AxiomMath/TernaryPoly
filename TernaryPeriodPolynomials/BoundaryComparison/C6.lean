module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.AppendixC6Complete
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.T0Entry
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.CharacterTriviality
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.ReflectionSign
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.ReflectionHecke
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConv.Unique
public import TernaryPeriodPolynomials.SymmetricSolution.ObstructionVanishing.Bernoulli
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.EndpointPull

@[expose] public section


/-!
# Appendix C.6 and Proposition 4.2 along the paper route (parallel export)

The targets `bad_plane_data_injective`, `line_restriction_eq_zero_of_good_vertices`, `symmetric_obstruction_vanishes` are proved (in their own files) through
`ConsumersStd.appendix_C6_complete_std`, whose per-datum detection is `StandardConv.sphericalGoodCuspDetectionConvergent`
(a modified port of the original detection, on the route audit's watch list).  This export proves the same statements
(verbatim) through `FiniteEntries.appendix_C6_complete_ms`, whose per-datum detection is `Entry.perDatumDetectionMS`:
the explicit class-level entry identity (`Entry.classLevel_paper`: the good-line component of `T[bad-plane section]` is the
printed scalar `-2πi/(9(n+1))·L^{(3)}(h,k-2)/L^{(3)}(h,k-1) ≠ 0` times the paper's line section), multiplicity one of the
pair-character eigenspace at the bad-plane cusp (`identityPlane_localUnique`) and the nonvanishing of the good-line cusp
coordinate of the line source (`DetectLine`).  The decomposition into per-datum summands is `PlaneSpanDecomposition`'s;
the separation of Hecke eigencharacters is the explicit Lagrange-interpolation projector of `FiniteEntries.HeckeCluster`
(no existence theorem for isotypical projectors, hence no `BadPlaneInjectivity.Ported*` input), followed by
`FiniteEntries.ClusterDetection.cluster_zero` on each character class; `T₀` is `line_constant_term_comparison`'s map.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Argument.Statements.FiniteEntries

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

/-- **Appendix C.6, injectivity, along the paper route** (the statement of `Targets/AppendixC6.lean`). -/
theorem appendix_C6_ms (n : ℕ) (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T ξ)) : ξ = 0 :=
  FiniteEntries.appendix_C6_complete_ms n hn T hT ξ hξ hgood hline

/-- **Proposition 4.2, boundary form, along the paper route** (the statement of `Targets/Prop42Boundary.lean`). -/
theorem prop_4_2_boundary_ms (n : ℕ) (hn : 4 ≤ n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hline : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2)
    (hgood : GoodBoundaryVanishing n trivialCharacter (globalCoordinates n trivialCharacter c)) :
    (globalCoordinates n trivialCharacter c).2 = 0 := by
  obtain ⟨T, hT1, hT2⟩ := TernaryPeriodPolynomials.line_constant_term_comparison n hn
  have hξP : InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 :=
    TernaryPeriodPolynomials.Argument.Classification.plane_innerBoundary_of_line_innerBoundary n trivialCharacter c hline
  have hTeq : (globalCoordinates n trivialCharacter c).2 =
      T (globalCoordinates n trivialCharacter c).1 :=
    hT2 c hξP hline
  have hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c' = (ξ, T ξ) :=
    fun ξ hξ => (hT1 ξ hξ).2
  have hgood2' :
      VanishesOnGood n trivialCharacter .line (T (globalCoordinates n trivialCharacter c).1) := by
    rw [← hTeq]; exact hgood.2
  have hzero : (globalCoordinates n trivialCharacter c).1 = 0 :=
    appendix_C6_ms n hn T hT (globalCoordinates n trivialCharacter c).1 hξP hgood.1 hgood2'
  rw [hTeq, hzero, map_zero]

/-- **Proposition 4.2 along the paper route** (the statement of `Targets/Prop42.lean`). -/
theorem prop_4_2_ms (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    bernoulliObstruction f = 0 := by
  by_cases hn4 : 4 ≤ n
  · obtain ⟨F, τ, c, hFunc, hPath, hRealizes, hUniq, hgood, hline, hPure, hA, hB, hR, himp⟩ :=
      TernaryPeriodPolynomials.PolynomialBoundaryBridge.polynomial_boundary_bridge n hn f hf
    exact himp (prop_4_2_boundary_ms n hn4 c hline hgood)
  · have hn3 : n ≤ 3 := by omega
    have hhom : f.val.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n f.val).mp f.2
    have hsol : TernaryPoly.Paper.Solution f.val := TernaryPeriodPolynomials.Argument.Classification.symmetricSolution_to_solution f hf
    have hzero : f.val = 0 :=
      (TernaryPeriodPolynomials.solution_homogeneous_symmetric_alternating_parts (F := ℂ)).2.2 n f.val hn3 hhom hsol
    exact TernaryPeriodPolynomials.Argument.Classification.bernoulliObstruction_eq_zero_of_val_eq_zero f hzero

/-- **The per-datum detection** (`Entry.perDatumDetectionMS`). -/
alias per_datum_detection_ms := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.perDatumDetectionMS

/-- **The class-level entry comparison for the paper's constant-term map `T₀`** (`line_constant_term_comparison`'s map, restricted to a summand). -/
alias class_level_paper_T0 := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.classLevel_paper_T0

/-- **`T₀` on the bad-plane section**: printed scalar times the paper's line section. -/
alias T0_bad_plane_good_component := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.T0_badPlane_goodComponent

/-- A rank-one character trivial on the integral units is trivial. -/
alias eq_trivial_character_of_units := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.eq_trivialCharacter_of_units

/-- A nonzero associate pair of even sign has trivial character (the reflection sign is the hypothesis). -/
alias chi_eq_trivial_of_pair_even := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.chi_eq_trivial_of_pair_even

alias exists_spherical_entry_package_of_pair := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.exists_sphericalEntryPackage_of_pair

/-- **formalized.** A class of the plane summand of an arbitrary inducing datum that extends over
`⟨K†, -I₃⟩` and has a nonzero bad-plane coordinate has `χ_∞(-1) = 1`, hence trivial inducing character. -/
alias chi_eq_trivial_of_extended_bad_plane := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.chi_eq_trivial_of_extended_bad_plane

alias even_of_extended_bad_plane := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.even_of_extended_bad_plane

/-- For odd `n` the extended classes of the odd-character strata vanish. -/
alias extended_class_eq_zero_of_odd := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.extended_class_eq_zero_of_odd

/-- The boundary coordinates of every global class of the `χ`-component extend once `reflScalar n χ = 1`. -/
alias global_coordinates_extended := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.globalCoordinates_extended

alias refl_scalar_trivial_odd := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.reflScalar_trivial_odd

alias exists_spherical_entry_package_of_extended :=
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.exists_sphericalEntryPackage_of_extended

/-- Extendedness over `⟨K†, -I₃⟩` is preserved by every realization of the Hecke correspondences. -/
alias is_refl_extended_hecke := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.isReflExtended_hecke

/-- Hecke-character class sums of an extended pair-level family are extended. -/
alias cluster_sum_extended := TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.cluster_sum_extended

/-- The character theorem for a decomposition `ξ = ∑ f D` with extended sum. -/
alias chi_eq_trivial_of_extended_sum_bad_plane :=
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries.chi_eq_trivial_of_extended_sum_bad_plane

/-- The line cocycle of a `RelatedConv` pair is the convergent `sourceStandard` (identity theorem on the half plane). -/
alias related_conv_line_eq_source_standard :=
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConv.relatedConv_line_eq_sourceStandard

/-- Any `T` with `RealizesStandardConv` is `sourceStandard` on classes of plane sources. -/
alias realizes_standard_conv_apply_eq_source_standard :=
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConv.realizesStandardConv_apply_eq_sourceStandard

end TernaryPeriodPolynomials.Argument.Statements.FiniteEntries
