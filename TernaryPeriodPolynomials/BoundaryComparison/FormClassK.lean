module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FormClass
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PlaneCoordinate
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.T
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Cosets
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspSplit
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.BaseCusp
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PlaneSpan
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Cells
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NConstantTerms
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Average
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Radical
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Face
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSection
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NLinear
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedLinear
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedSurj
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CellOrbit
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ZeroFlagsPlane
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NPlaneValues
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ClassicalSeries
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NCanonical
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.SeedSectionDictionary
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NDual
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.DualFlags
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FrameAssembly
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.SlashEquivariance
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.ClassStd
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.CuspBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.CuspNamed
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PlaneIwasawaRational
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.SLSurjective
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ClassicalSection
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.AdelicSection
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RowOrbits
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Final
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.TFormK
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.SectionB
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RealEquivK2

@[expose] public section


/-!
# The `K†`-corestriction of a `Γ(N)` class and the line coordinate (OB7 / G4)

Formalized by Claude Sonnet 5.5.  The paper, Proposition C.5 (`ar:prop:graph`), the constant terms, the descent to `K†`.

**Proved.**  The transfer `H²(Γ ∩ Γ(N), E_n) → H²(K†, E_n)` of a class of `Γ(N)`, and: if the class is locally inner at every rational plane
(vanishing on the stabilizer of every complete flag), then its `K†`-corestriction has `InnerBoundary` plane and line coordinates and its line
coordinate is the canonical map `T` of `line_constant_term_comparison` applied to its plane coordinate (`classK_line_eq_T`).

**Cusp by cusp (`CuspRestriction.lean`, R7 targets M3/M4).**  `resAtC`: restriction of a complex `Γ(N)` class to the plane group `Γ_{h⁻¹Ph}`;
`planeLocallyInner_iff_cusps`: `PlaneLocallyInner x ↔ ∀ h, resAtC h x ∈ faceLocallyInner N h n`; `formClass_planeLocallyInner` (M3 reduction): the summed series class over
cusps and seeds is `PlaneLocallyInner` given `SeriesRestrictionInSeedSpan` (the explicit input from the M1/M2) for each summand, for every tuple of cusp forms;
`formClass_line_eq_T`: hence `r_Q = T(r_P)` at `K†` for the classical series; `res_classK_eq_avg` (M4 averaging formula).

**Plane coordinate and printed `T`.**  `planeCoordinate_formula` (Mackey/conjugation formula: the Shapiro component of the `K†` plane coordinate at `F` is the average over `K†/Γ(N)`
of transfers of the conjugated per-cusp restrictions), `planeCoordinate_component`, `planeCoordinate_congr` (the plane coordinate depends only on the per-cusp restrictions: M4 is
reduced to the per-cusp values); `formClass_line_eq_T0` / `formClass_line_eq_printedT`: `r_Q = T₀ r_P` with `T₀ = (line_constant_term_comparison n hn).choose`, which on classes of plane sources is the printed integral
(the `T0_eq_printed`).

**Flags versus cosets, cusps (`Cosets.lean`, `CuspSplit.lean`).**  `planeFlagAt_eq_iff`, `cosetFlag_injective`, `range_cosetFlag`, `planeFlagAt_orbit_iff`
(orbit relation = the face relation of `PlaneFaces N`), `flagCusp`, `tsum_flags_by_cusp` (sum over flags split by cusp), `stab_planeFlagAt_iff`, `fiberEquiv`.

**Standard-cusp base case (`BaseCusp.lean`, L1/L2).**  `eisensteinAtClass_gammaN_one` (the series at the cusp `ofSL 1` with the holomorphic seed is the literal class),
`resAtC_one_complexify` (`resAtC N 1 ∘ complexify = faceH2Map ∘ complexifyG ∘ resP`), `baseRestriction_eq_faceSeed` / `baseRestriction_in_seedSpan` (one series at one cusp),
`rB_standard` (unconditional `r_B = 0` over the standard plane).  Not `SeriesRestrictionInSeedSpan` for any whole series.

**Plane span (`PlaneSpan.lean`, L9).**  `innerBoundary_plane_mem_span` (`InnerBoundary plane ξ → ξ ∈ automorphicPlaneSpan n`, `0 < n`), `mem_span_exists_sourceClass_sum`
(finite source-class representation), `T0_sum_printed`, `formClass_line_eq_printedT_sum` (printed intertwiner on finite sums, no hypothesis on the plane coordinate beyond `SeriesRestrictionInSeedSpan`).

**Line cells and `Γ(N)`-level constant terms (`LineCells.lean`, `GammaNConstantTerms.lean`).**  `nQ`, `lineRow_nQ`, `cosetMulR_nQ_of_zero`, `cosetMulR_nQ_injective` (the two cells of the line constant term);
`classCG`, `seedBoundary`, the propositions `ClassicalPlaneConstantTerms` / `ClassicalLineConstantTerm` (statements only) and the proved reductions `classicalLine_of_propC5`, `eisensteinP_of_classical`.

**Line face model and averaged class (U2: `LineAverage.lean`, `LineRadical.lean`, `LineFace.lean`).**  `TwistData` / `deRhamClass_avInvT` (the `deRhamClass_avInv` generalized to an arbitrary unipotent radical action and
coefficient representation; the files untouched), `sQ`/`uniRep_sQ` (the radical of `Q` acts on `E_n` by `ρ(qMat v)`, a smooth unipotent representation of `ℝ²`), `lineFaceMap`, `lineFaceForm`, `lineFaceForm_class`
(class of the face pullback = restriction along `ȷ : Γ_P ≃ Γ_Q`), `lineTwist`, **`lineFace_avg_class`** (the radical average of the face pullback represents `r_Q [F]`).

**`eisensteinP` by a linear section (`GammaNSection.lean`).**  `eisensteinP_of_section`: plane constant terms + linearity in the cusp forms (`ClassicalLinearity`, twisted action `TwTuple`) + seed surjectivity give the
`eisensteinP` obligation of `GammaNC5Obligations` with `T = (line coordinate) ∘ ℰ ∘ s`, WITHOUT unfolding the series at the line face; the canonical section-independent `T` needs injectivity of the seed map or the unfolding.

**Linearity and the dual field (`GammaNLinear.lean`).**  `classCG_add`, `classCG_smul` (from the `eisensteinAtClassC_add/_cmul`), `SeedLinearity` (the seed-side half, the L3, not proved here) with
`ClassicalLinearity.of_seed`, and `dualEisenstein_of_section` (the `dualEisenstein` field by a linear section, abstract in the dual classes).

**Unconditional `K†`-level results and `Γ(N)`-level plane constant terms (`Unconditional.lean`, `GammaNPlaneValues.lean`, `GammaNSeedSurj.lean`, `CellOrbit.lean`, `ZeroFlagsPlane.lean`).**  With the `seriesRestrictionInSeedSpan`
(`EisensteinClass/BridgeK`): `formClass_planeLocallyInner_uncond`, `formClass_line_eq_T0_uncond`, `formClass_line_eq_printedT_uncond`, `formClass_line_eq_printedT_sum_uncond`.  At level `Γ(N)`: `cell_exists_iff`, `no_cell_of_ne`, `cell_self`
(orbit combinatorics of the cells), `zeroFlags_of_plane_mixed`, `seedLinearity`, `classicalLinearity`, `seedBoundary_surjective`, **`classicalPlaneConstantTerms`** (`r_B = 0` and `r_P ℰ_P(ξ) = ξ` at every plane face, `3 ≤ N`, `4 ≤ n`)
and **`eisensteinP_gammaN`** (the `eisensteinP` obligation, unconditional).

NOT proved: (i) the unfolding of the series at the line face, hence the literal identification of `r_Q ℰ_P(ξ)` with the printed intertwiner AT LEVEL `Γ(N)` and the canonicity of `T`
(Eichler-Shimura injectivity); (ii) the classical-seed to adelic-section dictionary (the finite source family of `formClass_line_eq_printedT_sum_uncond` is existential); (iii) the dual field `dualEisenstein` of the obligations
beyond the abstract `dualEisenstein_of_section`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FormClassK

open TernaryPeriodPolynomials.Argument

alias faceRestriction_trToLevel_eq_zero := TernaryPeriodPolynomials.Argument.FormClassK.faceRestriction_trToLevel_eq_zero
alias innerBoundary_of_edgeVanishing := TernaryPeriodPolynomials.Argument.FormClassK.innerBoundary_of_edgeVanishing
alias lineCoordinate_eq_of_edgeVanishing := TernaryPeriodPolynomials.Argument.FormClassK.lineCoordinate_eq_of_edgeVanishing
alias principalEquiv := TernaryPeriodPolynomials.Argument.FormClassK.principalEquiv
alias classPrincipal := TernaryPeriodPolynomials.Argument.FormClassK.classPrincipal
alias principalIso_inv_classPrincipal := TernaryPeriodPolynomials.Argument.FormClassK.principalIso_inv_classPrincipal
alias classK := TernaryPeriodPolynomials.Argument.FormClassK.classK
alias PlaneLocallyInner := TernaryPeriodPolynomials.Argument.FormClassK.PlaneLocallyInner
alias classK_edge_vanishing := TernaryPeriodPolynomials.Argument.FormClassK.classK_edge_vanishing
alias classK_line_eq_T := TernaryPeriodPolynomials.Argument.FormClassK.classK_line_eq_T
alias resAtC := TernaryPeriodPolynomials.Argument.FormClassK.resAtC
alias planeLocallyInner_iff_cusps := TernaryPeriodPolynomials.Argument.FormClassK.planeLocallyInner_iff_cusps
alias SeriesRestrictionInSeedSpan := TernaryPeriodPolynomials.Argument.FormClassK.SeriesRestrictionInSeedSpan
alias formClass_planeLocallyInner := TernaryPeriodPolynomials.Argument.FormClassK.formClass_planeLocallyInner
alias formClass_line_eq_T := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_T
alias res_classK_eq_avg := TernaryPeriodPolynomials.Argument.FormClassK.res_classK_eq_avg
alias planeCoordinate_formula := TernaryPeriodPolynomials.Argument.FormClassK.planeCoordinate_formula
alias planeCoordinate_component := TernaryPeriodPolynomials.Argument.FormClassK.planeCoordinate_component
alias planeCoordinate_congr := TernaryPeriodPolynomials.Argument.FormClassK.planeCoordinate_congr
alias formClass_line_eq_T0 := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_T0
alias formClass_line_eq_printedT := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_printedT
alias planeFlagAt_eq_iff := TernaryPeriodPolynomials.Argument.FormClassK.planeFlagAt_eq_iff
alias cosetFlag := TernaryPeriodPolynomials.Argument.FormClassK.cosetFlag
alias cosetFlag_injective := TernaryPeriodPolynomials.Argument.FormClassK.cosetFlag_injective
alias range_cosetFlag := TernaryPeriodPolynomials.Argument.FormClassK.range_cosetFlag
alias planeFlagAt_orbit_iff := TernaryPeriodPolynomials.Argument.FormClassK.planeFlagAt_orbit_iff
alias flagCusp := TernaryPeriodPolynomials.Argument.FormClassK.flagCusp
alias tsum_flags_by_cusp := TernaryPeriodPolynomials.Argument.FormClassK.tsum_flags_by_cusp
alias stab_planeFlagAt_iff := TernaryPeriodPolynomials.Argument.FormClassK.stab_planeFlagAt_iff
alias fiberEquiv := TernaryPeriodPolynomials.Argument.FormClassK.fiberEquiv
alias eisensteinAtClass_gammaN_one := TernaryPeriodPolynomials.Argument.FormClassK.eisensteinAtClass_gammaN_one
alias faceH2Map := TernaryPeriodPolynomials.Argument.FormClassK.faceH2Map
alias resAtC_one_complexify := TernaryPeriodPolynomials.Argument.FormClassK.resAtC_one_complexify
alias baseRestriction_eq_faceSeed := TernaryPeriodPolynomials.Argument.FormClassK.baseRestriction_eq_faceSeed
alias baseRestriction_in_seedSpan := TernaryPeriodPolynomials.Argument.FormClassK.baseRestriction_in_seedSpan
alias rB_standard := TernaryPeriodPolynomials.Argument.FormClassK.rB_standard
alias innerBoundary_plane_mem_span := TernaryPeriodPolynomials.Argument.FormClassK.innerBoundary_plane_mem_span
alias mem_span_exists_sourceClass_sum := TernaryPeriodPolynomials.Argument.FormClassK.mem_span_exists_sourceClass_sum
alias T0_sum_printed := TernaryPeriodPolynomials.Argument.FormClassK.T0_sum_printed
alias formClass_line_eq_printedT_sum := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_printedT_sum
alias nQ := TernaryPeriodPolynomials.Argument.FormClassK.nQ
alias lineRow_nQ := TernaryPeriodPolynomials.Argument.FormClassK.lineRow_nQ
alias cosetMulR_nQ_of_zero := TernaryPeriodPolynomials.Argument.FormClassK.cosetMulR_nQ_of_zero
alias cosetMulR_nQ_injective := TernaryPeriodPolynomials.Argument.FormClassK.cosetMulR_nQ_injective
alias classCG := TernaryPeriodPolynomials.Argument.FormClassK.classCG
alias seedBoundary := TernaryPeriodPolynomials.Argument.FormClassK.seedBoundary
alias ClassicalPlaneConstantTerms := TernaryPeriodPolynomials.Argument.FormClassK.ClassicalPlaneConstantTerms
alias ClassicalLineConstantTerm := TernaryPeriodPolynomials.Argument.FormClassK.ClassicalLineConstantTerm
alias classicalLine_of_propC5 := TernaryPeriodPolynomials.Argument.FormClassK.classicalLine_of_propC5
alias eisensteinP_of_classical := TernaryPeriodPolynomials.Argument.FormClassK.eisensteinP_of_classical
alias deRhamClass_avInvT := TernaryPeriodPolynomials.Argument.FormClassK.TwistData.deRhamClass_avInvT
alias uniRep_sQ := TernaryPeriodPolynomials.Argument.FormClassK.uniRep_sQ
alias lineFaceMap := TernaryPeriodPolynomials.Argument.FormClassK.lineFaceMap
alias lineFaceForm := TernaryPeriodPolynomials.Argument.FormClassK.lineFaceForm
alias lineFaceForm_class := TernaryPeriodPolynomials.Argument.FormClassK.lineFaceForm_class
alias lineFace_avg_class := TernaryPeriodPolynomials.Argument.FormClassK.lineFace_avg_class
alias TwTuple := TernaryPeriodPolynomials.Argument.FormClassK.TwTuple
alias ClassicalLinearity := TernaryPeriodPolynomials.Argument.FormClassK.ClassicalLinearity
alias eisensteinP_of_section := TernaryPeriodPolynomials.Argument.FormClassK.eisensteinP_of_section
alias classCG_add := TernaryPeriodPolynomials.Argument.FormClassK.classCG_add
alias classCG_smul := TernaryPeriodPolynomials.Argument.FormClassK.classCG_smul
alias SeedLinearity := TernaryPeriodPolynomials.Argument.FormClassK.SeedLinearity
alias dualEisenstein_of_section := TernaryPeriodPolynomials.Argument.FormClassK.dualEisenstein_of_section
alias formClass_planeLocallyInner_uncond := TernaryPeriodPolynomials.Argument.FormClassK.formClass_planeLocallyInner_uncond
alias formClass_line_eq_T0_uncond := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_T0_uncond
alias formClass_line_eq_printedT_uncond := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_printedT_uncond
alias formClass_line_eq_printedT_sum_uncond := TernaryPeriodPolynomials.Argument.FormClassK.formClass_line_eq_printedT_sum_uncond
alias cell_exists_iff := TernaryPeriodPolynomials.Argument.FormClassK.cell_exists_iff
alias no_cell_of_ne := TernaryPeriodPolynomials.Argument.FormClassK.no_cell_of_ne
alias cell_self := TernaryPeriodPolynomials.Argument.FormClassK.cell_self
alias zeroFlags_of_plane_mixed := TernaryPeriodPolynomials.Argument.FormClassK.zeroFlags_of_plane_mixed
alias classicalLinearity := TernaryPeriodPolynomials.Argument.FormClassK.classicalLinearity
alias seedBoundary_surjective := TernaryPeriodPolynomials.Argument.FormClassK.seedBoundary_surjective
alias classicalPlaneConstantTerms := TernaryPeriodPolynomials.Argument.FormClassK.classicalPlaneConstantTerms
alias eisensteinP_gammaN := TernaryPeriodPolynomials.Argument.FormClassK.eisensteinP_gammaN
alias SeedMapInjective := TernaryPeriodPolynomials.Argument.FormClassK.SeedMapInjective
alias classicalLine_of_seedInjective := TernaryPeriodPolynomials.Argument.FormClassK.classicalLine_of_seedInjective
alias classCG_line_mixed := TernaryPeriodPolynomials.Argument.FormClassK.classCG_line_mixed
alias transferred_seeds_are_source_sum := TernaryPeriodPolynomials.Argument.FormClassK.transferred_seeds_are_source_sum
alias formClass_plane_inner := TernaryPeriodPolynomials.Argument.FormClassK.formClass_plane_inner
alias formClass_plane_coordinate_named := TernaryPeriodPolynomials.Argument.FormClassK.formClass_plane_coordinate_named
alias no_dual_cell_of_ne := TernaryPeriodPolynomials.Argument.FormClassK.no_dual_cell_of_ne
alias dualS_surjective := TernaryPeriodPolynomials.Argument.FormClassK.dualS_surjective
alias dualRQ_dualEH := TernaryPeriodPolynomials.Argument.FormClassK.dualRQ_dualEH
alias dualEisenstein_gammaN := TernaryPeriodPolynomials.Argument.FormClassK.dualEisenstein_gammaN
alias DualZeroFlags := TernaryPeriodPolynomials.Argument.FormClassK.DualZeroFlags
alias resToC_cxGen := TernaryPeriodPolynomials.Argument.FormClassK.resToC_cxGen
alias dualClassC_zeroFlags := TernaryPeriodPolynomials.Argument.FormClassK.dualClassC_zeroFlags
alias dualZeroFlagsSubmodule := TernaryPeriodPolynomials.Argument.FormClassK.dualZeroFlagsSubmodule
alias Hd_zeroFlags := TernaryPeriodPolynomials.Argument.FormClassK.Hd_zeroFlags
alias faceObligations_of_frame := TernaryPeriodPolynomials.Argument.FormClassK.faceObligations_of_frame
alias Fh_sl2_mul_slash := TernaryPeriodPolynomials.Argument.FormClassK.Fh_sl2_mul_slash
alias lineIso := TernaryPeriodPolynomials.Argument.FormClassK.lineIso
alias lineIsoPull := TernaryPeriodPolynomials.Argument.FormClassK.lineIsoPull
alias lineIsoPull_rLine := TernaryPeriodPolynomials.Argument.FormClassK.lineIsoPull_rLine
alias lineStd_series_class := TernaryPeriodPolynomials.Argument.FormClassK.lineStd_series_class
alias lineStd_series := TernaryPeriodPolynomials.Argument.FormClassK.lineStd_series
alias lineAtHom := TernaryPeriodPolynomials.Argument.FormClassK.lineAtHom
alias lineAtMor := TernaryPeriodPolynomials.Argument.FormClassK.lineAtMor
alias lineCuspForm := TernaryPeriodPolynomials.Argument.FormClassK.lineCuspForm
alias lineCuspForm_eq_twist := TernaryPeriodPolynomials.Argument.FormClassK.lineCuspForm_eq_twist
alias lineCusp_class_real := TernaryPeriodPolynomials.Argument.FormClassK.lineCusp_class_real
alias rLine_series_cusp := TernaryPeriodPolynomials.Argument.FormClassK.rLine_series_cusp
alias lineFaceForm_class_eq_avg := TernaryPeriodPolynomials.Argument.FormClassK.lineFaceForm_class_eq_avg
alias series_zeroFlags := TernaryPeriodPolynomials.Argument.FormClassK.series_zeroFlags
alias series_line_mixed := TernaryPeriodPolynomials.Argument.FormClassK.series_line_mixed
alias seriesLineCusp := TernaryPeriodPolynomials.Argument.FormClassK.seriesLineCusp
alias seriesLineCusp_spec := TernaryPeriodPolynomials.Argument.FormClassK.seriesLineCusp_spec
alias TclLine := TernaryPeriodPolynomials.Argument.FormClassK.TclLine
alias lineCuspSumEmbedding_TclLine := TernaryPeriodPolynomials.Argument.FormClassK.lineCuspSumEmbedding_TclLine
alias exists_rational_approx := TernaryPeriodPolynomials.Argument.FormClassK.exists_rational_approx
alias exists_rational_unit := TernaryPeriodPolynomials.Argument.FormClassK.exists_rational_unit
alias plane_rational_decomp := TernaryPeriodPolynomials.Argument.FormClassK.plane_rational_decomp
alias sl2_map_surjective := TernaryPeriodPolynomials.Argument.FormClassK.sl2_map_surjective
alias sl3_map_surjective := TernaryPeriodPolynomials.Argument.FormClassK.sl3_map_surjective
alias sectionClR := TernaryPeriodPolynomials.Argument.FormClassK.sectionClR
alias sectionCl_planeStab_mul := TernaryPeriodPolynomials.Argument.FormClassK.sectionCl_planeStab_mul
alias sectionCl_neg_mul := TernaryPeriodPolynomials.Argument.FormClassK.sectionCl_neg_mul
alias sectionCl_gammaNP_mul := TernaryPeriodPolynomials.Argument.FormClassK.sectionCl_gammaNP_mul
alias sectionCl_mul_right := TernaryPeriodPolynomials.Argument.FormClassK.sectionCl_mul_right
alias finComp_eq_iff := TernaryPeriodPolynomials.Argument.FormClassK.finComp_eq_iff
alias sectionCl_finComp := TernaryPeriodPolynomials.Argument.FormClassK.sectionCl_finComp
alias PhiQ0_eq_sectionClR := TernaryPeriodPolynomials.Argument.FormClassK.PhiQ0_eq_sectionClR
alias finiteGL_eq_planeRational_mul_integral := TernaryPeriodPolynomials.Argument.FormClassK.finiteGL_eq_planeRational_mul_integral
alias gammaN_of_rat_levelKernel := TernaryPeriodPolynomials.Argument.FormClassK.gammaN_of_rat_levelKernel
alias decomp_ratio := TernaryPeriodPolynomials.Argument.FormClassK.decomp_ratio
alias adelicSection := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection
alias adelicSection_of_decomp := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_of_decomp
alias adelicSection_mul_ker := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_mul_ker
alias adelicSection_planeDet_mul := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_planeDet_mul
alias adelicSection_rational := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_rational
alias finiteMeasure_latSet := TernaryPeriodPolynomials.Argument.FormClassK.finiteMeasure_latSet
alias adelicSection_gFin_add_lat := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_gFin_add_lat
alias decomp_gFin := TernaryPeriodPolynomials.Argument.FormClassK.decomp_gFin
alias adelicSection_gFin_rational := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_gFin_rational
alias orbit_of_pt_shift := TernaryPeriodPolynomials.Argument.FormClassK.orbit_of_pt_shift
alias exists_elt_of_decomp := TernaryPeriodPolynomials.Argument.FormClassK.exists_elt_of_decomp
alias radicalEquiv_measurePreserving := TernaryPeriodPolynomials.Argument.FormClassK.radicalEquiv_measurePreserving
alias integral_factorizable := TernaryPeriodPolynomials.Argument.FormClassK.integral_factorizable
alias pieceFin_disjoint := TernaryPeriodPolynomials.Argument.FormClassK.pieceFin_disjoint
alias volume_pieceFin := TernaryPeriodPolynomials.Argument.FormClassK.volume_pieceFin
alias exists_orbit_of_decomp := TernaryPeriodPolynomials.Argument.FormClassK.exists_orbit_of_decomp
alias printedIntegrand := TernaryPeriodPolynomials.Argument.FormClassK.printedIntegrand
alias Fz_on_piece := TernaryPeriodPolynomials.Argument.FormClassK.Fz_on_piece
alias Fz_integral := TernaryPeriodPolynomials.Argument.FormClassK.Fz_integral
alias printed_intertwiner_eval := TernaryPeriodPolynomials.Argument.FormClassK.printed_intertwiner_eval
alias printed_intertwiner_cells := TernaryPeriodPolynomials.Argument.FormClassK.printed_intertwiner_cells
alias printed_intertwiner_orbit_sum := TernaryPeriodPolynomials.Argument.FormClassK.printed_intertwiner_orbit_sum
alias printed_intertwiner_Yn := TernaryPeriodPolynomials.Argument.FormClassK.printed_intertwiner_Yn
alias printedCoeff_eq_integral := TernaryPeriodPolynomials.Argument.FormClassK.printedCoeff_eq_integral
alias rLine_series_integral := TernaryPeriodPolynomials.Argument.FormClassK.rLine_series_integral
alias adelicSectionB := TernaryPeriodPolynomials.Argument.FormClassK.adelicSectionB
alias adelicSectionB_of_decomp := TernaryPeriodPolynomials.Argument.FormClassK.adelicSectionB_of_decomp
alias adelicSectionB_mul_ker := TernaryPeriodPolynomials.Argument.FormClassK.adelicSectionB_mul_ker
alias adelicSectionB_planeDet_mul := TernaryPeriodPolynomials.Argument.FormClassK.adelicSectionB_planeDet_mul
alias exists_elt_of_decompK := TernaryPeriodPolynomials.Argument.FormClassK.exists_elt_of_decompK
alias adelicSection_gFin_rational_K := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_gFin_rational_K
alias orbit_of_pt_shift_elt_K := TernaryPeriodPolynomials.Argument.FormClassK.orbit_of_pt_shift_elt_K
alias pieceFinK_disjoint := TernaryPeriodPolynomials.Argument.FormClassK.pieceFinK_disjoint
alias exists_orbit_of_decompK := TernaryPeriodPolynomials.Argument.FormClassK.exists_orbit_of_decompK
alias FzK_on_piece := TernaryPeriodPolynomials.Argument.FormClassK.FzK_on_piece
alias cells_integral := TernaryPeriodPolynomials.Argument.FormClassK.cells_integral
alias FzK_integral := TernaryPeriodPolynomials.Argument.FormClassK.FzK_integral
alias adelicOf := TernaryPeriodPolynomials.Argument.FormClassK.adelicOf
alias printed_intertwiner_evalK := TernaryPeriodPolynomials.Argument.FormClassK.printed_intertwiner_evalK
alias printedIntegrand_adelicOf_ker := TernaryPeriodPolynomials.Argument.FormClassK.printedIntegrand_adelicOf_ker
alias rLine_series_integralK := TernaryPeriodPolynomials.Argument.FormClassK.rLine_series_integralK
alias PsiCoefQ_expansion := TernaryPeriodPolynomials.Argument.FormClassK.PsiCoefQ_expansion
alias PsiCoefQ_continuous_bound := TernaryPeriodPolynomials.Argument.FormClassK.PsiCoefQ_continuous_bound
alias FzE_integral := TernaryPeriodPolynomials.Argument.FormClassK.FzE_integral
alias TcoefK := TernaryPeriodPolynomials.Argument.FormClassK.TcoefK
alias TcoefK_integrable := TernaryPeriodPolynomials.Argument.FormClassK.TcoefK_integrable
alias TcoefK_value := TernaryPeriodPolynomials.Argument.FormClassK.TcoefK_value
alias TformK := TernaryPeriodPolynomials.Argument.FormClassK.TformK
alias coeff_TformK := TernaryPeriodPolynomials.Argument.FormClassK.coeff_TformK
alias fPull_TformK := TernaryPeriodPolynomials.Argument.FormClassK.fPull_TformK
alias adelicOfPair := TernaryPeriodPolynomials.Argument.FormClassK.adelicOfPair
alias adelicSection_mul_real := TernaryPeriodPolynomials.Argument.FormClassK.adelicSection_mul_real
alias TcoefG := TernaryPeriodPolynomials.Argument.FormClassK.TcoefG
alias TcoefG_eq := TernaryPeriodPolynomials.Argument.FormClassK.TcoefG_eq
alias coeff_rho_formPullback := TernaryPeriodPolynomials.Argument.FormClassK.coeff_rho_formPullback

end TernaryPeriodPolynomials.Argument.Statements.FormClassK
