module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.RestrictionFinal
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConv.Related
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceQuotient
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Relation
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.PlaneInner
public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.TEliminate

@[expose] public section


/-!
# A per-datum standard-realizing map, built as `line_constant_term_comparison`'s `T₀` restricted to the summand

Parts (a)+(b), done as a single construction: rather than building a
fresh per-datum operator from `StandardExistence.lean`'s pointwise witnesses (which would need
`StandardRelation.descendedStandard`'s `respectsRelations` hypothesis, and the *only* existing
proof of a `respectsRelations`-shaped fact is inside `GraphReduction.standard_graph_of_eisenstein`,
hence needs `HalfDimension`), `standardFromT0Std` is simply any fixed uniqueness-clause map `T₀`

(`TEliminate.lean`'s `IsUniquenessMap`, e.g. `line_constant_term_comparison`'s own canonical map), restricted and
corestricted to one datum's plane/line summands. Agreement with `T₀` (part (b)) is then not a
separate fact: it is what the restriction literally is. `RealizesStandard` (part (a)) follows from
`StandardRelation.realizesStandard_iff` plus the per-generator identity `T₀_sourceClass_eq_std`, which
combines the unconditional `ConstantTerm.restrictionFormula` with `CuspidalSpan.
boundarySummand_plane_subset_innerBoundary` (plane side) and this directory's own
`EdgePullback.line_innerBoundary_of_plane_innerBoundary` (line side) to invoke `T₀`'s own
uniqueness clause.

Change by Claude Sonnet 5.5: the plane Eisenstein hypothesis is now the
continuation-free `ConvergentEisenstein.PlaneEisensteinConvergent` (degree at least four, flat
extensions), and the restriction formula, global cocycle and standard line cocycle are the
convergent versions of `Revision/Proofs/ConvergentEisenstein`; no meromorphic continuation of the
plane Eisenstein operators is used.

Variant by Claude Sonnet 5.5 of `Consumers/StandardFromT0Conv.lean` in which the
predicate `RealizesStandard` (meromorphic continuation of the standard operator to the
whole plane) is replaced by `RealizesStandardConv` (meromorphic on the half plane `-n/2 < Re s` of
absolute convergence); the standard line cocycle is related to the plane cocycle by
`StandardConv.sourceStandard_relatedConv`, and the detection is
`StandardConv.sphericalGoodCuspDetectionConvergent`.  Names carry the suffix `Std`/`_std`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous


namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd

open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Argument.CuspidalSpan

/-- The coercion of `sourceToSummand` is literally `sourceClass`: `sourceToSummand` is defined as
a `codRestrict` of `sourceClass`, so this is definitional. Naming it lets later proofs `rw`
through the corestriction wrapper without re-unfolding it at every call site. -/
theorem sourceToSummand_val_std {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceSpace.sourceCocycles data side) :
    (SourceQuotient.sourceToSummand data side source).val =
      SourceSpace.sourceClass data side source := by
  simp [SourceQuotient.sourceToSummand, LinearMap.codRestrict_apply]

variable {n : ℕ} (D : CohomologicalCuspData n) (large : 4 ≤ n)
  (hhol : ConvergentEisenstein.PlaneEisensteinConvergent D.inducingData)
  (T₀ : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
  (hT₀ : IsUniquenessMap n trivialCharacter T₀)





include large hhol T₀ hT₀

/-- **Per-generator identity**: `T₀` agrees with the standard continuation map on the class of
every plane source cocycle of `D`. Combines the unconditional `restrictionFormula` with the
plane-side `InnerBoundary` fact from `CuspidalSpan.lean` and the line-side one from
`EdgePullback.lean`, fed into `T₀`'s own uniqueness clause `hT₀`. This is the bridge: `RestrictionFormula` alone only gives *a* pair of plane/line classes with equal global
coordinates, not that `T₀` agrees with the line coordinate; feeding that pair through `hT₀`
(which needs both sides' `InnerBoundary`) supplies exactly that. -/
theorem T₀_sourceClass_eq_std (plane : SourceSpace.sourceCocycles D.inducingData .plane) :
    T₀ (SourceSpace.sourceClass D.inducingData .plane plane) =
      SourceSpace.sourceClass D.inducingData .line
        (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData large hhol plane) := by
  have hc : globalCoordinates n trivialCharacter
      (ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle D.inducingData hhol large plane) =
      (SourceSpace.sourceClass D.inducingData .plane plane,
        SourceSpace.sourceClass D.inducingData .line
          (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData large hhol plane)) :=
    ConvergentEisenstein.ConstantTerm.restrictionFormula
      large D.inducingData hhol plane
  have hplane : InnerBoundary n trivialCharacter .plane
      (globalCoordinates n trivialCharacter
        (ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle D.inducingData hhol large plane)).1 := by
    rw [hc]
    exact boundarySummand_plane_subset_innerBoundary D.inducingData
      (SourceQuotient.sourceToSummand D.inducingData .plane plane).property
  have hline : InnerBoundary n trivialCharacter .line
      (globalCoordinates n trivialCharacter
        (ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle D.inducingData hhol large plane)).2 :=
    line_innerBoundary_of_plane_innerBoundary n trivialCharacter
      (ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle D.inducingData hhol large plane) hplane
  have hres := hT₀ (ConvergentEisenstein.EndpointEisensteinCocycle.globalCocycle D.inducingData hhol large plane)
    hplane hline
  rw [hc] at hres
  exact hres.symm

/-- **Codomain membership**: `T₀` maps every class in `D`'s plane summand into `D`'s line summand.
No well-definedness/choice argument is needed: `sourceToSummand_surjective` only supplies *some*
preimage, which is enough since `T₀` is already fixed and `T₀_sourceClass_eq_std` holds for every
generator uniformly. -/
theorem T₀_mapsTo_std (x : boundarySummand D.inducingData .plane) :
    T₀ x.val ∈ boundarySummand D.inducingData .line := by
  obtain ⟨plane, hplane⟩ := SourceQuotient.sourceToSummand_surjective D.inducingData .plane x
  rw [← hplane, sourceToSummand_val_std, T₀_sourceClass_eq_std D large hhol T₀ hT₀ plane,
    ← sourceToSummand_val_std]
  exact (SourceQuotient.sourceToSummand D.inducingData .line
    (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData large hhol plane)).property

/-- **The per-datum standard-realizing map**: `T₀` restricted and corestricted to `D`'s own
plane/line summands. Agreement with `T₀` is not a separate fact: it
is what this restriction literally is, and `.val` of an application is `rfl`-equal to `T₀` applied
to the underlying vector by construction. -/
noncomputable def standardFromT0Std :
    boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line where
  toFun x := ⟨T₀ x.val, T₀_mapsTo_std D large hhol T₀ hT₀ x⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

theorem standardFromT0Std_apply_val (x : boundarySummand D.inducingData .plane) :
    (standardFromT0Std D large hhol T₀ hT₀ x).val = T₀ x.val := rfl

/-- **`standardFromT0Std` realizes the standard intertwiner on `D`**:
the per-generator witness is exactly `ConvergentEisenstein.EndpointSourceStandard.sourceStandard`, related by
`sourceStandard_related`, and agreement of `standardFromT0Std` with it on each generator is
`T₀_sourceClass_eq_std` again. -/
theorem standardFromT0Std_realizesStandardConv :
    RealizesStandardConv D.inducingData (standardFromT0Std D large hhol T₀ hT₀) := by
  rw [realizesStandardConv_iff]
  intro plane
  refine ⟨ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData large hhol plane,
    ConvergentEisenstein.StandardConv.sourceStandard_relatedConv D.inducingData large hhol plane, ?_⟩
  apply Subtype.ext
  rw [standardFromT0Std_apply_val, sourceToSummand_val_std, T₀_sourceClass_eq_std D large hhol T₀ hT₀ plane]
  exact (sourceToSummand_val_std D.inducingData .line
    (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData large hhol plane)).symm

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd
