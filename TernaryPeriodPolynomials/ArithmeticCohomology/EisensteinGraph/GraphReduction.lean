module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Reduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.SourceStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.EisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardExistence
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.BoundaryDimension

@[expose] public section


/-!
# Reduction of the standard graph to a constant-term formula and half-dimension

Fix a projection `p` of the maximal boundary coordinates onto the associate pair. Suppose every
plane source cocycle has a standard continuation (`StandardRelation.Related`), and that there are
global classes `E c` whose projected restriction is `([c], [J c])` for every standard partner `J c`
of `c` (the cohomological constant-term formula). Suppose finally that no global class projects to
`(0, b)` with `b ≠ 0` (Harder's half-dimension statement). Then the standard integral descends to
an operator `T` on the cuspidal summand, `T` realizes the standard operator, and the projected
global image is exactly the graph of `T`.

For `4 ≤ n` and holomorphic data, the standard continuation and the global Eisenstein classes are
the constructions `EndpointSourceStandard.sourceStandard` and `EndpointEisensteinCocycle.globalClass`
of the Sol reference implementation; the required
classes then follow from the constant-term formula `ConstantTermFormula`. Conversely
(`inputs_of_standard_graph`) the three inputs follow from the standard graph in every degree, so
the reduction loses nothing. Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.GraphReduction

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- No global class has projected boundary coordinates `(0, b)` with `b ≠ 0`. -/
def HalfDimension {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi)) : Prop :=
  ∀ globalClass : WholeGlobalH2 n D.chi,
    (GraphPieces.Reduction.projectedRestriction D projection globalClass).1 = 0 →
      (GraphPieces.Reduction.projectedRestriction D projection globalClass).2 = 0

/-- The projected restriction of the global Eisenstein class of a plane source cocycle `c` is the
pair of classes `([c], [J c])`, where `J c` is the standard continuation of `c`. -/
def ConstantTermFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi)) : Prop :=
  ∀ plane : SourceSpace.sourceCocycles D .plane,
    GraphPieces.Reduction.projectedRestriction D projection
        (EndpointEisensteinCocycle.globalClass D holomorphic large plane) =
      (SourceSpace.sourceClass D .plane plane,
        SourceSpace.sourceClass D .line
          (EndpointSourceStandard.sourceStandard D large holomorphic plane))

/-- Global classes whose projected restriction is `([c], [J c])` for every plane source cocycle `c`
and every standard partner `J c` of `c`. -/
def HasEisensteinClasses {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi)) : Prop :=
  ∃ eisenstein : SourceSpace.sourceCocycles D .plane → WholeGlobalH2 n D.chi,
    ∀ plane line, StandardRelation.Related D plane line →
      GraphPieces.Reduction.projectedRestriction D projection (eisenstein plane) =
        (SourceSpace.sourceClass D .plane plane, SourceSpace.sourceClass D .line line)

/-- The unprojected form of the constant-term formula: the maximal-stratum coordinates of the
global Eisenstein cocycle of `c` are the classes of `c` and of its standard continuation. -/
def RestrictionFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic D) : Prop :=
  ∀ plane : SourceSpace.sourceCocycles D .plane,
    globalCoordinates n D.chi (EndpointEisensteinCocycle.globalCocycle D holomorphic large plane) =
      (SourceSpace.sourceClass D .plane plane,
        SourceSpace.sourceClass D .line
          (EndpointSourceStandard.sourceStandard D large holomorphic plane))

/-- The unprojected formula implies the projected one for any projection that is the identity on
the associate pair. -/
theorem constantTermFormula_of_restrictionFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (identity : ∀ x ∈ associatePair D, projection x = x)
    (formula : RestrictionFormula large D holomorphic) :
    ConstantTermFormula large D holomorphic projection := by
  intro plane
  have coordinates := GraphPieces.Helpers.canonicalCoordinates_restriction n D.chi
    (EndpointEisensteinCocycle.globalCocycle D holomorphic large plane)
  change projection ((GraphPieces.Helpers.canonicalCoordinates n D.chi).comp
      (GraphPieces.Helpers.canonicalRestriction n D.chi)
        (EndpointEisensteinCocycle.globalClass D holomorphic large plane)) = _
  have formula' := formula plane
  refine (congrArg projection (coordinates.trans formula')).trans (identity _ ⟨?_, ?_⟩)
  · rw [← SourceSpace.sourceClass_range D .plane]
    exact ⟨plane, rfl⟩
  · rw [← SourceSpace.sourceClass_range D .line]
    exact ⟨_, rfl⟩

/-- In degrees `4 ≤ n`, the constant-term formula for Sol's global Eisenstein classes gives the
required global classes. -/
theorem hasEisensteinClasses_of_constantTermFormula {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (constantTerm : ConstantTermFormula large D holomorphic projection) :
    HasEisensteinClasses D projection := by
  refine ⟨EndpointEisensteinCocycle.globalClass D holomorphic large, ?_⟩
  intro plane line related
  rw [constantTerm plane,
    StandardExistence.standard_source_relation_eq_sourceStandard large D holomorphic plane line
      related]

section Generic

variable {G P Q : Type*} [AddCommGroup G] [Module ℂ G] [AddCommGroup P] [Module ℂ P]
  [AddCommGroup Q] [Module ℂ Q]

/-- Abstract half-dimension: if the first-coordinate projection of the image of `Pr` covers a
subspace `SP` of dimension at least that of the image, then `Pr g = (0, b)` forces `b = 0`. -/
private theorem second_eq_zero_of_first_eq_zero [FiniteDimensional ℂ (P × Q)]
    (Pr : G →ₗ[ℂ] P × Q) (SP : Submodule ℂ P)
    (hcover : ∀ p ∈ SP, ∃ g, (Pr g).1 = p)
    (dimension : Module.finrank ℂ (LinearMap.range Pr) ≤ Module.finrank ℂ SP) :
    ∀ g, (Pr g).1 = 0 → (Pr g).2 = 0 := by
  let first : LinearMap.range Pr →ₗ[ℂ] P := (LinearMap.fst ℂ P Q).comp (LinearMap.range Pr).subtype
  have firstRange : SP ≤ LinearMap.range first := by
    intro p hp
    obtain ⟨g, hg⟩ := hcover p hp
    exact ⟨⟨Pr g, g, rfl⟩, hg⟩
  have rankNullity := LinearMap.finrank_range_add_finrank_ker first
  have rangeBound := Submodule.finrank_mono firstRange
  have kernelZero : Module.finrank ℂ (LinearMap.ker first) = 0 := by
    omega
  have kernelBot : LinearMap.ker first = ⊥ := by
    have : Module.IsTorsionFree ℂ (LinearMap.range Pr) := inferInstance
    exact Submodule.finrank_eq_zero.mp kernelZero
  intro g firstZero
  have inKernel : (⟨Pr g, g, rfl⟩ : LinearMap.range Pr) ∈ LinearMap.ker first := firstZero
  rw [kernelBot, Submodule.mem_bot] at inKernel
  have vanishes := congrArg Subtype.val inKernel
  have h : Pr g = 0 := vanishes
  rw [h]
  rfl

end Generic

/-- Half-dimension in its dimension form: given global classes with the constant-term property,
the projected global image has dimension at most that of the plane summand exactly when no global
class projects to `(0, b)` with `b ≠ 0`. This direction turns the dimension bound into
`HalfDimension`. -/
theorem halfDimension_of_finrank_le {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (existsIntegral : ∀ plane : SourceSpace.sourceCocycles D .plane,
      ∃ line, StandardRelation.Related D plane line)
    (eisenstein : HasEisensteinClasses D projection)
    (dimension : Module.finrank ℂ
        (LinearMap.range (GraphPieces.Reduction.projectedRestriction D projection)) ≤
      Module.finrank ℂ (boundarySummand D .plane)) :
    HalfDimension D projection := by
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n D.chi
  obtain ⟨classes, constantTerm⟩ := eisenstein
  refine second_eq_zero_of_first_eq_zero (GraphPieces.Reduction.projectedRestriction D projection)
    (boundarySummand D .plane) ?_ dimension
  intro planeClass membership
  have surjective := SourceQuotient.sourceToSummand_surjective D .plane ⟨planeClass, membership⟩
  obtain ⟨plane, planeEq⟩ := surjective
  have integral := existsIntegral plane
  obtain ⟨line, related⟩ := integral
  refine ⟨classes plane, ?_⟩
  rw [constantTerm plane line related]
  exact congrArg Subtype.val planeEq

/-- The abstract reduction: standard continuations, global classes with the constant-term formula,
and half-dimension give the standard graph. -/
theorem standard_graph_of_eisenstein {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (range : LinearMap.range projection = associatePair D)
    (existsIntegral : ∀ plane : SourceSpace.sourceCocycles D .plane,
      ∃ line, StandardRelation.Related D plane line)
    (eisenstein : SourceSpace.sourceCocycles D .plane → WholeGlobalH2 n D.chi)
    (constantTerm : ∀ plane line, StandardRelation.Related D plane line →
      GraphPieces.Reduction.projectedRestriction D projection (eisenstein plane) =
        (SourceSpace.sourceClass D .plane plane, SourceSpace.sourceClass D .line line))
    (halfDimension : HalfDimension D projection) :
    ∃ standard : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line,
      RealizesStandard D standard ∧
      (LinearMap.range (GraphPieces.Reduction.projectedRestriction D projection) :
        Set (BoundaryCoordinates n D.chi)) = GraphPieces.Reduction.spectralGraph D standard := by
  have respects : LinearMap.ker (StandardRelation.planeClass D) ≤
      LinearMap.ker (StandardRelation.lineClass D) := by
    rintro ⟨⟨plane, line⟩, related⟩ vanishes
    have vanishes' : SourceSpace.sourceClass D .plane plane = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp vanishes)
    have image := constantTerm plane line related
    have lineZero := halfDimension (eisenstein plane) (by rw [image, vanishes'])
    rw [image] at lineZero
    exact LinearMap.mem_ker.mpr (Subtype.ext lineZero)
  refine ⟨StandardRelation.descendedStandard D existsIntegral respects,
    StandardRelation.descendedStandard_realizes D existsIntegral respects, ?_⟩
  apply (GraphPieces.Reduction.graph_equality_iff D projection _).mpr
  constructor
  · intro globalClass
    have inPair : GraphPieces.Reduction.projectedRestriction D projection globalClass ∈ associatePair D := by
      rw [← range]
      exact ⟨_, rfl⟩
    let planePart : boundarySummand D .plane :=
      ⟨(GraphPieces.Reduction.projectedRestriction D projection globalClass).1, inPair.1⟩
    have surjective := SourceQuotient.sourceToSummand_surjective D .plane
    have planeExists : ∃ plane, SourceQuotient.sourceToSummand D .plane plane = planePart :=
      surjective planePart
    obtain ⟨plane, planeEq⟩ := planeExists
    have lineExists := existsIntegral plane
    obtain ⟨line, related⟩ := lineExists
    refine ⟨planePart, ?_⟩
    have image := constantTerm plane line related
    have planeVal : SourceSpace.sourceClass D .plane plane =
        (GraphPieces.Reduction.projectedRestriction D projection globalClass).1 :=
      congrArg Subtype.val planeEq
    have fstZero : (GraphPieces.Reduction.projectedRestriction D projection
        (globalClass - eisenstein plane)).1 = 0 :=
      (congrArg Prod.fst (map_sub (GraphPieces.Reduction.projectedRestriction D projection)
        globalClass (eisenstein plane))).trans
        (sub_eq_zero.mpr (planeVal.symm.trans (congrArg Prod.fst image).symm))
    have difference := halfDimension (globalClass - eisenstein plane) fstZero
    have sndEq : (GraphPieces.Reduction.projectedRestriction D projection globalClass).2 =
        SourceSpace.sourceClass D .line line :=
      (sub_eq_zero.mp ((congrArg Prod.snd (map_sub
        (GraphPieces.Reduction.projectedRestriction D projection) globalClass
        (eisenstein plane))).symm.trans difference)).trans (congrArg Prod.snd image)
    have standardValue : StandardRelation.descendedStandard D existsIntegral respects
        planePart = SourceQuotient.sourceToSummand D .line line :=
      (congrArg (StandardRelation.descendedStandard D existsIntegral respects) planeEq).symm.trans
        (StandardRelation.descendedStandard_related D existsIntegral respects
          ⟨(plane, line), related⟩)
    exact Prod.ext rfl (sndEq.trans (congrArg Subtype.val standardValue).symm)
  · intro planeClass
    have planeExists := SourceQuotient.sourceToSummand_surjective D .plane planeClass
    obtain ⟨plane, rfl⟩ := planeExists
    have lineExists := existsIntegral plane
    obtain ⟨line, related⟩ := lineExists
    refine ⟨eisenstein plane, ?_⟩
    have standardValue := StandardRelation.descendedStandard_related D existsIntegral respects
      ⟨(plane, line), related⟩
    simp only [StandardRelation.planeClass, StandardRelation.lineClass, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.fst_apply,
      LinearMap.snd_apply] at standardValue
    refine (constantTerm plane line related).trans (Prod.ext rfl ?_)
    exact (congrArg Subtype.val standardValue).symm

/-- In degrees `4 ≤ n` the standard graph follows from global classes with the constant-term
property and half-dimension: the standard continuation is Sol's `sourceStandard`. -/
theorem standard_graph_of_large_degree {n : ℕ} (large : 4 ≤ n) (D : InducingData n)
    (holomorphic : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (range : LinearMap.range projection = associatePair D)
    (eisenstein : HasEisensteinClasses D projection)
    (halfDimension : HalfDimension D projection) :
    ∃ standard : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line,
      RealizesStandard D standard ∧
      (LinearMap.range (GraphPieces.Reduction.projectedRestriction D projection) :
        Set (BoundaryCoordinates n D.chi)) = GraphPieces.Reduction.spectralGraph D standard :=
  standard_graph_of_eisenstein D projection range
    (EndpointSourceStandard.related_total D large holomorphic)
    eisenstein.choose eisenstein.choose_spec halfDimension

/-- Conversely, a standard operator whose graph is the projected global image yields all three
inputs, in every degree. So the reduction loses nothing: the inputs are exactly as strong as the
standard-graph obligation. -/
theorem inputs_of_standard_graph {n : ℕ} (D : InducingData n)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (standard : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line)
    (realizes : RealizesStandard D standard)
    (graph : (LinearMap.range (GraphPieces.Reduction.projectedRestriction D projection) :
      Set (BoundaryCoordinates n D.chi)) = GraphPieces.Reduction.spectralGraph D standard) :
    (∀ plane : SourceSpace.sourceCocycles D .plane,
      ∃ line, StandardRelation.Related D plane line) ∧
    HasEisensteinClasses D projection ∧ HalfDimension D projection := by
  have pointwise := (StandardRelation.realizesStandard_iff D standard).mp realizes
  obtain ⟨imageInGraph, graphInImage⟩ :=
    (GraphPieces.Reduction.graph_equality_iff D projection standard).mp graph
  refine ⟨fun plane => (pointwise plane).imp fun _ h => h.1, ?_, ?_⟩
  · refine ⟨fun plane => (graphInImage (SourceQuotient.sourceToSummand D .plane plane)).choose, ?_⟩
    intro plane line related
    rw [(graphInImage (SourceQuotient.sourceToSummand D .plane plane)).choose_spec]
    have pointwisePlane := pointwise plane
    obtain ⟨line', related', value⟩ := pointwisePlane
    have same := StandardExistence.standard_source_relation_single_valued D plane line' line
      related' related
    subst same
    exact Prod.ext rfl (congrArg Subtype.val value)
  · intro globalClass firstZero
    have graphPoint := imageInGraph globalClass
    obtain ⟨planeClass, equality⟩ := graphPoint
    have planeZero : planeClass = 0 := by
      apply Subtype.ext
      have first := congrArg Prod.fst equality
      rw [firstZero] at first
      exact first.symm
    have lineZero : (GraphPieces.Reduction.projectedRestriction D projection globalClass).2 =
        ((standard planeClass : boundarySummand D .line) : StratumH2 n D.chi .line) :=
      congrArg Prod.snd equality
    exact lineZero.trans (congrArg (fun p => ((standard p : boundarySummand D .line) :
      StratumH2 n D.chi .line)) planeZero |>.trans (congrArg Subtype.val (map_zero standard)))

end TernaryPeriodPolynomials.EisensteinGraph.GraphReduction
