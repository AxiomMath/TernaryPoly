module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CochainOperations
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.VertexPrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def homogeneousDiagonalPrimitive {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) : cochains subgroup representation 1 :=
  ⟨fun vertices => cycle.val.val (fun _ => vertices 0),
    fun element vertices => cycle.val.property element (fun _ => vertices 0)⟩

def homogeneousNormalizedCycle {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) : cocycles subgroup representation :=
  cycle - boundaryMap subgroup representation (homogeneousDiagonalPrimitive subgroup representation cycle)

theorem homogeneousNormalizedCycle_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) (vertices : Fin 3 → G) :
    (homogeneousNormalizedCycle subgroup representation cycle).val.val vertices =
      cycle.val.val vertices - cycle.val.val (fun _ => vertices 1) := by
  change cycle.val.val vertices - (cycle.val.val (fun _ => vertices 1) -
    cycle.val.val (fun _ => vertices 0) + cycle.val.val (fun _ => vertices 0)) = _
  abel

theorem homogeneousNormalizedCycle_class {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (subgroup : Subgroup G) (representation : Representation ℂ G V)
    (cycle : cocycles subgroup representation) :
    classOf subgroup representation (homogeneousNormalizedCycle subgroup representation cycle) =
      classOf subgroup representation cycle := by
  have boundary_zero : classOf subgroup representation
      (boundaryMap subgroup representation (homogeneousDiagonalPrimitive subgroup representation cycle)) = 0 :=
    (classOf_eq_zero_iff subgroup representation _).mpr ⟨_, rfl⟩
  rw [homogeneousNormalizedCycle, map_sub, boundary_zero, sub_zero]

def sourceDiagonalCochain {degree : ℕ} (source : SourceCochain degree) : SourceCochain degree :=
  fun vertices => source (fun _ => vertices 1)

def sourceNormalizedCochain {degree : ℕ} (source : SourceCochain degree) : SourceCochain degree :=
  source - sourceDiagonalCochain source

theorem sourceDiagonalCochain_isSourceCocycle {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source) :
    IsSourceCocycle data side (sourceDiagonalCochain source) := by
  refine ⟨fun vertices monomial => cocycle.1 (fun _ => vertices 1) monomial, ?_, ?_, ?_⟩
  · intro monomial
    exact hasSmoothCuspLift_reindex data side cohomologicalPoint
      (fun vertices argument => (source vertices argument).val.coeff monomial)
      (cocycle.2.1 monomial) (fun _ : Fin 3 => (1 : Fin 3))
  · intro element vertices argument
    exact cocycle.2.2.1 element (fun _ => vertices 1) argument
  · intro vertices argument
    change source (fun _ => vertices 2) argument - source (fun _ => vertices 2) argument +
      source (fun _ => vertices 1) argument - source (fun _ => vertices 1) argument = 0
    abel

theorem sourceNormalizedCochain_isSourceCocycle {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source) :
    IsSourceCocycle data side (sourceNormalizedCochain source) :=
  isSourceCocycle_sub data side source (sourceDiagonalCochain source) cocycle
    (sourceDiagonalCochain_isSourceCocycle data side source cocycle)

theorem sourceNormalizedCochain_diagonal {degree : ℕ} (source : SourceCochain degree)
    (vertex : RealGL3) (argument : AdelicGL) :
    sourceNormalizedCochain source (fun _ => vertex) argument = 0 := sub_self _

theorem sourceCocycle_repeated_first {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (first second : RealGL3) (argument : AdelicGL) : source ![first, first, second] argument = 0 := by
  have relation := cocycle.2.2.2 ![first, first, first, second] argument
  have constant : ![first, first, first] = fun _ : Fin 3 => first := by
    funext index
    fin_cases index <;> rfl
  change source ![first, first, second] argument - source ![first, first, second] argument +
    source ![first, first, second] argument - source ![first, first, first] argument = 0 at relation
  rw [constant, diagonal, sub_self, zero_add, sub_zero] at relation
  exact relation

theorem sourceCocycle_repeated_last {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (first second : RealGL3) (argument : AdelicGL) : source ![first, second, second] argument = 0 := by
  have relation := cocycle.2.2.2 ![first, second, second, second] argument
  have constant : ![second, second, second] = fun _ : Fin 3 => second := by
    funext index
    fin_cases index <;> rfl
  change source ![second, second, second] argument - source ![first, second, second] argument +
    source ![first, second, second] argument - source ![first, second, second] argument = 0 at relation
  rw [constant, diagonal] at relation
  linear_combination (norm := abel) -relation

theorem sourceNormalizedCochain_evaluates {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cycle : MaximalCycles degree data.chi side)
    (evaluates : Evaluates data side source cycle) :
    Evaluates data side (sourceNormalizedCochain source)
      (homogeneousNormalizedCycle rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) side) cycle) := by
  intro vertices representative
  have value := congrFun (homogeneousNormalizedCycle_apply rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree data.chi) side) cycle vertices)
      (QuotientGroup.mk representative)
  change _ = cycle.val.val vertices (QuotientGroup.mk representative) -
    cycle.val.val (fun _ => vertices 1) (QuotientGroup.mk representative) at value
  rw [evaluates, evaluates] at value
  exact value

theorem sourceNormalizedCochain_support {degree : ℕ} (source : SourceCochain degree)
    (supported : BadPlaneSource source) : BadPlaneSource (sourceNormalizedCochain source) := by
  intro vertices representative good real
  change source vertices _ - source (fun _ => vertices 1) _ = 0
  rw [supported vertices representative good real, supported (fun _ => vertices 1) representative good real, sub_self]

theorem badPlaneRepresentative_exists_normalized {degree : ℕ} (data : InducingData degree)
    (coordinate : boundarySummand data .plane) (supported : BadPlaneRepresentative data coordinate) :
    ∃ (source : SourceCochain degree) (cycle : MaximalCycles degree data.chi .plane),
      IsSourceCocycle data .plane source ∧ Evaluates data .plane source cycle ∧
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle = coordinate.val ∧
      BadPlaneSource source ∧ ∀ (vertex : RealGL3) (argument : AdelicGL), source (fun _ => vertex) argument = 0 := by
  obtain ⟨source, cycle, source_cycle, evaluates, represents, support⟩ := supported
  refine ⟨sourceNormalizedCochain source,
    homogeneousNormalizedCycle rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle,
    sourceNormalizedCochain_isSourceCocycle data .plane source source_cycle,
    sourceNormalizedCochain_evaluates data .plane source cycle evaluates, ?_,
    sourceNormalizedCochain_support source support, sourceNormalizedCochain_diagonal source⟩
  exact (homogeneousNormalizedCycle_class rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle).trans represents

end TernaryPeriodPolynomials.SphericalDetection.Helpers
