module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EdgeOrbitAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.BoundaryExactness

@[expose] public section


/- Ported from AxiomDeep (Claude Opus 5.5). -/
/-!
# Endpoint-kernel vanishing reduced to single complete flags

The endpoint pullback of an evaluated source class to complete flags is a
coboundary as soon as, for every rational representative `q` of a complete flag,
the scalar cocycle `x ↦ c(x)(q⁻¹)` is the coboundary of a cochain equivariant for
the stabilizer of that flag in the arithmetic group.  This is the orbit-assembly
(Shapiro) half of endpoint-kernel vanishing, with no hypothesis on the data.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.GraphPieces.EndpointReduction

/-- Stabilizer exactness of a source cocycle at one complete flag `q·B`. -/
def FlagExact {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree) (flag : RationalGL3) : Prop :=
  ∃ primitive : (Fin 2 → RationalGL3) → HomogeneousPoly degree,
    (∀ γ : rationalLevel, γ.val • (QuotientGroup.mk flag : Edges) = QuotientGroup.mk flag →
      ∀ x, primitive (fun i => γ.val * x i) =
        rationalCoefficientComponent degree data.chi γ.val (primitive x)) ∧
    ∀ x : Fin 3 → RationalGL3,
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup flag⁻¹) =
        primitive ![x 1, x 2] - primitive ![x 0, x 2] + primitive ![x 0, x 1]

theorem endpointPull_value {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (cocycle : MaximalCycles degree data.chi side) (evaluates : Evaluates data side source cocycle)
    (x : Fin 3 → RationalGL3) (flag : RationalGL3) :
    (BoundaryExactness.endpointPullCocycle degree data.chi side cocycle).val.val x
        (QuotientGroup.mk flag : Edges) =
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (x i)) (rationalGroup flag⁻¹) :=
  evaluates x flag

/-- One evaluated class lies in the endpoint kernel when the source is exact at every flag. -/
theorem endpointPull_eq_zero {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (cocycle : MaximalCycles degree data.chi side) (evaluates : Evaluates data side source cocycle)
    (exact : ∀ flag, FlagExact data source flag) :
    BoundaryExactness.endpointPullH2 degree data.chi side
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) side)
        cocycle) = 0 := by
  rw [BoundaryExactness.endpointPullH2_realizes]
  set pulled := BoundaryExactness.endpointPullCocycle degree data.chi side cocycle
  have localExact : ∀ edge : Edges, EdgeOrbitAssembly.LocallyExact rationalLevel
      (rationalCoefficientComponent degree data.chi) pulled.val.val edge := by
    intro edge
    obtain ⟨flag, rfl⟩ := QuotientGroup.mk_surjective edge
    obtain ⟨primitive, equivariant, boundary⟩ := exact flag
    refine ⟨primitive, equivariant, ?_⟩
    intro x
    rw [endpointPull_value data side source cocycle evaluates x flag]
    exact boundary x
  obtain ⟨primitive, equality⟩ := EdgeOrbitAssembly.exists_primitive rationalLevel
    (rationalCoefficientComponent degree data.chi) pulled.val localExact
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  exact equality

/-- **Reduction of endpoint-kernel vanishing.** If every source cocycle is exact at
every complete flag, the whole summand lies in the endpoint kernel. -/
theorem boundarySummand_le_ker {degree : ℕ} (data : InducingData degree) (side : Side)
    (exact : ∀ source, IsSourceCocycle data side source → ∀ flag, FlagExact data source flag) :
    boundarySummand data side ≤
      LinearMap.ker (BoundaryExactness.endpointPullH2 degree data.chi side) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨source, isSource, cocycle, evaluates, rfl⟩
  exact endpointPull_eq_zero data side source cocycle evaluates (exact source isSource)

end TernaryPeriodPolynomials.GraphPieces.EndpointReduction
