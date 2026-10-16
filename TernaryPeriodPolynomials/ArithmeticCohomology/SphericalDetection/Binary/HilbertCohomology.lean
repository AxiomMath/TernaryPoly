module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ContinuousCohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryHilbertCocycle_no_finiteLevel_primitive (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (nonzero : groupCohomology.H1π (binaryCuspidalRep cusp degree) cycle ≠ 0)
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL =>
      binaryHilbertEmbedding cusp basis (cycle (point 0))))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL)) :
    ¬ ∃ vector : index → cusp.H,
      (∀ matrix, binaryHilbertEmbedding cusp basis (cycle matrix) =
        binaryHilbertOperator cusp basis matrix vector - vector) ∧
      ∀ element : level, ∀ position, cusp.π (atFinite element.val) (vector position) = vector position := by
  rintro ⟨vector, boundary, fixed⟩
  obtain ⟨values, equality⟩ := binaryHilbertPrimitive_mem_range cusp basis _ regular
    vector boundary level level_open level_compact fixed
  subst vector
  apply nonzero
  rw [groupCohomology.H1π_eq_zero_iff]
  let primitive : binaryCuspidalRep cusp degree := values
  refine ⟨primitive, ?_⟩
  funext matrix
  let embedding : (binaryCuspidalRep cusp degree) →ₗ[ℂ] (index → cusp.H) :=
    binaryHilbertEmbedding cusp basis
  apply (show Function.Injective embedding from binaryHilbertEmbedding_injective cusp basis)
  change embedding ((binaryCuspidalRep cusp degree).ρ matrix primitive - primitive) = embedding (cycle matrix)
  rw [map_sub]
  exact (congrArg (fun value => value - embedding values)
    (binaryHilbertOperator_intertwines cusp basis matrix values).symm).trans (boundary matrix).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
