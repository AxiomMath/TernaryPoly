/-
  Clause (a) of `IsSourceCocycle` for the finite-coset Hecke translate, from the
  finite-level-invariance / decomposition input, and the resulting conditional
  capstone:

    (density/decomposition input)  ->  Hecke-stability of `associatePair`
    (invariant complement) + (multiplicity one)  ->  the exact target.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.InducedUpToLevel
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInduced
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLift
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Equivariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.RationalLevel
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeInvariance
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HeckeStability
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.TargetReduction
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.UniversalProjection
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.TrivialCorrespondence

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix MvPolynomial


noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.TargetFromDecomposition

variable {n : ℕ} {D : InducingData n} {side : Side}

/-- **Clause (a) of `IsSourceCocycle` for the Hecke translate, from the
finite-level-invariance input.** -/
theorem translateSource_isInduced_coeff_of_decomposition
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hdec : ∀ k : finiteLevel, ∃ d : rationalLevel, ∃ u : finiteLevel,
      k.val = rationalFinite d.val * u.val ∧
      ∀ r ∈ t.representatives, (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel)
    (x : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    IsInduced D side cohomologicalPoint
      (fun g => (HeckeInvariance.translateSource D t c x g).val.coeff m) := by
  apply InducedUpToLevel.isInduced_of_upToLevel
  · have hfun : (fun g => (HeckeInvariance.translateSource D t c x g).val.coeff m)
        = fun g => ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val).coeff m := by
      funext g
      rw [HeckeInvariance.translateSource]
      rw [show (∑ r ∈ t.representatives, realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val
          = ∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val
          from map_sum (Submodule.subtype (homogeneousSubmodule (Fin 3) ℂ n)) _ _]
      rw [show (∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val).coeff m
          = ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val).coeff m
          from map_sum (SourceSmoothness.coeffLM m) _ _]
    rw [hfun]
    apply InducedUpToLevel.isInducedUpToLevel_finset_sum
    intro r _
    exact InducedUpToLevel.isInducedUpToLevel_right_shift r
      (InducedUpToLevel.isInducedUpToLevel_of_isInduced
        (TranslateIsInduced.repCoeff_isInduced hc r x m))
  · intro k g
    exact congrArg (fun p : HomogeneousPoly n => p.val.coeff m)
      (TranslateRationalLevel.translateSource_finiteLevel_invariant_of_decomposition t hc x g
        hdec k)

/-- Source-cocycle closure of the Hecke translate from the finite-level input. -/
theorem translateSource_isSourceCocycle_of_decomposition
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hdec : ∀ k : finiteLevel, ∃ d : rationalLevel, ∃ u : finiteLevel,
      k.val = rationalFinite d.val * u.val ∧
      ∀ r ∈ t.representatives, (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel) :
    IsSourceCocycle D side (HeckeInvariance.translateSource D t c) :=
  ⟨fun x m => translateSource_isInduced_coeff_of_decomposition t hc hdec x m,
   fun m => TranslateHasSmoothCuspLift.translateSource_hasSmoothCuspLift hc t m,
   fun h x g => HeckeInvariance.translateSource_equivariant D t c hc.2.2.1 h x g,
   fun x g => HeckeInvariance.translateSource_closed D t c hc.2.2.2 x g⟩

/-- **Conditional capstone.**  The exact conclusion follows from the
finite-level-invariance/decomposition input, a `pairHecke`-invariant complement
of the associate pair, and the multiplicity-one vanishing `Q = 0`. -/
theorem cuspidal_associate_projector_of_inputs
    (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hdec : ∀ t : HeckeCorrespondence, ∀ k : finiteLevel,
      ∃ d : rationalLevel, ∃ u : finiteLevel,
        k.val = rationalFinite d.val * u.val ∧
        ∀ r ∈ t.representatives, (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel)
    (hcompl : ∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧ ∀ t, ∀ x ∈ S', pairHecke D hecke t x ∈ S')
    (hQ : ∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range q ≤ associatePair D →
      (∀ x ∈ associatePair D, q x = 0) →
      (∀ t, q.comp (pairHecke D hecke t) = (pairHecke D hecke t).comp q) → q = 0) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D hecke p ∧
      ∀ p', IsIsotypicalProjection D hecke p' → p' = p :=
  TargetReduction.existsUnique_of_split hecke hhecke
    (fun t x hx => HeckeStability.associatePair_hecke_stable t hecke hhecke
      (fun _side _c hc => translateSource_isSourceCocycle_of_decomposition t hc (hdec t)) x hx)
    hcompl hQ

/-- Paper-form corollary of the conditional capstone. -/
theorem conclusion_of_inputs (n : ℕ) (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
    (hdec : ∀ t : HeckeCorrespondence, ∀ k : finiteLevel,
      ∃ d : rationalLevel, ∃ u : finiteLevel,
        k.val = rationalFinite d.val * u.val ∧
        ∀ r ∈ t.representatives, (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel)
    (hcompl : ∃ S' : Submodule ℂ (BoundaryCoordinates n trivialCharacter),
      IsCompl (associatePair D.inducingData) S' ∧
      ∀ t, ∀ x ∈ S', pairHecke D.inducingData hecke t x ∈ S')
    (hQ : ∀ q : Module.End ℂ (BoundaryCoordinates n trivialCharacter),
      LinearMap.range q ≤ associatePair D.inducingData →
      (∀ x ∈ associatePair D.inducingData, q x = 0) →
      (∀ t, q.comp (pairHecke D.inducingData hecke t) =
        (pairHecke D.inducingData hecke t).comp q) → q = 0) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n trivialCharacter),
      IsIsotypicalProjection D.inducingData hecke p ∧
      ∀ p', IsIsotypicalProjection D.inducingData hecke p' → p' = p :=
  cuspidal_associate_projector_of_inputs D.inducingData hecke hhecke hdec hcompl hQ

/-- The capstone's finite-level/decomposition input is non-vacuously satisfiable:
it holds for the identity double coset `Γ 1 Γ`. -/
theorem hdec_trivialCorrespondence :
    ∀ k : finiteLevel, ∃ d : rationalLevel, ∃ u : finiteLevel,
      k.val = rationalFinite d.val * u.val ∧
      ∀ r ∈ TrivialCorrespondence.trivialCorrespondence.representatives,
        (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel := by
  intro k
  refine ⟨1, k, ?_, ?_⟩
  · simp
  · intro r hr
    have hr' : r ∈ ({1} : Finset RationalGL3) := hr
    rw [Finset.mem_singleton] at hr'
    subst hr'
    simpa only [map_one, inv_one, one_mul, mul_one] using k.property

/-- The decomposition input holds for every correspondence all of whose
representatives already lie in the compact level: take `d = 1`, `u = k`; then
`(rationalFinite r)⁻¹ * k * rationalFinite r` is a product of three elements of
`finiteLevel`. -/
theorem hdec_of_integral (t : HeckeCorrespondence)
    (hint : ∀ r ∈ t.representatives, rationalFinite r ∈ finiteLevel) :
    ∀ k : finiteLevel, ∃ d : rationalLevel, ∃ u : finiteLevel,
      k.val = rationalFinite d.val * u.val ∧
      ∀ r ∈ t.representatives, (rationalFinite r)⁻¹ * u.val * rationalFinite r ∈ finiteLevel := by
  intro k
  refine ⟨1, k, ?_, ?_⟩
  · simp
  · intro r hr
    exact finiteLevel.mul_mem
      (finiteLevel.mul_mem (finiteLevel.inv_mem (hint r hr)) k.property) (hint r hr)

end TernaryPeriodPolynomials.HeckeTranslate.TargetFromDecomposition

end
