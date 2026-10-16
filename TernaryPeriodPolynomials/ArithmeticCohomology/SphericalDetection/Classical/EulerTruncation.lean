module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.EulerRealTranslate

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance classicalEulerTruncationDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem goodLineFinitePadicTruncatedIntegral_classical_insert (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) (real : BinaryRealGL)
    (places : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ places) :
    goodLineFinitePadicTruncatedIntegral cusp (cuspSmoothAction cusp (atInfinity real) vector.val) exponent
        (insert place places) =
      goodLineFinitePadicTruncatedIntegral cusp (cuspSmoothAction cusp (atInfinity real)
        (cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent
          (by linarith) vector).val) exponent places := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have integrable := goodLineFinitePadicIntegrand_global_integrable cusp
    (cuspSmoothAction cusp (atInfinity real) vector.val)
    (cuspSmoothAction_real_spherical cusp vector.val vector.property.1 real) exponent convergent
  have lifted := (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [goodLineFinitePadicTruncatedIntegral_away cusp _ exponent places place distinct outside
    (goodLineFinitePadicIntegrand_global_integrable cusp _
      (cuspSmoothAction_real_spherical cusp _
        (cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent
          (by linarith) vector).property.1 real) exponent convergent)]
  rw [goodLineFinitePadicTruncatedIntegral,
    ← (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).setIntegral_preimage_emb
      (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding,
    goodLineFiniteSupportRegion_padic_preimage_insert places place distinct]
  rw [setIntegral_prod_symm_of_integrable _ _ _ _ _ lifted.integrableOn]
  simp_rw [setIntegral_univ, goodLineFinitePadicIntegrand_split,
    cuspLocalPadicIntegral_classicalEuler_real cusp central_positive halfWeight negative place exponent
      (by linarith) vector real]
  rfl

theorem goodLineFinitePadicTruncatedIntegral_classical_equiv (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (places : Finset FinitePlace) :
    ∃ equiv : cuspClassicalVectors cusp halfWeight ≃ₗ[ℂ] cuspClassicalVectors cusp halfWeight,
      (∀ (vector : cuspClassicalVectors cusp halfWeight) (real : BinaryRealGL),
        goodLineFinitePadicTruncatedIntegral cusp (cuspSmoothAction cusp (atInfinity real) vector.val) exponent places =
          cusp.realize (equiv vector).val (atInfinity real)) ∧
      (∀ (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight),
        equiv (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) =
          cuspClassicalPrimeHecke cusp central_positive halfWeight prime (equiv vector)) := by
  induction places using Finset.induction_on with
  | empty =>
    refine ⟨LinearEquiv.refl ℂ _, ?_, fun _ _ => rfl⟩
    intro vector real
    rw [goodLineFinitePadicTruncatedIntegral_empty, cuspSmoothAction_realize, one_mul]
    rfl
  | @insert place places outside induction =>
    obtain ⟨equiv, values, commute⟩ := induction
    by_cases same : place = placeThree
    · subst place
      refine ⟨equiv, ?_, commute⟩
      intro vector real
      rw [goodLineFinitePadicTruncatedIntegral_insert_three, values]
    · let localEquiv := cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent
        (by linarith)
      refine ⟨localEquiv.trans equiv, ?_, ?_⟩
      · intro vector real
        rw [goodLineFinitePadicTruncatedIntegral_classical_insert cusp central_positive halfWeight negative
          exponent convergent vector real places place same outside, values]
        rfl
      · intro prime vector
        simp only [LinearEquiv.trans_apply, localEquiv,
          cuspClassicalLocalEulerEquiv_hecke_commute, commute]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
