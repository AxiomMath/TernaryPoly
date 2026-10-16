module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.IntegralRationals
public import Mathlib.Data.Nat.ChineseRemainder

@[expose] public section


/-!
# Approximation of integral finite adeles by integers

* `isUnit_intCast_of_not_dvd`: an integer prime to the residue characteristic of a
  place is a unit of the local integers.
* `exists_int_add_mul`: `Ẑ = ℤ + M Ẑ` for every `M ≠ 0` (local approximation plus CRT).
* `int_dvd_of_eq_mul`: `ℤ ∩ M Ẑ = M ℤ`.
* `exists_three_mul_of_reduction_zero`: the kernel of reduction modulo three.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic IsDedekindDomain

noncomputable section

namespace TernaryPeriodPolynomials.HeckeStability.AdelicApproximation

/-- The rational prime of a finite place. -/
abbrev placePrime (v : FinitePlace) : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)

instance placePrime_fact (v : FinitePlace) : Fact (placePrime v).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The local ring isomorphism with the `p`-adic integers. -/
def localEquiv (v : FinitePlace) : v.adicCompletionIntegers ℚ ≃+* ℤ_[placePrime v] :=
  @AlgEquiv.toRingEquiv _ _ _ _ _ _ (Ring.toIntAlgebra _) _
    (@ContinuousAlgEquiv.toAlgEquiv _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _) _
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v))

theorem placePrime_symm (q : Nat.Primes) :
    placePrime (Rat.HeightOneSpectrum.primesEquiv.symm q) = q :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ q)

theorem isUnit_intCast_of_not_dvd (v : FinitePlace) (z : ℤ)
    (h : ¬ (placePrime v : ℤ) ∣ z) : IsUnit (z : v.adicCompletionIntegers ℚ) := by
  have hp : Irreducible (placePrime v : ℤ) :=
    (Nat.prime_iff_prime_int.mp (placePrime_fact v).out).irreducible
  have hunit : IsUnit (localEquiv v (z : v.adicCompletionIntegers ℚ)) := by
    rw [map_intCast, PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]
    exact ((Irreducible.coprime_iff_not_dvd hp).mpr h).symm
  exact (MulEquiv.isUnit_map (localEquiv v).toMulEquiv).mp hunit

theorem isUnit_natCast_of_not_dvd (v : FinitePlace) (z : ℕ)
    (h : ¬ placePrime v ∣ z) : IsUnit (z : v.adicCompletionIntegers ℚ) := by
  have := isUnit_intCast_of_not_dvd v (z : ℤ) (by exact_mod_cast h)
  simpa using this

theorem exists_nat_sub_eq_mul (v : FinitePlace) (x : v.adicCompletionIntegers ℚ) (e : ℕ) :
    ∃ a : ℕ, ∃ y : v.adicCompletionIntegers ℚ,
      x - (a : v.adicCompletionIntegers ℚ) = (placePrime v : v.adicCompletionIntegers ℚ) ^ e * y := by
  have h := PadicInt.appr_spec e (localEquiv v x)
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  refine ⟨(localEquiv v x).appr e, (localEquiv v).symm y, ?_⟩
  apply (localEquiv v).injective
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]
  exact hy

/-- Local divisibility by `M` from divisibility by the exact prime-power part of `M`. -/
theorem exists_mul_of_ordProj (v : FinitePlace) (M : ℕ) (hM : M ≠ 0)
    (w : v.adicCompletionIntegers ℚ)
    (hw : ∃ y : v.adicCompletionIntegers ℚ,
      w = (placePrime v : v.adicCompletionIntegers ℚ) ^ M.factorization (placePrime v) * y) :
    ∃ y : v.adicCompletionIntegers ℚ, w = (M : v.adicCompletionIntegers ℚ) * y := by
  obtain ⟨y, hy⟩ := hw
  set p := placePrime v
  have hsplit : M = p ^ M.factorization p * (M / p ^ M.factorization p) :=
    (Nat.ordProj_mul_ordCompl_eq_self M p).symm
  have hnot : ¬ p ∣ M / p ^ M.factorization p :=
    Nat.not_dvd_ordCompl (placePrime_fact v).out hM
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd v _ hnot
  refine ⟨(↑u⁻¹ : v.adicCompletionIntegers ℚ) * y, ?_⟩
  conv_rhs => rw [hsplit]
  rw [Nat.cast_mul, Nat.cast_pow, ← hu, hy, mul_assoc, Units.mul_inv_cancel_left]

/-- `Ẑ = ℤ + M Ẑ`. -/
theorem exists_int_add_mul (M : ℕ) (hM : M ≠ 0) (x : IntegralAdeles) :
    ∃ z : ℤ, ∃ y : IntegralAdeles, x = (z : IntegralAdeles) + (M : IntegralAdeles) * y := by
  classical
  let T : Finset FinitePlace := M.primeFactors.attach.image
    (fun p => Rat.HeightOneSpectrum.primesEquiv.symm
      (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
  have hT : ∀ v, v ∈ T ↔ placePrime v ∣ M := by
    intro v
    constructor
    · intro hv
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hv
      have h := placePrime_symm (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)
      change placePrime (Rat.HeightOneSpectrum.primesEquiv.symm
        (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)) ∣ M
      rw [h]
      exact Nat.dvd_of_mem_primeFactors p.2
    · intro hv
      apply Finset.mem_image.mpr
      refine ⟨⟨placePrime v, Nat.mem_primeFactors.mpr ⟨(placePrime_fact v).out, hv, hM⟩⟩,
        Finset.mem_attach _ _, ?_⟩
      apply (Rat.HeightOneSpectrum.primesEquiv).injective
      exact Subtype.ext (placePrime_symm _)
  let e : FinitePlace → ℕ := fun v => M.factorization (placePrime v)
  let s : FinitePlace → ℕ := fun v => placePrime v ^ e v
  choose a y0 hay using fun v => exists_nat_sub_eq_mul v (x v) (e v)
  have hs : ∀ v ∈ T, s v ≠ 0 := fun v _ => pow_ne_zero _ (placePrime_fact v).out.ne_zero
  have hpair : Set.Pairwise (T : Set FinitePlace) (Function.onFun Nat.Coprime s) := by
    intro v _ w _ hvw
    apply Nat.coprime_pow_primes _ _ (placePrime_fact v).out (placePrime_fact w).out
    intro heq
    apply hvw
    apply (Rat.HeightOneSpectrum.primesEquiv).injective
    exact Subtype.ext heq
  obtain ⟨z, hz⟩ := Nat.chineseRemainderOfFinset a s T hs hpair
  have hlocal : ∀ v, ∃ yv : v.adicCompletionIntegers ℚ,
      x v - ((z : ℤ) : v.adicCompletionIntegers ℚ) = (M : v.adicCompletionIntegers ℚ) * yv := by
    intro v
    by_cases hv : v ∈ T
    · apply exists_mul_of_ordProj v M hM
      have hmod := (hz v hv)
      have hdvd : (s v : ℤ) ∣ (a v : ℤ) - (z : ℤ) := hmod.dvd
      obtain ⟨t, ht⟩ := hdvd
      refine ⟨y0 v + (t : v.adicCompletionIntegers ℚ), ?_⟩
      have hcast : ((a v : ℤ) : v.adicCompletionIntegers ℚ) - ((z : ℤ) : v.adicCompletionIntegers ℚ) =
          (placePrime v : v.adicCompletionIntegers ℚ) ^ e v * (t : v.adicCompletionIntegers ℚ) := by
        rw [← Int.cast_sub, ht, Int.cast_mul]
        push_cast [s]
        rfl
      have h1 := hay v
      push_cast at hcast
      calc x v - ((z : ℤ) : v.adicCompletionIntegers ℚ)
          = (x v - (a v : v.adicCompletionIntegers ℚ)) +
            ((a v : v.adicCompletionIntegers ℚ) - ((z : ℤ) : v.adicCompletionIntegers ℚ)) := by ring
        _ = _ := by
            rw [h1]
            push_cast
            rw [hcast]
            ring
    · have hnot : ¬ placePrime v ∣ M := fun h => hv ((hT v).mpr h)
      obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd v M hnot
      refine ⟨(↑u⁻¹ : v.adicCompletionIntegers ℚ) * (x v - ((z : ℤ) : v.adicCompletionIntegers ℚ)), ?_⟩
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  choose yv hyv using hlocal
  refine ⟨(z : ℤ), yv, ?_⟩
  funext v
  have := hyv v
  rw [Pi.add_apply, Pi.mul_apply]
  have hzv : ((z : ℤ) : IntegralAdeles) v = ((z : ℤ) : v.adicCompletionIntegers ℚ) := by
    simp
  have hMv : ((M : ℕ) : IntegralAdeles) v = (M : v.adicCompletionIntegers ℚ) := by
    simp
  rw [hzv, hMv, ← this]
  ring

/-- `ℤ ∩ M Ẑ = M ℤ`. -/
theorem int_dvd_of_eq_mul (M : ℕ) (hM : M ≠ 0) (n : ℤ) (y : IntegralAdeles)
    (h : (n : IntegralAdeles) = (M : IntegralAdeles) * y) : (M : ℤ) ∣ n := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have hint : algebraMap ℚ FiniteAdeles ((n : ℚ) / M) ∈ Set.range integralEmbedding := by
    refine ⟨y, ?_⟩
    have h2 := congrArg integralEmbedding h
    rw [map_intCast, map_mul, map_natCast] at h2
    have hMf : (M : FiniteAdeles) = algebraMap ℚ FiniteAdeles (M : ℚ) := by simp
    have hnf : (n : FiniteAdeles) = algebraMap ℚ FiniteAdeles (n : ℚ) := by simp
    have hunit : IsUnit (M : FiniteAdeles) := by
      rw [hMf]
      exact (IsUnit.mk0 _ hMq).map _
    apply hunit.mul_left_cancel
    rw [← h2, hnf, hMf, ← map_mul, mul_div_cancel₀ _ hMq]
  obtain ⟨k, hk⟩ := (PlaneEisensteinContinuation.IntegralRationals.integral_iff_integer _).mp hint
  refine ⟨k, ?_⟩
  have : (n : ℚ) = (M : ℚ) * k := by
    rw [← hk]; field_simp
  exact_mod_cast this

/-- The kernel of reduction modulo three, at the place three. -/
theorem exists_three_mul_of_reduction_zero (x : IntegralAdeles) (h : integralReduction x = 0) :
    ∃ y : placeThree.adicCompletionIntegers ℚ, x placeThree = 3 * y := by
  have hker : integralThree x ∈ RingHom.ker (PadicInt.toZMod (p := 3)) := h
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨y, hy⟩ := hker
  refine ⟨threeIntegralEquiv.symm y, ?_⟩
  apply threeIntegralEquiv.injective
  rw [map_mul, RingEquiv.apply_symm_apply, map_ofNat]
  exact_mod_cast hy

end TernaryPeriodPolynomials.HeckeStability.AdelicApproximation
