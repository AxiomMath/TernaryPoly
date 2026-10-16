module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.Eigenperiod

@[expose] public section


/-!
# The printed sentence fails in the library's exponent-`+1` Hom model (and ONLY there)

Formalized by Claude Sonnet 5.5.

**Scope.**  This file refutes a statement about the library's Hom-model operator
(`homPlusComplexHecke`, see `Scalar.lean`), a choice of rational extension (`det^e`, `e = +1`) of the integral
`GL₂(ℤ)` coefficient system.  It does NOT refute the paper: the paper's `T₂(p)` is a homology
correspondence whose comparison with this Hom operator is not established.

Paper: "The homological
correspondence above is the standard Hecke operator on the period polynomial of `h`."  Read for the Hom model,
the sentence is `HomModelPrintedClaim d hd p`: the exponent-`+1` Hom-model `T₂(p)` and the standard analytic
`T_p` agree on the period of every level-one cusp form of weight `d + 2`.

By `homPlus_periodMap_zpow`, `T₂(p) (periodMap f) = p^{1-d} • periodMap (T_p f)`; the period map is injective,
so for `d ≥ 2`

* `printedClaim_iff`: `HomModelPrintedClaim d hd p ↔ T_p = 0` on `S_{d+2}`;
* `not_forall_printedClaim`: if `dim S_{d+2} ≥ 2` the Hom-model claim fails for some prime `p` (if it held for
  every prime, every form would be a simultaneous Hecke eigenform with all eigenvalues `0`, hence determined
  by its first Fourier coefficient, so `dim ≤ 1`);
* `not_forall_printedClaim_weight24`: the instance `d = 22` (weight `24`, `dim S_24 = 2`), needing no
  numerical value of any Fourier coefficient.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open scoped MatrixGroups
open TernaryPoly TernaryPoly.BinaryComplexPeriod TernaryPoly.BinaryCuspPeriod
open TernaryPoly.BinaryCuspPeriodDetection

/-- **The printed sentence of the paper, read for the library's exponent-`+1` Hom model**: this
correspondence `T₂(p)` equals the standard analytic `T_p` on the period of every cusp form of weight `d + 2`. -/
def HomModelPrintedClaim (d : ℕ) (hd : Even d) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ f : Forms d, homPlusComplexHecke d p (periodMap d hd f) =
    periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f)

/-- The analytic period map is injective (kernel stability from `periodMap_hecke`). -/
theorem periodMap_injective' (d : ℕ) (hd : Even d) : Function.Injective (periodMap d hd) :=
  periodMap_injective_of_intertwines d hd (primePeriodHecke d) (primeScalar d)
    (BinaryLiftableResidueDetection.actualIntertwining d hd)

theorem zpow_one_sub_ne_one {d : ℕ} (hd2 : 2 ≤ d) (p : ℕ) (hp : p.Prime) :
    (p : ℂ) ^ ((1 : ℤ) - d) ≠ 1 := by
  intro h
  have e : (1 : ℤ) - d = -((d - 1 : ℕ) : ℤ) := by omega
  rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h
  have h' : p ^ (d - 1) = 1 := by exact_mod_cast h
  rcases Nat.pow_eq_one.mp h' with h1 | h1
  · exact hp.one_lt.ne' h1
  · omega

/-- For `d ≥ 2`, the printed claim at the prime `p` holds exactly when `T_p` vanishes on `S_{d+2}`. -/
theorem printedClaim_iff {d : ℕ} (hd : Even d) (hd2 : 2 ≤ d) (p : ℕ) [Fact p.Prime] :
    HomModelPrintedClaim d hd p ↔ ∀ f : Forms d, BinaryCuspHeckeEndomorphism.T d p f = 0 := by
  constructor
  · intro h f
    have h1 := h f
    rw [homPlus_periodMap_zpow hd f p] at h1
    by_contra hne
    have hx : periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) ≠ 0 := fun hz =>
      hne (periodMap_injective' d hd (hz.trans (map_zero _).symm))
    have h2 : (p : ℂ) ^ ((1 : ℤ) - d) • periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) =
        (1 : ℂ) • periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) := by
      rw [h1, one_smul]
    exact zpow_one_sub_ne_one hd2 p (Fact.out : p.Prime) (smul_left_injective ℂ hx h2)
  · intro h f
    rw [homPlus_periodMap_zpow hd f p, h f, map_zero, smul_zero]

/-- Fourier coefficient `a(1)` as a linear functional on `S_{d+2}`. -/
def firstCoefficient (d : ℕ) : Forms d →ₗ[ℂ] ℂ where
  toFun f := coefficients f 1
  map_add' f g := by
    have hp : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by
      simpa only [Subgroup.strictWidthInfty_SL2Z] using
        Subgroup.strictWidthInfty_mem_strictPeriods 𝒮ℒ
    change (UpperHalfPlane.qExpansion 1 (⇑(f + g))).coeff 1 =
      (UpperHalfPlane.qExpansion 1 (⇑f)).coeff 1 + (UpperHalfPlane.qExpansion 1 (⇑g)).coeff 1
    rw [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num) hp f g]
    simp
  map_smul' c f := BinaryCuspHecke.coefficients_smul f c 1

/-- If `T_p` vanishes for every prime `p`, a cusp form is determined by its first Fourier coefficient. -/
theorem firstCoefficient_injective {d : ℕ}
    (hT : ∀ (p : ℕ) [Fact p.Prime] (f : Forms d), BinaryCuspHeckeEndomorphism.T d p f = 0) :
    Function.Injective (firstCoefficient d) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  have he : BinaryCuspHecke.IsPrimeEigenform f (fun _ => 0) := by
    intro p z
    have : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
    have h := congrArg (fun g : Forms d => g z) (hT p.val f)
    simpa using h
  exact BinaryCuspHecke.first_coefficient_ne_zero f _ he hne hf

theorem finrank_le_one_of_T_zero {d : ℕ}
    (hT : ∀ (p : ℕ) [Fact p.Prime] (f : Forms d), BinaryCuspHeckeEndomorphism.T d p f = 0) :
    Module.finrank ℂ (Forms d) ≤ 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (firstCoefficient_injective hT)
  simpa using h

/-- If `dim S_{d+2} ≥ 2`, the printed claim fails for at least one prime `p`. -/
theorem not_forall_printedClaim {d : ℕ} (hd : Even d) (h2 : 2 ≤ Module.finrank ℂ (Forms d)) :
    ¬ ∀ (p : ℕ) [Fact p.Prime], HomModelPrintedClaim d hd p := by
  intro h
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have hsub : Subsingleton (Forms d) :=
      ⟨fun f g => by rw [forms_eq_zero_of_lt_ten (by omega) f, forms_eq_zero_of_lt_ten (by omega) g]⟩
    have := Module.finrank_zero_of_subsingleton (R := ℂ) (M := Forms d)
    omega
  have := finrank_le_one_of_T_zero (d := d)
    (fun (p : ℕ) [Fact p.Prime] f => (printedClaim_iff hd hd2 p).mp (h p) f)
  omega

/-- **Weight 24 (`d = 22`, `dim S_24 = 2`)**: the printed claim is false for at least one prime. -/
theorem not_forall_printedClaim_weight24 :
    ¬ ∀ (p : ℕ) [Fact p.Prime], HomModelPrintedClaim 22 (by decide) p := by
  apply not_forall_printedClaim
  rw [forms_finrank 22 (by decide)]
  decide

/-- If `T_p f ≠ 0` for some `f` of weight `d + 2 > 3`, the Hom-model `T₂(p)` and the standard `T_p` differ
on `periodMap f`, by the factor `p^{1-d} ≠ 1`. -/
theorem not_printedClaim_of_T_ne_zero {d : ℕ} (hd : Even d) (hd2 : 2 ≤ d) (p : ℕ) [Fact p.Prime]
    (f : Forms d) (hf : BinaryCuspHeckeEndomorphism.T d p f ≠ 0) : ¬ HomModelPrintedClaim d hd p :=
  fun h => hf ((printedClaim_iff hd hd2 p).mp h f)

/-- **Weight 12, `p = 2`, explicitly**: for every cusp form `f` of weight 12,
`T₂(2) (periodMap f) = 2^{-9} • periodMap (T_2 f)`; since `T_2 Δ = -24 Δ` this differs from the standard
`T_2 = -24` on `periodMap Δ` by the factor `2^{-9}`. -/
theorem homPlus_weight12_prime2 (f : Forms 10) :
    homPlusComplexHecke 10 2 (periodMap 10 (by decide) f) =
      (1 / 512 : ℂ) • periodMap 10 (by decide) (BinaryCuspHeckeEndomorphism.T 10 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [homPlus_periodMap_zpow (by decide) f 2]
  congr 1
  norm_num [zpow_neg]

end TernaryPeriodPolynomials.Argument.HeckeNormalization
