module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.ModelFamily
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Rotation

@[expose] public section


/-!
# The `K`-type weight gap of the Bergman model

The rotation `rotGL θ` acts on the Taylor coefficient `coeffPlus F n` of a Bergman function by
the character `exp ((k + 2 n) θ i)` and on `coeffMinus F n` by its inverse.  A function `F` on
which all rotations act through `θ ↦ exp (m θ i)` therefore has `m = k + 2 n` or `m = -(k + 2 n)`
for every nonzero coefficient (`bergman_rotation_gap`), so a nonzero eigenvector of rotation weight
`m` has `k ≤ |m|`.  This is the `WeightGap` of every cuspidal representation embedded
equivariantly in `bergmanRep M` (`weightGap_of_embedding`), in particular of every constituent
`cyclicOfLE` built from it (`weightGap_cyclicOfLE`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binaryRotations)
open TernaryPeriodPolynomials.Regularity
open TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility
open TernaryPeriodPolynomials.Automorphic.ModelFamily

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- Two integer frequencies whose exponentials `θ ↦ exp (a θ i)` and `θ ↦ exp (b θ i)` agree for
every real `θ` are equal. -/
theorem eq_of_exp_mul_eq (a b : ℤ)
    (h : ∀ θ : ℝ, Complex.exp (((a : ℂ) * θ) * Complex.I) =
      Complex.exp (((b : ℂ) * θ) * Complex.I)) : a = b := by
  by_contra hne
  have hd : (a : ℂ) - b ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ((a : ℂ) - b) * (θ : ℂ) = (Real.pi : ℂ) :=
    ⟨Real.pi / ((a : ℝ) - b), by push_cast; field_simp⟩
  have hsplit : ((a : ℂ) * θ) * Complex.I =
      ((b : ℂ) * θ) * Complex.I + Real.pi * Complex.I := by
    linear_combination Complex.I * hθ
  have h' := h θ
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one] at h'
  exact Complex.exp_ne_zero (((b : ℂ) * θ) * Complex.I) (by linear_combination (-1 / 2 : ℂ) * h')

/-- A nonzero upper coefficient of a rotation eigenvector of weight `m` has `m = k + 2 n`. -/
theorem eq_of_coeffPlus_ne_zero_of_rotation {k : ℕ} (M : FiniteModel k) {F : BergmanSpace k M.E}
    {m : ℤ} (hF : ∀ θ : ℝ, bergmanRep M (atInfinity (rotGL θ)) F =
      Complex.exp (((m : ℂ) * θ) * Complex.I) • F) {n : ℕ} (hn : coeffPlus F n ≠ 0) :
    m = (k : ℤ) + 2 * n := by
  have h5 : ∀ θ : ℝ, Complex.exp (((((k : ℤ) + 2 * n : ℤ) : ℂ) * θ) * Complex.I) =
      Complex.exp (((m : ℂ) * θ) * Complex.I) := by
    intro θ
    have hθ := hF θ
    rw [bergmanRep_atInfinity] at hθ
    have h := congrArg (fun G => coeffPlus G n) hθ
    simp only [coeffPlus_realRep_rot, coeffPlus_smul] at h
    have h2 : (Complex.exp ((((k : ℂ) + 2 * n) * θ) * Complex.I) -
        Complex.exp (((m : ℂ) * θ) * Complex.I)) • coeffPlus F n = 0 := by
      rw [sub_smul, h, sub_self]
    exact_mod_cast sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hn)
  exact (eq_of_exp_mul_eq _ _ h5).symm

/-- A nonzero lower coefficient of a rotation eigenvector of weight `m` has `m = -(k + 2 n)`. -/
theorem eq_of_coeffMinus_ne_zero_of_rotation {k : ℕ} (M : FiniteModel k) {F : BergmanSpace k M.E}
    {m : ℤ} (hF : ∀ θ : ℝ, bergmanRep M (atInfinity (rotGL θ)) F =
      Complex.exp (((m : ℂ) * θ) * Complex.I) • F) {n : ℕ} (hn : coeffMinus F n ≠ 0) :
    m = -((k : ℤ) + 2 * n) := by
  have h5 : ∀ θ : ℝ, Complex.exp ((((-((k : ℤ) + 2 * n) : ℤ) : ℂ) * θ) * Complex.I) =
      Complex.exp (((m : ℂ) * θ) * Complex.I) := by
    intro θ
    have hθ := hF θ
    rw [bergmanRep_atInfinity] at hθ
    have h := congrArg (fun G => coeffMinus G n) hθ
    simp only [coeffMinus_realRep_rot, coeffMinus_smul] at h
    have h2 : (Complex.exp (-(((k : ℂ) + 2 * n) * θ) * Complex.I) -
        Complex.exp (((m : ℂ) * θ) * Complex.I)) • coeffMinus F n = 0 := by
      rw [sub_smul, h, sub_self]
    have e : (((-((k : ℤ) + 2 * n) : ℤ) : ℂ) * θ) * Complex.I =
        -(((k : ℂ) + 2 * n) * θ) * Complex.I := by
      push_cast
      ring
    rw [e]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hn)
  exact (eq_of_exp_mul_eq _ _ h5).symm

/-- **The rotation gap of the Bergman model.**  A nonzero element of the Bergman space of weight
`k` on which the rotations of `SO(2)` act through `θ ↦ exp (m θ i)` has `k ≤ |m|`. -/
theorem bergman_rotation_gap {k : ℕ} (M : FiniteModel k) (hk : 2 ≤ k) (F : BergmanSpace k M.E)
    (m : ℤ) (hF : ∀ θ : ℝ, bergmanRep M (atInfinity (rotGL θ)) F =
      Complex.exp (((m : ℂ) * θ) * Complex.I) • F) (hne : F ≠ 0) : (k : ℤ) ≤ |m| := by
  by_contra hlt
  obtain ⟨hm1, hm2⟩ := abs_lt.1 (not_le.1 hlt)
  refine hne (eq_of_coeff hk (fun n => ?_) (fun n => ?_))
  · have h0 : coeffPlus (0 : BergmanSpace k M.E) n = 0 := by
      simpa using coeffPlus_smul (0 : ℂ) (0 : BergmanSpace k M.E) n
    rw [h0]
    by_contra hn
    have h := eq_of_coeffPlus_ne_zero_of_rotation M hF hn
    omega
  · have h0 : coeffMinus (0 : BergmanSpace k M.E) n = 0 := by
      simpa using coeffMinus_smul (0 : ℂ) (0 : BergmanSpace k M.E) n
    rw [h0]
    by_contra hn
    have h := eq_of_coeffMinus_ne_zero_of_rotation M hF hn
    omega

/-- The matrix of `binaryRotations a`. -/
theorem binaryRotations_val_eq (a : Circle) :
    (binaryRotations a).val = !![(a : ℂ).re, -(a : ℂ).im; (a : ℂ).im, (a : ℂ).re] := rfl

/-- The rotation of the circle element `exp (θ i)` is `rotGL θ`. -/
theorem binaryRotations_exp_eq_rotGL (θ : ℝ) : binaryRotations (Circle.exp θ) = rotGL θ := by
  apply Units.ext
  rw [binaryRotations_val_eq, rotGL_val, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- The `m`-th power of `exp (θ i)` in the circle is `exp (m θ i)`. -/
theorem circle_exp_zpow (θ : ℝ) (m : ℤ) :
    ((Circle.exp θ : Circle) : ℂ) ^ m = Complex.exp (((m : ℂ) * θ) * Complex.I) := by
  rw [Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  ring

/-- **The weight gap, abstractly.**  A cuspidal representation `σ` equivariantly embedded (by a
homogeneous map `ι` that vanishes only at `0`) in the holomorphic model `bergmanRep M` of weight
`n + 3` has the weight gap `WeightGap σ n`. -/
theorem weightGap_of_embedding {n : ℕ} (M : FiniteModel (n + 3)) (σ : CuspidalRepresentation)
    (ι : σ.H → BergmanSpace (n + 3) M.E) (hzero : ∀ u, ι u = 0 → u = 0)
    (hsmul : ∀ (c : ℂ) u, ι (c • u) = c • ι u)
    (hint : ∀ g u, ι (σ.π g u) = bergmanRep M g (ι u)) : WeightGap σ n := by
  intro m u hu hm
  by_contra hu0
  have hne : ι u ≠ 0 := fun h => hu0 (hzero u h)
  have hrot : ∀ θ : ℝ, bergmanRep M (atInfinity (rotGL θ)) (ι u) =
      Complex.exp (((m : ℂ) * θ) * Complex.I) • ι u := by
    intro θ
    have h := hu (Circle.exp θ)
    rw [binaryRotations_exp_eq_rotGL] at h
    rw [← hint, h, hsmul, circle_exp_zpow]
  have h := bergman_rotation_gap M (by omega) (ι u) m hrot hne
  push_cast at h
  exact absurd hm (not_lt.mpr h)

/-- The Bergman space of weight `n + 3` over a finite-adelic model is complete. -/
instance bergmanSpace_completeSpace_three {n : ℕ} (M : FiniteModel (n + 3)) :
    CompleteSpace (BergmanSpace (n + 3) M.E) :=
  have : Fact (2 ≤ n + 3) := ⟨by omega⟩
  inferInstance

/-- **The weight gap of the cuspidal constituents.**  Every cuspidal representation `cyclicOfLE`
built from a nonzero vector of a compression-simple subspace of the holomorphic model of weight
`n + 3` has the weight gap `WeightGap _ n`. -/
theorem weightGap_cyclicOfLE {n : ℕ} (M : FiniteModel (n + 3))
    (R : SubRepresentation.Realization (bergmanRep M) IsUnitary.norm_map)
    (hc : ∀ v, Continuous (fun g => bergmanRep M g v)) (C : Subgroup BinaryAdelicGL)
    (χ : C → ℂ) {S N : Submodule ℂ (BergmanSpace (n + 3) M.E)} [FiniteDimensional ℂ S]
    (hNS : N ≤ S) (hN : CompressionSimple (bergmanRep M) C χ N)
    {v : BergmanSpace (n + 3) M.E} (hvN : v ∈ N) (hv : v ≠ 0) :
    WeightGap (cyclicOfLE R hc C χ hNS hN hvN hv) n :=
  weightGap_of_embedding M (cyclicOfLE R hc C χ hNS hN hvN hv)
    (fun u => Subtype.val (show cyclicSpan (bergmanRep M) v from u))
    (fun _ hu => Subtype.ext hu) (fun _ _ => rfl) (fun _ _ => rfl)

end TernaryPeriodPolynomials.Automorphic.Constituent

end
