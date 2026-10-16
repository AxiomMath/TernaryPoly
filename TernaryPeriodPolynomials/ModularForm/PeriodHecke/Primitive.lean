module

public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Terms
public import TernaryPeriodPolynomials.ModularForm.Endpoint.Uniqueness

@[expose] public section


noncomputable section
open Complex Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryCuspHecke BinaryCuspHeckeEndomorphism

/-- The actual sum of normalized Eichler primitive terms in standard cusp normalization. -/
def heckePrimitive {d : ℕ} (f : Forms d) (p : ℕ) (x y z : ℂ) : ℂ :=
  (p : ℂ)^d * (heckePrimitiveInfinity f p x y z + ∑ b : Fin p, heckePrimitiveFinite f p b x y z)

theorem dilate_ofComplex (p : ℕ) (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) :
    dilate p hp (ofComplex z) = ofComplex ((p : ℂ)*z) := by
  have hr : (0 : ℝ) < p := by exact_mod_cast hp
  apply UpperHalfPlane.ext
  rw [coe_dilate, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos]
  simpa using mul_pos hr hz

theorem divideTranslate_ofComplex (p : ℕ) (hp : 0 < p) (b : Fin p)
    {z : ℂ} (hz : 0 < z.im) :
    divideTranslate p hp b (ofComplex z) = ofComplex ((z+b.val)/p) := by
  have hr : (0 : ℝ) < p := by exact_mod_cast hp
  apply UpperHalfPlane.ext
  rw [coe_divideTranslate, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos]
  simpa using div_pos hz hr

/-- The derivative of the actual primitive sum is exactly the differential of standard T_p. -/
theorem heckePrimitive_hasDerivAt {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (heckePrimitive f p x y) (periodIntegrand (T d p f) x y z) z := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h₀ := heckePrimitiveInfinity_hasDerivAt f p hp x y hz
  have hs := HasDerivAt.fun_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin p))) =>
    heckePrimitiveFinite_hasDerivAt f p hp b x y hz)
  have h := (h₀.add hs).const_mul ((p : ℂ)^d)
  have he : (p : ℂ)^d * (f (ofComplex (p*z))*(z*y-x)^d*p +
      ∑ b : Fin p, f (ofComplex ((z+b.val)/p))*(z*y-x)^d/(p : ℂ)^(d+1)) =
        periodIntegrand (T d p f) x y z := by
    rw [periodIntegrand, T_apply, primeOperator, dilate_ofComplex p hp hz]
    simp_rw [divideTranslate_ofComplex p hp _ hz]
    rw [←Finset.sum_div, ←Finset.sum_mul, pow_succ]
    field_simp
  simpa only [heckePrimitive, he] using! h

/-- The standard primitive sum has the same zero normalization at infinity as the genuine E(T_p f). -/
theorem heckePrimitive_tendsto {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (x y : ℂ) : Tendsto (fun t : ℝ => heckePrimitive f p x y (I*t)) atTop (𝓝 0) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hs := tendsto_finsetSum Finset.univ (fun b _ => heckePrimitiveFinite_tendsto f p hp b x y)
  have h := ((heckePrimitiveInfinity_tendsto f p hp x y).add hs).const_mul ((p : ℂ)^d)
  simpa only [heckePrimitive, Finset.sum_const_zero, add_zero, mul_zero] using h

/-- Exact actual Eichler primitive formula for the genuine standard cusp Hecke endomorphism. -/
theorem eichlerIntegral_hecke {d : ℕ} (f : Forms d) (p : ℕ) [Fact p.Prime]
    (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral (T d p f) x y z = heckePrimitive f p x y z := by
  have h := primitive_difference_from_axis_limits _ _ _ 0 0
    (eichlerIntegral_hasDerivAt (T d p f) x y)
    (fun z hz => heckePrimitive_hasDerivAt f p x y hz)
    (eichlerIntegral_axis_tendsto_infty (T d p f) x y)
    (heckePrimitive_tendsto f p x y) hz
  simpa using h

end TernaryPoly.BinaryCuspSymbol
