module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Transform

@[expose] public section


/-!
# The combined Eichler primitive `Φ₀`

The sum of the holomorphic Eichler primitive and the coefficientwise conjugate of the antiholomorphic one, as a function of `(a, z)`, and its transformation law (`Phi0_transform`).

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

/-- The binomial coefficients `C(n+1, j) (-1)^{n+1-j}` of the Eichler polynomial. -/
def cc (n j : ℕ) : ℂ := ((n + 1).choose j : ℂ) * (-1) ^ (n + 1 - j)

theorem conj_cc (n j : ℕ) : conj (cc n j) = cc n j := by
  unfold cc
  simp [map_mul, map_pow, map_neg, map_natCast]

theorem eval_map_conj (P : MvPolynomial (Fin 2) ℂ) (a : Fin 2 → ℂ) :
    MvPolynomial.eval a (MvPolynomial.map (starRingEnd ℂ) P) =
      conj (MvPolynomial.eval (fun i => conj (a i)) P) := by
  rw [MvPolynomial.eval_map]
  have h := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (RingHom.id ℂ) (fun i => conj (a i)) P
  have e : ((starRingEnd ℂ) ∘ fun i => conj (a i)) = a := by funext i; simp
  rw [e, RingHom.comp_id] at h
  exact h.symm

/-- The `v`-free part of the combined Eichler integral. -/
def Phi0 (n : ℕ) (G H : ℕ → ℂ → ℂ) (a : Fin 2 → ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval a (eichlerPoly n G z) +
    MvPolynomial.eval a (MvPolynomial.map (starRingEnd ℂ) (eichlerPoly n H z))

theorem Phi0_eq_sum (n : ℕ) (G H : ℕ → ℂ → ℂ) (a : Fin 2 → ℂ) (z : ℂ) :
    Phi0 n G H a z = ∑ j ∈ Finset.range (n + 2), (G j z + conj (H j z)) * cc n j * a 1 ^ j * a 0 ^ (n + 1 - j) := by
  unfold Phi0
  rw [eval_map_conj, eval_eichlerPoly, eval_eichlerPoly]
  simp only [map_sum, map_mul, map_pow, map_natCast, map_neg, map_one, Complex.conj_conj]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold cc
  ring

theorem conj_invCoord (γ : GL (Fin 2) ℝ) (a : Fin 2 → ℂ) :
    (fun i => conj (invCoord γ a i)) = invCoord γ (fun i => conj (a i)) := by
  funext i
  fin_cases i <;> simp [invCoord, map_sub, map_mul, map_neg]

theorem holPart (n : ℕ) (f1 f2 : ℂ → ℂ) (G1 G2 : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ) (hdet : γ.det = 1)
    (hG1 : ∀ j z, 0 < z.im → HasDerivAt (G1 j) (f1 z * z ^ j) z)
    (hG2 : ∀ j z, 0 < z.im → HasDerivAt (G2 j) (f2 z * z ^ j) z)
    (hmf : ∀ z : ℂ, 0 < z.im → f1 (mob γ z) = dnm γ z ^ (n + 3) * f2 z)
    (hG2I : ∀ j, G2 j Complex.I = 0) (a : Fin 2 → ℂ) {z : ℂ} (hz : 0 < z.im) :
    MvPolynomial.eval a (eichlerPoly n G1 (mob γ z)) =
      MvPolynomial.eval (invCoord γ a) (eichlerPoly n G2 z) +
        MvPolynomial.eval a (eichlerPoly n G1 (mob γ Complex.I)) := by
  have hI : 0 < (Complex.I : ℂ).im := by simp
  have h := primitive_defect_const' n f1 f2 γ hdet hmf
    (fun v w => MvPolynomial.eval v (eichlerPoly n G1 w)) (fun v w => MvPolynomial.eval v (eichlerPoly n G2 w))
    (fun v z hz => eichlerPoly_hasDerivAt n f1 G1 hG1 v hz) (fun v z hz => eichlerPoly_hasDerivAt n f2 G2 hG2 v hz)
    a hz hI
  simp only [eichlerPoly_base n G2 hG2I, map_zero, sub_zero] at h
  linear_combination h

theorem Phi0_transform (n : ℕ) (f1 f2 g1 g2 : ℂ → ℂ) (G1 G2 H1 H2 : ℕ → ℂ → ℂ) (γ : GL (Fin 2) ℝ)
    (hdet : γ.det = 1)
    (hG1 : ∀ j z, 0 < z.im → HasDerivAt (G1 j) (f1 z * z ^ j) z)
    (hG2 : ∀ j z, 0 < z.im → HasDerivAt (G2 j) (f2 z * z ^ j) z)
    (hH1 : ∀ j z, 0 < z.im → HasDerivAt (H1 j) (g1 z * z ^ j) z)
    (hH2 : ∀ j z, 0 < z.im → HasDerivAt (H2 j) (g2 z * z ^ j) z)
    (hmf : ∀ z : ℂ, 0 < z.im → f1 (mob γ z) = dnm γ z ^ (n + 3) * f2 z)
    (hmg : ∀ z : ℂ, 0 < z.im → g1 (mob γ z) = dnm γ z ^ (n + 3) * g2 z)
    (hG2I : ∀ j, G2 j Complex.I = 0) (hH2I : ∀ j, H2 j Complex.I = 0) (a : Fin 2 → ℂ) {z : ℂ}
    (hz : 0 < z.im) :
    Phi0 n G1 H1 a (mob γ z) = Phi0 n G2 H2 (invCoord γ a) z + Phi0 n G1 H1 a (mob γ Complex.I) := by
  unfold Phi0
  have h1 := holPart n f1 f2 G1 G2 γ hdet hG1 hG2 hmf hG2I a hz
  have h2 := holPart n g1 g2 H1 H2 γ hdet hH1 hH2 hmg hH2I (fun i => conj (a i)) hz
  rw [h1]
  rw [eval_map_conj, eval_map_conj, eval_map_conj, h2, map_add, conj_invCoord γ a]
  ring

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
