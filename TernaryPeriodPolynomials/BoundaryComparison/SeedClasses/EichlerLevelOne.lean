module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RadicalEichlerClass
public import TernaryPeriodPolynomials.ModularForm.Symbol.Cocycle

@[expose] public section


/-!
# Lemma C.3: agreement of the general Eichler cocycle with the library's level-one cocycle

For `Λ_P = SL₂(ℤ)` the library has the Eichler integral `eichlerIntegral` (normalized at the cusp
`∞`) and its transformation constants `slConstant`, with the cocycle relation `slConstant_mul`.
The general Eichler cocycle of `EichlerClass` (normalized at the base point `i`) differs from it by
the explicit coboundary of `κ(v) = eichlerIntegral f v₀ v₁ i`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

open TernaryPoly.BinaryCuspPeriod TernaryPoly.BinaryCuspSymbol

theorem mob_coe_sl (g : SL2) (z : ℂ) :
    mob (g : GL (Fin 2) ℝ) z = slMobius g z := by
  simp [mob, slMobius]

theorem invCoord_coe_sl (g : SL2) (v : Fin 2 → ℂ) :
    invCoord (g : GL (Fin 2) ℝ) v = slCoordinates g⁻¹ v := by
  rw [slCoordinates_inv]
  ext i
  fin_cases i <;> simp [invCoord]

/-- The `i`-normalized polynomial primitive differs from the library's Eichler integral by the
constant `κ(v) = eichlerIntegral f v₀ v₁ i`, on the whole upper half-plane. -/
theorem eichlerIntegral_eq_poly_add (n : ℕ) (f : Forms (n + 1)) (G : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    (v : Fin 2 → ℂ) {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral f (v 0) (v 1) z =
      MvPolynomial.eval v (eichlerPoly n G z) + eichlerIntegral f (v 0) (v 1) Complex.I := by
  have hder : ∀ u : ℂ, 0 < u.im →
      HasDerivAt (fun u => eichlerIntegral f (v 0) (v 1) u -
        MvPolynomial.eval v (eichlerPoly n G u)) 0 u := by
    intro u hu
    have h1 := eichlerIntegral_hasDerivAt f (v 0) (v 1) u hu
    have h2 := eichlerPoly_hasDerivAt n (fun z => f (ofComplex z)) G hG v hu
    have h3 := h1.sub h2
    have h5 : periodIntegrand f (v 0) (v 1) u - binaryIntegrand n (fun z => f (ofComplex z)) v u
        = 0 := by
      simp [periodIntegrand, binaryIntegrand]
    exact h3.congr_deriv h5
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconv : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hI : 0 < (Complex.I : ℂ).im := by simp
  have hc := IsOpen.is_const_of_deriv_eq_zero hopen hconv
    (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hder u hu).deriv) hz hI
  simp only [eichlerPoly_base n G hG0, map_zero, sub_zero] at hc
  linear_combination hc

/-- **Agreement at level one.** The library's transformation constants `slConstant` of the
Eichler integral equal the general Eichler cocycle `eichlerCocycle` up to the coboundary of
`κ(v) = eichlerIntegral f v₀ v₁ i`, for every `g ∈ SL₂(ℤ)`. -/
theorem slConstant_eq_eichlerCocycle_add (n : ℕ) (f : Forms (n + 1)) (G : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    (g : SL2) (v : Fin 2 → ℂ) :
    slConstant f g v =
      MvPolynomial.eval v (eichlerCocycle n G (g : GL (Fin 2) ℝ)) +
        eichlerIntegral f (v 0) (v 1) Complex.I -
          eichlerIntegral f (slCoordinates g⁻¹ v 0) (slCoordinates g⁻¹ v 1) Complex.I := by
  have hI : 0 < (Complex.I : ℂ).im := by simp
  unfold slConstant
  rw [eichlerIntegral_eq_poly_add n f G hG0 hG v (slMobius_im_pos g hI)]
  unfold eichlerCocycle
  rw [mob_coe_sl]

/-- **The normalizing constant is a homogeneous binary form.** `κ(v) = eichlerIntegral f v₀ v₁ i`
is the evaluation of a homogeneous polynomial of degree `n + 1` in `v = (v₀, v₁)` (the
negative of the moment integral over `(1, ∞)`), so the coboundary of
`slConstant_eq_eichlerCocycle_add` lies in the coefficient module `Sym^{n+1}`. -/
theorem eichlerIntegral_base_isPoly (n : ℕ) (f : Forms (n + 1)) :
    ∃ P : MvPolynomial (Fin 2) ℂ, MvPolynomial.IsHomogeneous P (n + 1) ∧
      ∀ v : Fin 2 → ℂ, eichlerIntegral f (v 0) (v 1) Complex.I = MvPolynomial.eval v P := by
  refine ⟨-∑ j ∈ Finset.range (n + 2),
    MvPolynomial.C (((n + 1).choose j : ℂ) * (-1) ^ j *
      ∫ t : ℝ in Set.Ioi 1, axisIntegrand f (n + 1 - j) t) *
        MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ (n + 1 - j), ?_, ?_⟩
  · refine (MvPolynomial.IsHomogeneous.sum _ _ _ fun j hj => ?_).neg
    have hj' : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hj
    have h1 := ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow j).mul
      ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow (n + 1 - j))
    have e : 1 * j + 1 * (n + 1 - j) = n + 1 := by omega
    rw [e] at h1
    have h2 := (MvPolynomial.isHomogeneous_C (Fin 2)
      (((n + 1).choose j : ℂ) * (-1) ^ j *
        ∫ t : ℝ in Set.Ioi 1, axisIntegrand f (n + 1 - j) t)).mul h1
    rw [zero_add] at h2
    rw [mul_assoc]
    exact h2
  · intro v
    have hint : ∀ j ∈ Finset.range (n + 2),
        MeasureTheory.IntegrableOn (fun t : ℝ =>
          ((n + 1).choose j : ℂ) * (-1) ^ j * v 0 ^ j * v 1 ^ (n + 1 - j) *
            axisIntegrand f (n + 1 - j) t) (Set.Ioi 1) := fun j _ =>
      ((axisIntegrand_integrable f (n + 1 - j)).mono_set
        (Set.Ioi_subset_Ioi zero_le_one)).const_mul _
    have h := MeasureTheory.integral_finsetSum _ hint
    unfold eichlerIntegral
    simp_rw [rayIntegrand_binomial]
    rw [sub_self, zero_sub, h]
    simp only [map_neg, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_const_mul]
    ring

/-- **Agreement at level one, inside the coefficient module.** The library's cocycle `slConstant`
equals the general Eichler cocycle plus the coboundary of a homogeneous binary form `κ` of degree
`n + 1`, as an identity of polynomials. -/
theorem slConstant_eq_eichlerCocycle_add_coboundary (n : ℕ) (f : Forms (n + 1)) (G : ℕ → ℂ → ℂ)
    (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z) :
    ∃ P : MvPolynomial (Fin 2) ℂ, MvPolynomial.IsHomogeneous P (n + 1) ∧
      ∀ (g : SL2) (v : Fin 2 → ℂ), slConstant f g v = MvPolynomial.eval v
        (eichlerCocycle n G (g : GL (Fin 2) ℝ) + P -
          MvPolynomial.bind₁ (invCoordPoly (g : GL (Fin 2) ℝ)) P) := by
  obtain ⟨P, hP, hPv⟩ := eichlerIntegral_base_isPoly n f
  refine ⟨P, hP, fun g v => ?_⟩
  rw [slConstant_eq_eichlerCocycle_add n f G hG0 hG g v, map_sub, map_add,
    eval_bind₁_invCoordPoly, invCoord_coe_sl, ← hPv v, ← hPv (slCoordinates g⁻¹ v)]

end TernaryPeriodPolynomials.Argument.SeedC3
