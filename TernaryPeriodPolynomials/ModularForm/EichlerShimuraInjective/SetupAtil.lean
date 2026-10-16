module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.ProductFamily

@[expose] public section


/-!
# Standing hypotheses and the coset sum

`Setup`: the data of two cusp forms, their Eichler primitives and a coboundary relation; `Atil_eq_holAnti`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

theorem toR_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((toR g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp [toR, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

theorem mob_T (z : ℂ) : mob (toR ModularGroup.T) z = z + 1 := by
  unfold mob
  rw [toR_apply, toR_apply, toR_apply, toR_apply]
  simp [ModularGroup.T]

theorem dnm_T (z : ℂ) : dnm (toR ModularGroup.T) z = 1 := by
  unfold dnm
  rw [toR_apply, toR_apply]
  simp [ModularGroup.T]

theorem mob_S (z : ℂ) : mob (toR ModularGroup.S) z = -1 / z := by
  unfold mob
  rw [toR_apply, toR_apply, toR_apply, toR_apply]
  simp [ModularGroup.S]

theorem dnm_S (z : ℂ) : dnm (toR ModularGroup.S) z = z := by
  unfold dnm
  rw [toR_apply, toR_apply]
  simp [ModularGroup.S]


/-- The standing hypotheses of the injectivity argument. -/
structure Setup (Γ : Subgroup SL(2, ℤ)) (n : ℕ) (f g : ℂ → ℂ) (Gf Gg : ℕ → ℂ → ℂ)
    (v : MvPolynomial (Fin 2) ℂ) : Prop where
  hf : DifferentiableOn ℂ f Uset
  hg : DifferentiableOn ℂ g Uset
  mf : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im → f (mob (toR γ) z) = dnm (toR γ) z ^ (n + 3) * f z
  mg : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im → g (mob (toR γ) z) = dnm (toR γ) z ^ (n + 3) * g z
  dGf : ∀ j z, 0 < z.im → HasDerivAt (Gf j) (f z * z ^ j) z
  dGg : ∀ j z, 0 < z.im → HasDerivAt (Gg j) (g z * z ^ j) z
  Gf0 : ∀ j, Gf j Complex.I = 0
  Gg0 : ∀ j, Gg j Complex.I = 0
  vh : v.IsHomogeneous (n + 1)
  cob : ∀ γ ∈ Γ, eichlerCocycle n Gf (toR γ) + MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n Gg (toR γ)) =
    MvPolynomial.bind₁ (invCoordPoly (toR γ)) v - v

section Main

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ}
  {v : MvPolynomial (Fin 2) ℂ}

omit [Γ.FiniteIndex] in
theorem Aval_Gamma (S : Setup Γ n f g Gf Gg v) :
    ∀ γ ∈ Γ, ∀ w : ℂ, 0 < w.im →
      Aval n f Gf Gg v (mob (toR γ) w) = conj (dnm (toR γ) w) ^ 2 * Aval n f Gf Gg v w := by
  intro γ hγ w hw
  have := Aval_cov n f g Gf Gg v S.vh (toR γ) (toR_det γ) S.dGf S.dGg (S.mf γ hγ) (S.mg γ hγ) S.Gf0 S.Gg0
    (S.cob γ hγ) hw
  exact this

/-- The coset representatives used in the sum. -/
def gq (Γ : Subgroup SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ) := (Quotient.out q)⁻¹

theorem Atil_eq_holAnti (_S : Setup Γ n f g Gf Gg v) {z : ℂ} (_hz : 0 < z.im) :
    Atil Γ (Aval n f Gf Gg v) z = holAnti (uQ (gq Γ) (u0 n Gf)) (wQ (gq Γ) (w0 n f Gg v)) z := by
  rw [holAnti_Q]
  unfold Atil Ahat Ag gq
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Aval_eq_holAnti, map_pow]

end Main

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
