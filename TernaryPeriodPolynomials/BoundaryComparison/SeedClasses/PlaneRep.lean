module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneGroup

@[expose] public section


/-!
# The coefficient representation of a plane parabolic group

`ρ(g) = realCoefficient n (σ g)`, the library's `Sym^n((ℂ³)*) ⊗ det⁻¹` for the real matrix
`[[λ(g), w(g)], [0, 1]]`, on the normed model `Coef n` of `E_n`, and its explicit polynomial form
`rho` of `RhoAction`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G)

/-- The coefficient representation (over `ℂ`) of the plane parabolic group. -/
def rhoC (n : ℕ) : Representation ℂ G (HomogeneousPoly n) :=
  (GeneralEisenstein.realCoefficient n).comp D.sigma

theorem rhoC_coe (n : ℕ) (g : G) (q : HomogeneousPoly n) :
    ((D.rhoC n g q : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      rho (D.plm g) (q : MvPolynomial (Fin 3) ℂ) := by
  have hinv : (D.plm g)⁻¹ = D.plm g⁻¹ :=
    Matrix.inv_eq_right_inv (by rw [← D.plm_mul, mul_inv_cancel, D.plm_one])
  have hdet : (D.plm g).det = 1 := D.det_plm g
  unfold rhoC
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (D.sigma g))) (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  rw [hinv, hdet]
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map]
  have hd : ((D.plm g).map Complex.ofReal).det = 1 := by
    have := RingHom.map_det Complex.ofRealHom (D.plm g)
    rw [hdet, map_one] at this
    exact this.symm
  rw [hd, inv_one, one_smul, hinv]

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
