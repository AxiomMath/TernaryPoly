module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.QComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Inv
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.HomModel
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceDescent

@[expose] public section


/-!
# `Γ(6) ⊂ SL₃(ℤ)` versus the model group `principalSix ⊂ GL₃(ℤ)`

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.IntegralGL3Congruence

/-- The inclusion `Γ(6) ⊂ SL₃(ℤ)` into the model group `principalSix ⊂ GL₃(ℤ)`. -/
def gammaSixHom : gammaN 6 →* Γ6 where
  toFun p := ⟨Matrix.SpecialLinearGroup.toGL p.1, p.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

theorem gammaSixHom_injective : Function.Injective gammaSixHom := by
  intro a b h
  apply Subtype.ext
  have h1 : Matrix.SpecialLinearGroup.toGL a.1 = Matrix.SpecialLinearGroup.toGL b.1 :=
    congrArg Subtype.val h
  apply Subtype.ext
  have := congrArg (fun g : GL (Fin 3) ℤ => (g : Matrix (Fin 3) (Fin 3) ℤ)) h1
  exact this

theorem gammaSixHom_surjective : Function.Surjective gammaSixHom := by
  intro g
  have hdet : (g.1 : GL (Fin 3) ℤ).val.det = 1 := principalSix_det_one g.1 g.2
  refine ⟨⟨⟨(g.1 : GL (Fin 3) ℤ).val, hdet⟩, ?_⟩, ?_⟩
  · change Matrix.SpecialLinearGroup.toGL ⟨(g.1 : GL (Fin 3) ℤ).val, hdet⟩ ∈ principal 6
    have : Matrix.SpecialLinearGroup.toGL ⟨(g.1 : GL (Fin 3) ℤ).val, hdet⟩ = g.1 := by
      apply Units.ext
      rfl
    rw [this]
    exact g.2
  · apply Subtype.ext
    apply Units.ext
    rfl

/-- **`Γ(6) ≃ principalSix`**: the isomorphism of the neat principal congruence subgroup of `SL₃(ℤ)` with the model group. -/
def gammaSixEquiv : gammaN 6 ≃* Γ6 :=
  MulEquiv.ofBijective gammaSixHom ⟨gammaSixHom_injective, gammaSixHom_surjective⟩

theorem gammaSixEquiv_apply (p : gammaN 6) : ((gammaSixEquiv p : Γ6) : GL (Fin 3) ℤ) = Matrix.SpecialLinearGroup.toGL p.1 := rfl


theorem iotaQ_gammaSix (p : gammaN 6) :
    iotaQ (gammaSixEquiv p) = Matrix.SpecialLinearGroup.mapGL ℚ p.1 := by
  apply Units.ext
  ext i j
  simp [iotaQ, gammaSixEquiv_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL]

section Coefficients

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open GeneralEisenstein

variable (n : ℕ) (χ : RankOneCharacter)

/-- The coefficient module `E_n` as a representation of the model group `Γ(6)`. -/
def rho6 : Representation ℂ Γ6 (HomogeneousPoly n) :=
  (rationalCoefficientComponent n χ).comp iotaQ

theorem rho6_gammaSix (p : gammaN 6) (v : HomogeneousPoly n) :
    rho6 n χ (gammaSixEquiv p) v = ambRep n p.1 v := by
  change rationalCoefficientComponent n χ (iotaQ (gammaSixEquiv p)) v = _
  rw [iotaQ_gammaSix, coeff_mapGL]

theorem rho6_gammaSix_symm (g : Γ6) (v : HomogeneousPoly n) :
    rho6 n χ g v = ambRep n (gammaSixEquiv.symm g).1 v := by
  have := rho6_gammaSix n χ (gammaSixEquiv.symm g) v
  rwa [MulEquiv.apply_symm_apply] at this

/-- Transport of the coefficient comparison along `Γ(6) ≃ principalSix`. -/
theorem hT6 (g : Γ6) (v : (gammaNRepAll 6 n)) :
    (LinearMap.id : gammaNRepAll 6 n →ₗ[ℂ] Rep.of (rho6 n χ))
      ((gammaNRepAll 6 n).ρ ((gammaSixEquiv.symm : Γ6 ≃* gammaN 6).toMonoidHom g) v) =
    (Rep.of (rho6 n χ)).ρ g ((LinearMap.id : gammaNRepAll 6 n →ₗ[ℂ] Rep.of (rho6 n χ)) v) := by
  exact (rho6_gammaSix_symm n χ g v).symm

end Coefficients

end TernaryPeriodPolynomials.Argument.GammaNStokes
