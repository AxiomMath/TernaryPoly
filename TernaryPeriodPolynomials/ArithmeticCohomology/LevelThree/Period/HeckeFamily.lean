module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeSum

@[expose] public section


/-!
# Hecke equivariance for coset families of constant determinant

A `HeckeH1.RightCosets` datum for `Γ₁(3)` in `GL₂(ℚ)` whose representatives all have the same
determinant `D > 0` and which is compatible with the real embedding gives a
`LevelThreeHeckeSum.CosetFamily` (`toCosetFamily`), hence an operator
`f ↦ ∑_j f ∣[k] α_j` on `S_k(Γ₁(3))` (`CosetFamily.sumOp`). Then
`periodMap_hecke_sumOp`: the period class of `D^{-e} ∑_j f ∣[m+2] α_j` is the Hecke image
(`LevelThreeHeckeH1.crossedHecke`) of the period class of `f`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix UpperHalfPlane
open scoped Manifold ModularForm MatrixGroups
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHecke
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeFamily

variable {embed : core →* GL (Fin 2) ℚ} (Sx : RightCosets embed)
  (hφ : ∀ k, toReal (embed k) = coreReal k)
  (hpos : ∀ j, 0 < (((Sx.rep j).det : ℚˣ) : ℚ))

/-- The coset family attached to right cosets of `Γ₁(3)`. -/
def toCosetFamily : CosetFamily Sx.index where
  rep := Sx.rep
  det_pos := hpos
  transition := by
    intro g hg
    obtain ⟨k, rfl⟩ := exists_core_of_mem g hg
    refine ⟨(Sx.nextEquiv k).symm, fun i => ?_⟩
    have hj : Sx.next k ((Sx.nextEquiv k).symm i) = i := (Sx.nextEquiv k).apply_symm_apply i
    refine ⟨coreSL (Sx.delta k ((Sx.nextEquiv k).symm i)), coreSL_mem _, ?_⟩
    have hs := Sx.delta_spec k ((Sx.nextEquiv k).symm i)
    have hs' := congrArg toReal hs
    rw [map_mul, map_mul, map_inv, hφ, hφ, hj] at hs'
    rw [mapGL_coreSL, mapGL_coreSL]
    change toReal (Sx.rep ((Sx.nextEquiv k).symm i)) * coreReal k =
      coreReal (Sx.delta k ((Sx.nextEquiv k).symm i)) * toReal (Sx.rep i)
    rw [hs']
    group

theorem toCosetFamily_rep (j : Sx.index) : (toCosetFamily Sx hφ hpos).rep j = Sx.rep j := rfl

variable (m : ℕ) (e : ℤ) {D : ℝ}
  (hD : ∀ j, (toReal (Sx.rep j)).val.det = D)

include hD in
/-- The Hecke image of the period class of `f` is the period class of
`D^{-e} ∑_j f ∣[m+2] α_j`. -/
theorem periodMap_hecke_sumOp (hemb : Function.Injective embed) (f : S m) :
    crossedHecke Sx (rationalRho m e) (coreRep m e) (compat_of m e hφ) hemb
        (levelThreePeriodMap m e f) =
      levelThreePeriodMap m e
        (((D : ℂ) ^ (-e)) • ((toCosetFamily Sx hφ hpos).sumOp ((m : ℤ) + 2) f)) := by
  apply periodMap_hecke m e Sx hemb hφ hpos
  funext τ
  simp only [FunLike.coe_smul, CosetFamily.sumOp_apply, CosetFamily.sumFun, toCosetFamily_rep,
    hD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodHeckeFamily
