module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.SlantEval
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SlantExt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SumReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG9
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG8
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG4

@[expose] public section


/-!
# The letter lift of a plane flag group into the plane group `gammaNPAt 6 h`, and the calibration `λ = -6 ⟨·, Sh₁ σ⟩`

Formalized by Claude Sonnet 5.5.

The plane twin of `FlagLift`: `planeLift h w σ hσ : LetterLift (pairModelOfSplitting (faceSplitting 6 h)) (Stab (pflag h w)) σ`; `chainEval_nuSh_ptest`: the plane test cocycle has `⟨ξ_ψ, Sh₁σ⟩ = -72 ψ σ`
(the `planeE_inl_v`: `v(inl r) = (-6 r₂, -6 r₁)`); `planeLam_eq_slant`: `λ_{F}[Θ] = -6 ⟨Θ, Sh₁σ⟩` for `(≥ 1)`-cocycles of the plane flag group (`plane_calibration`: `λ = 432 ψ σ`).
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.SeedC3S4c

variable (h : SL(3, ℤ)) (w : Prim2)

theorem planeEmb_stabToE (s : ↥(MulAction.stabilizer Γ6 (pflag h w))) :
    planeEmb h (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s) = (s : Γ6) := by
  have := (planeStabEquiv h).apply_symm_apply (Subgroup.inclusion (by
    have := stab_flag_le_stab_pt flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant (pflag h w)
    rw [flagPlaneOf_pflag h w] at this
    exact this) s)
  exact congrArg Subtype.val this

theorem stabToE_injective : Function.Injective (stabToE h (pflag h w) (flagPlaneOf_pflag h w)) := by
  intro a b hab
  apply Subtype.ext
  rw [← planeEmb_stabToE h w a, ← planeEmb_stabToE h w b, hab]

variable (σ : Gamma 6) (hσ : σ.1 = posPar w.1)

/-- **The letter lift of the plane flag group.** -/
def planeLift : LetterLift (pairModelOfSplitting (faceSplitting 6 h)) ↥(MulAction.stabilizer Γ6 (pflag h w)) σ where
  ι := stabToE h (pflag h w) (flagPlaneOf_pflag h w)
  inj := stabToE_injective h w
  nlB a := ⟨planeEmb h ((faceExt 6 h).inl (Additive.toMul a)), pflag_stab_nl h w _⟩
  llB := ⟨planeEmb h ((faceSplitting 6 h) σ), pflag_stab_ll h w σ hσ⟩
  hnl a := by
    apply planeEmb_injective h
    rw [planeEmb_stabToE, pm_nl]
  hll := by
    apply planeEmb_injective h
    rw [planeEmb_stabToE, pm_ll]

section PTest

variable (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b)

theorem stabToE_nlB (a : Additive RadicalLattice) :
    stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB a) = (faceExt 6 h).inl (Additive.toMul a) :=
  ((planeLift h w σ hσ).hnl a).trans (pm_nl _ a)

theorem stabToE_llB :
    stabToE h (pflag h w) (flagPlaneOf_pflag h w) (planeLift h w σ hσ).llB = faceSplitting 6 h σ :=
  (planeLift h w σ hσ).hll.trans (pm_ll _ σ)

omit hσ in
theorem ptest_beta_inl (r r' : RadicalLattice) :
    (matLineData (planeEHom h) (planeEHom_lineType h)).beta ((faceExt 6 h).inl r) ((faceExt 6 h).inl r') =
      -36 * (((Multiplicative.toAdd r).1 * (Multiplicative.toAdd r').2 - (Multiplicative.toAdd r).2 * (Multiplicative.toAdd r').1 : ℤ) : ℚ) := by
  unfold LineData.beta
  rw [planeE_inl_A, Matrix.vecMul_one, planeE_inl_v, planeE_inl_v]
  simp only [omega]
  push_cast
  ring

include hψ in
theorem chainEval_nuSh_ptest (hdet : radDet (splitRadicalInput (faceSplitting 6 h) σ) = 1) :
    chainEval ((planeLift h w σ hσ).nuSh (Additive.ofMul latE1) (Additive.ofMul latE2)) (pTestCochain h w ψ) = -72 * ψ σ := by
  have hψ1 : ψ 1 = 0 := by
    have := hψ 1 1
    rw [mul_one] at this
    linarith
  have key := (planeLift h w σ hσ).chainEval_nuSh_cup (Additive.ofMul latE1) (Additive.ofMul latE2)
    (fun b => planeTestU h ψ (stabToE h (pflag h w) (flagPlaneOf_pflag h w) b))
    (fun a b => (matLineData (planeEHom h) (planeEHom_lineType h)).beta
      (stabToE h (pflag h w) (flagPlaneOf_pflag h w) a) (stabToE h (pflag h w) (flagPlaneOf_pflag h w) b))
    (fun a => by
      show ψ ((faceExt 6 h).rightHom (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB a))) = 0
      rw [stabToE_nlB, (faceExt 6 h).rightHom_inl, hψ1])
  refine key.trans ?_
  have e1 : Additive.toMul ((pairModelOfSplitting (faceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE1)) =
      splitRadicalInput (faceSplitting 6 h) σ latE1 := rfl
  have e2 : Additive.toMul ((pairModelOfSplitting (faceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE2)) =
      splitRadicalInput (faceSplitting 6 h) σ latE2 := rfl
  have hd : (((Multiplicative.toAdd (splitRadicalInput (faceSplitting 6 h) σ latE1)).1 *
      (Multiplicative.toAdd (splitRadicalInput (faceSplitting 6 h) σ latE2)).2 -
      (Multiplicative.toAdd (splitRadicalInput (faceSplitting 6 h) σ latE1)).2 *
        (Multiplicative.toAdd (splitRadicalInput (faceSplitting 6 h) σ latE2)).1 : ℤ) : ℚ) = 1 := by
    have := hdet
    unfold radDet at this
    exact_mod_cast this
  show ψ ((faceExt 6 h).rightHom (stabToE h (pflag h w) (flagPlaneOf_pflag h w) (planeLift h w σ hσ).llB)) *
    ((matLineData (planeEHom h) (planeEHom_lineType h)).beta
      (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB ((pairModelOfSplitting (faceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE1))))
      (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB ((pairModelOfSplitting (faceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE2)))) -
     (matLineData (planeEHom h) (planeEHom_lineType h)).beta
      (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB ((pairModelOfSplitting (faceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE2))))
      (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB ((pairModelOfSplitting (faceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE1))))) = _
  simp only [stabToE_nlB]
  rw [stabToE_llB, (faceSplitting 6 h).rightHom_splitting, ptest_beta_inl, ptest_beta_inl, e1, e2]
  push_cast at hd ⊢
  linear_combination (-72 * ψ σ) * hd

end PTest

section PFinal

/-- **The value of `λ_F` on a `(≥1)`-cocycle of a plane flag group**: `λ_F[Θ] = -6 ⟨Θ, Sh₁ σ⟩`
(`plane_calibration`: `λ = 432 ψ σ` on the test cocycle, `⟨ξ_ψ, Sh₁σ⟩ = -72 ψ σ`). -/
theorem planeLam_eq_slant (hdet : ∀ A, radDet (splitRadicalInput (faceSplitting 6 h) A) = 1)
    (hψσ : ∃ ψ : Gamma 6 → ℚ, (∀ a b, ψ (a * b) = ψ a + ψ b) ∧ ψ σ ≠ 0)
    (Θ : (Fin 3 → ↥(MulAction.stabilizer Γ6 (pflag h w))) → ℚ) (hΘ : dThree Θ = 0)
    (hz : ∀ a b c, Θ ![(planeLift h w σ hσ).nlB a, (planeLift h w σ hσ).nlB b, (planeLift h w σ hσ).nlB c] = 0) :
    flagLam (pflag h w) (clsRes (MulAction.stabilizer Γ6 (pflag h w)) Θ hΘ) =
      -6 * chainEval ((planeLift h w σ hσ).nuSh (Additive.ofMul latE1) (Additive.ofMul latE2)) Θ := by
  obtain ⟨ψ, hψ, hψσ⟩ := hψσ
  have hcal := plane_calibration h w ψ hψ
  rw [flagLam_clsRes] at hcal ⊢
  have hψ1 : ψ 1 = 0 := by
    have := hψ 1 1
    rw [mul_one] at this
    linarith
  have hσpos : σ = posParSL w.1 := Subtype.ext (by rw [hσ]; rfl)
  obtain ⟨m₀, hm₀⟩ := hmu_of_det (faceSplitting 6 h) hdet σ
  have := (planeLift h w σ hσ).lam_eq_torus (flagStabDataOf (pflag h w)) (Additive.ofMul latE1) (Additive.ofMul latE2) m₀ hm₀
    _ (pTestCochain_cocycle h w ψ hψ) (fun a b c => by
      show ψ ((faceExt 6 h).rightHom (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ((planeLift h w σ hσ).nlB a))) * _ = 0
      rw [stabToE_nlB, (faceExt 6 h).rightHom_inl, hψ1, zero_mul])
    (-72) 432 (ψ σ) (by norm_num) hψσ (chainEval_nuSh_ptest h w σ hσ ψ hψ (hdet σ))
    (by rw [hcal, hσpos]) Θ hΘ hz
  rw [this]
  norm_num

end PFinal

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
