module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.SlantEval
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.CuspCalib
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ShuffleBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SlantExt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SumReduction

@[expose] public section


/-!
# The letter lift of the flag group `Stab (flagAt h w)` into the line group `gammaNQAt 6 h`

Formalized by Claude Sonnet 5.5.

For the stabilizer `B` of the flag `flagAt h w` and a Levi element `σ ∈ Γ(6)` fixing `w`, `flagLift h w σ hσ : LetterLift (pairModelOfSplitting (lineFaceSplitting 6 h)) B σ`:
the injective homomorphism `B → gammaNQAt 6 h` is the inverse of `lineEmb h` on the stabilizer of the line, the `N`-letters are the radical elements and the `L`-letter is `s σ` (the `lineEmb_inl_mem_stab`,
`lineEmb_split_mem_stab`).
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

variable (h : SL(3, ℤ)) (w : Prim2)

theorem stab_flagAt_le_range : MulAction.stabilizer Γ6 (flagAt h w) ≤ (lineEmb h).range := by
  intro g hg
  rw [lineEmb_range]
  have := stab_flagAt_fixes_line h w ⟨g, hg⟩
  exact this

/-- The inverse of `lineEmb h` on the stabilizer of the flag. -/
def flagIota : ↥(MulAction.stabilizer Γ6 (flagAt h w)) →* ↥(gammaNQAt 6 h) :=
  (MonoidHom.ofInjective (lineEmb_injective h)).symm.toMonoidHom.comp (Subgroup.inclusion (stab_flagAt_le_range h w))

theorem lineEmb_flagIota (b : ↥(MulAction.stabilizer Γ6 (flagAt h w))) : lineEmb h (flagIota h w b) = (b : Γ6) := by
  have := (MonoidHom.ofInjective (lineEmb_injective h)).apply_symm_apply ⟨(b : Γ6), stab_flagAt_le_range h w b.2⟩
  exact congrArg Subtype.val this

theorem flagIota_injective : Function.Injective (flagIota h w) := by
  intro a b hab
  apply Subtype.ext
  rw [← lineEmb_flagIota h w a, ← lineEmb_flagIota h w b, hab]

variable (σ : Gamma 6) (hσ : ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ w.1 = w.1)

/-- **The letter lift of the flag group.** -/
def flagLift : LetterLift (pairModelOfSplitting (lineFaceSplitting 6 h)) ↥(MulAction.stabilizer Γ6 (flagAt h w)) σ where
  ι := flagIota h w
  inj := flagIota_injective h w
  nlB a := ⟨lineEmb h ((lineFaceExt 6 h).inl (Additive.toMul a)), lineEmb_inl_mem_stab h w _⟩
  llB := ⟨lineEmb h ((lineFaceSplitting 6 h) σ), lineEmb_split_mem_stab h w σ hσ⟩
  hnl a := by
    apply lineEmb_injective h
    rw [lineEmb_flagIota, pm_nl]
  hll := by
    apply lineEmb_injective h
    rw [lineEmb_flagIota, pm_ll]

section Test

variable (hh : LineType (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h))
  (hN : ∀ s, conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h s ∈ gammaN 6)
  (φ : Gamma 6 → ℚ) (hφ : ∀ a b, φ (a * b) = φ a + φ b)

theorem gammaOfM_nl (r : RadicalLattice) :
    gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN ⟨_, lineEmb_inl_mem_stab h w r⟩ = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact (letter_inl h w r hh).1

theorem gammaOfM_ll :
    gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN ⟨_, lineEmb_split_mem_stab h w σ hσ⟩ = σ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (letter_split h w σ hσ hh).1

theorem beta_nl (r r' : RadicalLattice) :
    (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).beta ⟨_, lineEmb_inl_mem_stab h w r⟩
      ⟨_, lineEmb_inl_mem_stab h w r'⟩ =
      36 * (((Multiplicative.toAdd r).1 * (Multiplicative.toAdd r').2 - (Multiplicative.toAdd r).2 * (Multiplicative.toAdd r').1 : ℤ) : ℚ) := by
  obtain ⟨hA', -⟩ := letter_inl h w r' hh
  obtain ⟨-, hv⟩ := letter_inl h w r hh
  obtain ⟨-, hv'⟩ := letter_inl h w r' hh
  unfold LineData.beta
  rw [hA', Matrix.vecMul_one, hv, hv']
  simp only [omega]
  push_cast
  ring

theorem gammaOfM_llB :
    gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN (flagLift h w σ hσ).llB = σ :=
  gammaOfM_ll h w σ hσ hh hN

theorem beta_nlB (a b : Additive RadicalLattice) :
    (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).beta ((flagLift h w σ hσ).nlB a) ((flagLift h w σ hσ).nlB b) =
      36 * (((Multiplicative.toAdd (Additive.toMul a)).1 * (Multiplicative.toAdd (Additive.toMul b)).2 -
        (Multiplicative.toAdd (Additive.toMul a)).2 * (Multiplicative.toAdd (Additive.toMul b)).1 : ℤ) : ℚ) :=
  beta_nl h w hh _ _

include hφ in
theorem chainEval_nuSh_test (hdet : radDet (splitRadicalInput (lineFaceSplitting 6 h) σ) = 1) :
    chainEval ((flagLift h w σ hσ).nuSh (Additive.ofMul latE1) (Additive.ofMul latE2))
        (cupCochain (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh
          (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s))) = 72 * φ σ := by
  have hφ1 : φ 1 = 0 := by
    have := hφ 1 1
    rw [mul_one] at this
    linarith
  have key := (flagLift h w σ hσ).chainEval_nuSh_cup (Additive.ofMul latE1) (Additive.ofMul latE2)
    (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s))
    (matLineData (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh).beta
    (fun a => by
      show φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN
        ⟨_, lineEmb_inl_mem_stab h w (Additive.toMul a)⟩) = 0
      rw [gammaOfM_nl, hφ1])
  refine key.trans ?_
  rw [gammaOfM_llB, beta_nlB, beta_nlB]
  have hd : (((Multiplicative.toAdd (splitRadicalInput (lineFaceSplitting 6 h) σ latE1)).1 *
      (Multiplicative.toAdd (splitRadicalInput (lineFaceSplitting 6 h) σ latE2)).2 -
      (Multiplicative.toAdd (splitRadicalInput (lineFaceSplitting 6 h) σ latE1)).2 *
        (Multiplicative.toAdd (splitRadicalInput (lineFaceSplitting 6 h) σ latE2)).1 : ℤ) : ℚ) = 1 := by
    have := hdet
    unfold radDet at this
    exact_mod_cast this
  have e1 : Additive.toMul ((pmE (lineFaceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE1)) =
      splitRadicalInput (lineFaceSplitting 6 h) σ latE1 := rfl
  have e2 : Additive.toMul ((pmE (lineFaceSplitting 6 h)).ψ σ⁻¹ (Additive.ofMul latE2)) =
      splitRadicalInput (lineFaceSplitting 6 h) σ latE2 := rfl
  rw [e1, e2]
  push_cast at hd ⊢
  linear_combination (72 * φ σ) * hd

end Test

section Final

theorem gammaOfM_additive (hh : LineType (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h))
    (hN : ∀ s, conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h s ∈ gammaN 6) (φ : Gamma 6 → ℚ)
    (hφ : ∀ a b, φ (a * b) = φ a + φ b) (a b : ↥(MulAction.stabilizer Γ6 (flagAt h w))) :
    (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s)) (a * b) =
      (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s)) a +
        (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s)) b := by
  show φ (gammaOfM _ hh hN (a * b)) = φ (gammaOfM _ hh hN a) + φ (gammaOfM _ hh hN b)
  rw [gammaOfM_mul, hφ]

/-- **The value of `λ_F` on a `(≥1)`-cocycle of the flag group**: `λ_F[Θ] = -6 ⟨Θ, Sh₁ σ⟩` (calibrated on the line cup class `u_φ ∪ β`, `λ = -432 φ(σ)`, `⟨u_φ ∪ β, Sh₁σ⟩ = 72 φ(σ)`). -/
theorem flagLam_eq_slant (hσpos : σ = posParSL w.1) (hdet : ∀ A, radDet (splitRadicalInput (lineFaceSplitting 6 h) A) = 1)
    (hφσ : ∃ φ : Gamma 6 → ℚ, (∀ a b, φ (a * b) = φ a + φ b) ∧ φ σ ≠ 0)
    (Θ : (Fin 3 → ↥(MulAction.stabilizer Γ6 (flagAt h w))) → ℚ) (hΘ : dThree Θ = 0)
    (hz : ∀ a b c, Θ ![(flagLift h w σ hσ).nlB a, (flagLift h w σ hσ).nlB b, (flagLift h w σ hσ).nlB c] = 0) :
    flagLam (flagAt h w) (clsRes (MulAction.stabilizer Γ6 (flagAt h w)) Θ hΘ) =
      -6 * chainEval ((flagLift h w σ hσ).nuSh (Additive.ofMul latE1) (Additive.ofMul latE2)) Θ := by
  obtain ⟨φ, hφ, hφσ⟩ := hφσ
  have hh := lineType_flagAt h w
  have hN := gammaN_flagAt h w
  have hT : dThree (cupCochain (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh
      (fun s => φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN s))) = 0 :=
    cupCochain_cocycle _ hh _ (gammaOfM_additive h w hh hN φ hφ)
  have hcal := flagLam_calib h w φ hφ hh hN hT
  rw [flagLam_clsRes] at hcal ⊢
  have hφ1 : φ 1 = 0 := by
    have := hφ 1 1
    rw [mul_one] at this
    linarith
  obtain ⟨m₀, hm₀⟩ := hmu_of_det (lineFaceSplitting 6 h) hdet σ
  have := (flagLift h w σ hσ).lam_eq_torus (flagStabDataOf (flagAt h w)) (Additive.ofMul latE1) (Additive.ofMul latE2) m₀ hm₀
    _ hT (fun a b c => by
      show φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 (flagAt h w)) h) hh hN
        ⟨_, lineEmb_inl_mem_stab h w (Additive.toMul a)⟩) * _ = 0
      rw [gammaOfM_nl, hφ1, zero_mul])
    72 (-432) (φ σ) (by norm_num) hφσ (chainEval_nuSh_test h w σ hσ hh hN φ hφ (hdet σ))
    (by rw [hcal, hσpos]) Θ hΘ hz
  rw [this]
  norm_num

end Final

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
