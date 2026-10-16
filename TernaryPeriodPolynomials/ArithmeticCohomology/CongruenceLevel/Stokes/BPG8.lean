module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG7

@[expose] public section


/-!
# Plane geometry package, part 8: calibration of `λ_F` on the plane test cocycle (G-c)

Formalized by Claude Sonnet 5.5.

For a frame `h`, a primitive vector `w` and an additive `ψ` on `Γ(6)`, `λ_{pflag h w}` of the class of the plane test cocycle `planeTestE h ψ`, pulled back to the stabilizer of `pflag h w` along `stabToE`, equals `432 ψ(posPar w)`.
-/

open scoped MatrixGroups
open CongruenceSubgroup CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

/-- The plane test cocycle restricted to the stabilizer of `pflag h w`. -/
def pTestCochain (h : SL(3, ℤ)) (w : Prim2) (ψ : Gamma 6 → ℚ) :
    (Fin 3 → ↥(MulAction.stabilizer Γ6 (pflag h w))) → ℚ :=
  fun x => planeTestE h ψ (stabToE h (pflag h w) (flagPlaneOf_pflag h w) ∘ x)

theorem pTestCochain_cocycle (h : SL(3, ℤ)) (w : Prim2) (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) :
    dThree (pTestCochain h w ψ) = 0 :=
  dThree_comp _ _ (planeTestE_cocycle h ψ hψ)

theorem pTestCochain_eq (h : SL(3, ℤ)) (w : Prim2) (ψ : Gamma 6 → ℚ) :
    pTestCochain h w ψ = cupCochain (pMh h w) (pMh_lineType h w)
      (fun s => planeTestU h ψ (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s)) := rfl

/-- **Calibration of `λ_F` on the plane test cocycle (G-c).** -/
theorem plane_calibration (h : SL(3, ℤ)) (w : Prim2) (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) :
    flagLam (pflag h w) (clsRes (MulAction.stabilizer Γ6 (pflag h w)) (pTestCochain h w ψ)
      (pTestCochain_cocycle h w ψ hψ)) = 432 * ψ (posParSL w.1) := by
  have hT' : dThree (cupCochain (pMh h w) (pMh_lineType h w)
      (fun s => planeTestU h ψ (stabToE h (pflag h w) (flagPlaneOf_pflag h w) s))) = 0 :=
    pTestCochain_eq h w ψ ▸ pTestCochain_cocycle h w ψ hψ
  rw [clsRes_congr _ (pTestCochain_eq h w ψ) (pTestCochain_cocycle h w ψ hψ) hT']
  rw [flagLam_cup_value_tau (pflag h w) (qBD w * h) rfl (pMh h w) (pMh_lineType h w) (tau (qBD w))
    (tau_mem_lineBorel_of_planeBorel (qBD_mem w)) (pMh_rel h w) (-ψ (posParSL w.1) / 6) _ (pMh_u h w ψ hψ) hT',
    tau_qBD_00]
  push_cast
  ring

end TernaryPeriodPolynomials.Argument.GammaNStokes
