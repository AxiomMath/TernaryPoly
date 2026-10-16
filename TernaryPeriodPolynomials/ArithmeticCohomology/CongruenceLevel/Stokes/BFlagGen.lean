module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine5
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BHeisTau
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BTau

@[expose] public section


/-!
# The value of `λ_F` on cup classes relative to an arbitrary standard datum, and the plane version

Formalized by Claude Sonnet 5.5.

`flagLam_gen`: the evaluation functional `λ_F` on `u ∪ β_{M_h}`, relative to a standard datum `D'` of the frame homomorphism and a coordinate `b'` with `b' ∪ β_{D'}` of value `κ` on the Heisenberg cycle.
`flagLam_cup_value_tau`: the plane version, for the datum of the image of the frame homomorphism under the involution `tau`.
-/

open scoped MatrixGroups
open CategoryTheory MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3 TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.ConvergenceC4

theorem flagLam_gen (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (D' : LineData ↥(MulAction.stabilizer Γ6 F))
    (b' : ↥(MulAction.stabilizer Γ6 F) → ℤ) (hb' : ∀ x y, b' (x * y) = b' x + b' y)
    (Mg Mh : ↥(MulAction.stabilizer Γ6 F) →* SL(3, ℤ)) (hgL : LineType Mg) (hh : LineType Mh)
    (hD : ∀ s, (matLineData Mg hgL).A s = D'.A s ∧ (matLineData Mg hgL).v s = D'.v s)
    (q : SL(3, ℤ)) (hq : q ∈ lineBorel)
    (hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * (Mh s : Matrix (Fin 3) (Fin 3) ℤ) =
      (Mg s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ))
    (κ : ℚ) (hval : chainEval (flagDataAt F g hg).z (fun x : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
      (b' (x 0) : ℚ) * D'.beta (x 1) (x 2)) = κ)
    (c : ℚ) (u : ↥(MulAction.stabilizer Γ6 F) → ℚ) (hu : ∀ s, u s = c * b' s)
    (hT : dThree (cupCochain Mh hh u) = 0) :
    flagLam F (clsRes (MulAction.stabilizer Γ6 F) (cupCochain Mh hh u) hT) = ((q : Matrix (Fin 3) (Fin 3) ℤ) 0 0 : ℚ) * (c * κ) := by
  rw [flagLam_frame F g hg]
  simp only [LinearMap.comp_apply, clsRes, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [FlagCohomDatum.lam_cocycle]
  exact local_value_gen D' b' hb' Mg Mh hgL hh hD q hq hrel (flagDataAt F g hg).z (flagDataAt F g hg).isCycle κ hval c u hu

end TernaryPeriodPolynomials.Argument.GammaNStokes
