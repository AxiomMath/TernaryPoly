module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenIdent
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.LineSetup
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.PlaneData

@[expose] public section


/-!
# Step 2 for the plane faces: `OrbitIdentPlane`

Formalized by Claude Sonnet 5.5.

**`orbitIdentPlane`**: for `3 ≤ M`, `6 ∣ M`, the level-6 canonical pairing `can6P` of the orbit components `planeTermX`, `planeTermY` of the restrictions to the plane group `K_i = Γ(6) ∩ P_i⁻¹ P P_i` of induced
classes equals the level-`M` canonical pairing `canAtClassP` at the frame `P_i · u_O` of the restrictions of the level-`M` classes, with constant exactly `1`.  The geometric data is the conjugation
`p ↦ u p u⁻¹` (`plane_hmem`, `plane_hback`, `plane_hinl`, `plane_hspl` of `PlaneData`), the rest is `orbit_ident_gen`.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section Main

variable (M n : ℕ) [NeZero M]

/-- **Step 2 for the plane faces (`OrbitIdentPlane`), with the constant exactly `1`.** -/
theorem orbitIdentPlane (hM : 3 ≤ M) (h6 : 6 ∣ M) : OrbitIdentPlane M n hM := by
  intro c₀ hz c₀' hz' cV cVd hcV hcVd i o
  have hu : ((uOPlane M i o : ↥(gammaN 6)) : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o := Quotient.out_eq' _
  exact orbit_ident_gen hM h6 (gammaNPAt 6 (planeFaceRepr i))
    (gammaNPAt M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp) (fun _ hp => gammaNPAt_le_gammaN M _ hp)
    (uOPlane M i o)
    (fun s hs => plane_hmem (planeFaceRepr i) ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)) _ s.2 s.1.2 hs)
    (fun p => plane_hback (planeFaceRepr i) ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)) h6 _ p.2)
    (faceExt 6 (planeFaceRepr i)) (faceSplitting 6 (planeFaceRepr i)) (planeFaceRadicalInput_det 6 (planeFaceRepr i))
    (faceExt M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (faceSplitting M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (planeFaceRadicalInput_det M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))))
    (plane_hinl (planeFaceRepr i) ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)) h6)
    (plane_hspl (planeFaceRepr i) ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)) (gamma_le_of_dvd h6))
    (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) o hu c₀ cV hcV c₀' cVd hcVd
    (res_radical_of_planeMixedAt (planeTermX c₀ hz cV hcV i o)) (planeEdge_mem_cuspidal (planeTermX c₀ hz cV hcV i o))
    (res_radical_of_planeMixedAt (planeTermY c₀' hz' cVd hcVd i o)) (planeEdge_mem_cuspidal (planeTermY c₀' hz' cVd hcVd i o))
    (res_radical_of_planeMixedAt (planeClass M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀ hz))
    (planeEdge_mem_cuspidal (planeClass M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀ hz))
    (res_radical_of_planeMixedAt (planeClassDual M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀' hz'))
    (planeEdge_mem_cuspidal (planeClassDual M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀' hz'))

end Main

end TernaryPeriodPolynomials.Argument.RadicalInduction
