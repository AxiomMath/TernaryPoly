module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Cut
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.EvalInst
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine5
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane4
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Uniform

@[expose] public section


/-!
# The uniform face factorisation `FaceFactorisation6U` from the fibre-integration identities with the constants `κ_L = -3`, `κ_P = +3`

Formalized by Claude Sonnet 5.5.

`faceFactorisation6U_of_M3At`: if `M3LineAt flagEval (fun _ => -3)` and `M3PlaneAt flagEval (fun _ => 3)` (the values computed by `lineSum_final`, `planeSum_final`) then
`lineFacePairM = c · can6` and `planeFacePairM = -c · can6P` with the single nonzero constant `c = -3 Λ`, `Λ` the universal coefficient; the relative sign `-1` of the plane faces is `κ_P = -κ_L`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

theorem faceFactorisation6U_of_M3At (h3L : M3LineAt flagEval (fun _ => -3)) (h3P : M3PlaneAt flagEval (fun _ => 3)) :
    FaceFactorisation6U := by
  obtain ⟨Λ, hΛ0, h⟩ := factorisation_of_M3At flagEval ConjFrames.default (lineImageSumZero ConjFrames.default)
    (planeImageSumZero ConjFrames.default) (fun _ => -3) (fun _ => 3) h3L h3P
  refine ⟨((Λ * (-3) : ℚ) : ℂ), ?_, fun V _ _ _ _ _ ρ => ?_⟩
  · have : (Λ * (-3) : ℚ) ≠ 0 := mul_ne_zero hΛ0 (by norm_num)
    exact_mod_cast this
  · obtain ⟨hl, hp⟩ := h V ρ
    refine ⟨hl, fun i x y => ?_⟩
    rw [hp i x y]
    congr 1
    push_cast
    ring

theorem M3LineC_of_At (E : FlagEval) (h : M3LineAt E (fun _ => -3)) : M3LineC E :=
  ⟨fun _ => -3, fun _ => by norm_num, h⟩

theorem M3PlaneC_of_At (E : FlagEval) (h : M3PlaneAt E (fun _ => 3)) : M3PlaneC E :=
  ⟨fun _ => 3, fun _ => by norm_num, h⟩

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
