module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerResolution
public import TernaryPeriodPolynomials.Building.FreeResolution.Main

@[expose] public section


/-!
# `H⁴` of the boundary stabilizers vanishes

The principal congruence subgroup of level three has a free resolution of `ℂ` of length three (the
well-rounded retract), and it has finite index in the arithmetic level. Restricting the resolution
to the stabilizer of a point of any `GL₃(ℚ)`-set gives `H⁴ = 0` for every such stabilizer, in
particular for the stabilizers of the representative flags of the boundary trace; and every twisted
cup product of a line and a plane two-cocycle has a vertex primitive on lines.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing

open TernaryPeriodPolynomials.TopVanishing
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TracePairing
open TernaryPeriodPolynomials.BoundaryDuality.FlagShapiro
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerResolution

/-- **`H⁴` of every point stabilizer in the level vanishes.** -/
theorem topVanishing_pointStabilizer_unconditional {Y : Type} [MulAction RationalGL3 Y] (y : Y) :
    IsTopVanishing (pointStabilizer y) :=
  topVanishing_pointStabilizer principalLevel_relIndex_ne_zero
    FreeResolution.principalFreeResolution y

/-- `H⁴` of the stabilizer of a point, in the form `rationalLevel ⊓ stabilizer`. -/
theorem topVanishing_levelStabilizer {Y : Type} [MulAction RationalGL3 Y] (y : Y) :
    IsTopVanishing (rationalLevel ⊓ MulAction.stabilizer RationalGL3 y) :=
  topVanishing_pointStabilizer_unconditional y

/-- **Vertex primitives on lines, unconditionally.** -/
theorem lineCupExact {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ) :
    LineCupExact T :=
  lineCupExact_of_freeResolution T principalLevel_relIndex_ne_zero
    FreeResolution.principalFreeResolution

end TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing
