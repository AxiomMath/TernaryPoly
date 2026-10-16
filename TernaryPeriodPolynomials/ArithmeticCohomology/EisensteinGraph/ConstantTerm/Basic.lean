module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.EisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.SourceStandard

@[expose] public section


/-!
# The constant-term defect of the global Eisenstein cocycle

Fix a plane source cocycle `c` in degree `n ≥ 4`, let `E c` be its global Eisenstein cocycle
and `J c` its standard continuation. On the plane stratum, the restriction of `E c` and the
evaluation of `c` differ by the flag cochain `(x, q) ↦ (E c - c)(x)(q⁻¹)`; on the line stratum,
the restriction of `E c` and the evaluation of `J c` differ by `(x, q) ↦ (E c - J c)(x)(q⁻¹)`.
This file names these defects and the real translation families along the unipotent radical
used to show that they are coboundaries.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

variable {n : ℕ}

/-- The source cocycle evaluated on each stratum: `c` on the plane stratum, its standard
continuation `J c` on the line stratum. -/
def sideSource (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) : (side : Side) → SourceSpace.sourceCocycles D side
  | .plane => c
  | .line => EndpointSourceStandard.sourceStandard D large hol c

/-- The Eisenstein value `E c(y)(g)` at real vertices. -/
def eisensteinValue (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (g : AdelicGL) :
    HomogeneousPoly n :=
  GlobalEisensteinCocycle.sourceValueAtReal D hol c y g

/-- The defect `(E c - c_side)(y)(g)`, where `c_side` is `c` or `J c`. -/
def defectValue (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (side : Side) (y : Fin 3 → RealGL3)
    (g : AdelicGL) : HomogeneousPoly n :=
  eisensteinValue D hol c y g - (sideSource large D hol c side).val y g

/-- The flag 2-cochain measuring the failure of the restriction formula on one stratum. -/
def defectCochain (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (side : Side) :
    cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) side) 2 :=
  (restrictionCocycle n D.chi side
      (EndpointEisensteinCocycle.globalCocycle D hol large c)).val -
    (SourceSpace.evaluatedSource D side (sideSource large D hol c side)).val

/-- The unipotent radical of the standard parabolic of each side. -/
def sideUnipotent (side : Side) {R : Type*} [CommRing R] (s t : R) : GL3 R :=
  match side with
  | .plane => planeUnipotent s t
  | .line => lineUnipotent s t

/-- The real translation family of the defect at the rational flag `q`, along the radical of
the standard parabolic scaled by `K`: `r ↦ (E c - c_side)(y)(u(K r) q⁻¹)`. -/
def defectFamily (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (c : SourceSpace.sourceCocycles D .plane) (side : Side) (q : RationalGL3) (K : ℕ)
    (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) : HomogeneousPoly n :=
  defectValue large D hol c side (GlobalEisensteinCocycle.realVertices y)
    (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) * rationalGroup q⁻¹)

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
