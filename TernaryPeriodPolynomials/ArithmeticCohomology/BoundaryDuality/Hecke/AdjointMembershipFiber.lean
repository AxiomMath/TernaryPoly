module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipEngine
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction

@[expose] public section


/-!
# The `U`-primitives from vanishing radical restriction

`FiberExact.exists_omegaU` and `FiberExact.exists_thetaU` need the vanishing of the homogeneous
classes of the restrictions `x ↦ z(x)(Lf)` and `x ↦ y(φ x)(dualFlag Lf)` to a lattice `U` in the
stabilizer of `Lf`. Both are pullbacks (along the identity and along `φ`) of the two-cocycle
`x ↦ z(x)(Lf)` of the stabilizer, respectively `x ↦ y(x)(F)` of the stabilizer of the dual plane
`F`. By `HeckeAdjointMembershipEngine`, they are exact as soon as the group cohomology class of the
cocycle of the stabilizer has vanishing restriction along an injective homomorphism from a lattice
whose image contains `U` (respectively `φ U`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipFiber

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipEngine
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} {χ : RankOneCharacter}

/-- **The line restriction to a lattice is exact** if the restriction to the lattice of the group
cohomology class of the line cocycle at `Lf` vanishes. -/
theorem classOf_lineRestriction_eq_zero (z : MaximalCycles n χ .line) (Lf : Flags .line)
    (U : Subgroup RationalGL3) (hU : U ≤ levelStabilizer Lf) {N : Type} [Group N]
    (ι : N →* ↥(levelStabilizer Lf)) (hι : Function.Injective ι)
    (hzero : twoCohomologyRestriction ι
      (subgroupCoefficientRep (levelStabilizer Lf) (rationalCoefficientComponent n χ))
      (groupCohomology.H2π
        (subgroupCoefficientRep (levelStabilizer Lf) (rationalCoefficientComponent n χ))
        (ambientCocycleToGroup (levelStabilizer Lf) (rationalCoefficientComponent n χ)
          (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) Lf z))) = 0)
    (hrad : ∀ u ∈ U, ∃ a : N, (ι a).val = u) :
    classOf U (rationalCoefficientComponent n χ) (lineRestriction z Lf U hU) = 0 :=
  classOf_pullback_eq_zero_of_restriction_zero (rationalCoefficientComponent n χ)
    (rationalCoefficientComponent n χ) (MonoidHom.id RationalGL3) (fun _ => rfl)
    (levelStabilizer Lf) U (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) Lf z)
    (lineRestriction z Lf U hU) (fun _ => rfl) ι hι hzero (fun u hu => hrad u hu)

/-- **The line restriction to a lattice is exact** if the class of the line cocycle at `Lf` in the
homogeneous cohomology of the stabilizer vanishes. -/
theorem classOf_lineRestriction_eq_zero_of_classOf (z : MaximalCycles n χ .line) (Lf : Flags .line)
    (U : Subgroup RationalGL3) (hU : U ≤ levelStabilizer Lf)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) Lf
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) = 0) :
    classOf U (rationalCoefficientComponent n χ) (lineRestriction z Lf U hU) = 0 :=
  classOf_pullback_eq_zero (rationalCoefficientComponent n χ) (rationalCoefficientComponent n χ)
    (MonoidHom.id RationalGL3) (fun _ => rfl) (levelStabilizer Lf) U (fun _ hu => hU hu)
    (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) Lf z)
    (lineRestriction z Lf U hU) (fun _ => rfl) h

/-- The dual-plane cocycle in the form of the pullback along the identity of the cocycle of the
stabilizer of the dual plane. -/
theorem planeRestriction_val (Td : DualityData n χ) (y : MaximalCycles n χ .plane)
    (Lf : Flags .line) (F : Flags .plane) (hF : Td.dualFlag Lf = F) (U : Subgroup RationalGL3)
    (hU : U ≤ levelStabilizer Lf) (x : Fin 3 → RationalGL3) :
    (planeRestriction Td y Lf U hU).val.val x =
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) F y).val.val
        (fun i => Td.φ (x i)) := by
  have t : (fun i : Fin 3 => Td.φ (x i)) = ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] := by
    funext i
    fin_cases i <;> rfl
  change y.val.val ![Td.φ (x 0), Td.φ (x 1), Td.φ (x 2)] (Td.dualFlag Lf) =
    y.val.val (fun i => Td.φ (x i)) F
  rw [hF, t]

/-- **The dual plane restriction to a lattice is exact** if the restriction to a lattice of the
group cohomology class of the plane cocycle at the dual plane vanishes, and `φ U` lies in the image
of the lattice. -/
theorem classOf_planeRestriction_eq_zero (Td : DualityData n χ) (y : MaximalCycles n χ .plane)
    (Lf : Flags .line) (F : Flags .plane) (hF : Td.dualFlag Lf = F) (U : Subgroup RationalGL3)
    (hU : U ≤ levelStabilizer Lf) {N : Type} [Group N] (ι : N →* ↥(levelStabilizer F))
    (hι : Function.Injective ι)
    (hzero : twoCohomologyRestriction ι
      (subgroupCoefficientRep (levelStabilizer F) (rationalCoefficientComponent n χ))
      (groupCohomology.H2π
        (subgroupCoefficientRep (levelStabilizer F) (rationalCoefficientComponent n χ))
        (ambientCocycleToGroup (levelStabilizer F) (rationalCoefficientComponent n χ)
          (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) F y))) = 0)
    (hrad : ∀ u ∈ U, ∃ a : N, (ι a).val = Td.φ u) :
    classOf U (dualRep Td) (planeRestriction Td y Lf U hU) = 0 :=
  classOf_pullback_eq_zero_of_restriction_zero (rationalCoefficientComponent n χ) (dualRep Td)
    Td.φ (fun _ => rfl) (levelStabilizer F) U
    (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) F y)
    (planeRestriction Td y Lf U hU) (planeRestriction_val Td y Lf F hF U hU) ι hι hzero hrad

/-- **The dual plane restriction to a lattice is exact** if the class of the plane cocycle at the
dual plane in the homogeneous cohomology of its stabilizer vanishes, and `φ U` lies in that
stabilizer. -/
theorem classOf_planeRestriction_eq_zero_of_classOf (Td : DualityData n χ)
    (y : MaximalCycles n χ .plane) (Lf : Flags .line) (F : Flags .plane)
    (hF : Td.dualFlag Lf = F) (U : Subgroup RationalGL3) (hU : U ≤ levelStabilizer Lf)
    (hφ : ∀ u ∈ U, Td.φ u ∈ levelStabilizer F)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
        0) :
    classOf U (dualRep Td) (planeRestriction Td y Lf U hU) = 0 :=
  classOf_pullback_eq_zero (rationalCoefficientComponent n χ) (dualRep Td) Td.φ (fun _ => rfl)
    (levelStabilizer F) U hφ (fixedPointCycle rationalLevel (rationalCoefficientComponent n χ) F y)
    (planeRestriction Td y Lf U hU) (planeRestriction_val Td y Lf F hF U hU) h

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipFiber
