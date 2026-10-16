module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineSetup

@[expose] public section


/-!
# The binary edge of a cocycle representing a cup product on the good line

Let `D : LineCupData n` and let `Z` be a degree-two cocycle of the good-line stabilizer that
represents the cup product of the potentials of `D` (`LineCupData.Represents`).  The group
two-cocycle `ambientCocycleToGroup Z` vanishes on pairs of radical elements
(`LineCupData.cup_relative`: `a` is constant on the radical orbit of `1`), so it is literally a
relative two-cocycle (`LineCupData.lineCupRelative`).  Its mixed edge term at a radical lattice
point `r` and a Levi element `m` is computed in closed form (`LineCupData.edge_value`):

  `c (s m, u (m·r)) - c (u r, s m) = lam r (a (s m) - a 1) + (ρ(u r) w - w)`,
  `w = l (s m) (a (s m) - a 1)`,

with `s m = goodLineLeviSection m`, `u r = goodLineRadicalInclusion r`.  The second summand is the
radical coboundary of the vector `w`, which the lower-radical coordinate `lowerRadicalCoordinate`
does not see (`lowerRadicalCocycleCoordinate_oneBoundary`).  Under the Kostant law
`LineKostantLaw n lam c` (the pair of generator values of `lam` has coordinate `c q`) the binary
edge cocycle is therefore `m ↦ c • (a (s m) - a 1)` (`LineCupData.edgeCycle_value`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

theorem lineQRep_apply {n : ℕ} (γ : LineStab) (q : LineQ n) :
    lineQRep n γ q =
      (arithmeticBinaryRep (n + 1) 0).ρ (goodLineLeviProjection γ) q := rfl

theorem lineQRep_eq_self {n : ℕ} {γ : LineStab} (h : goodLineLeviProjection γ = 1)
    (q : LineQ n) : lineQRep n γ q = q := by
  rw [lineQRep_apply, h, map_one]
  rfl

/-- The group element `u r · s m` is `s m · u (m · r)`. -/
theorem goodLine_radical_commute (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineRadicalInclusion r * goodLineLeviSection m =
      goodLineLeviSection m * goodLineRadicalInclusion (lowerLeviLatticeInput m r) := by
  exact Subtype.ext (lowerLeviLatticeInput_conjugation m r)

/-- The radical lattice acts on `Hom(Q, V)` through its action on `V` alone. -/
theorem lineHom_radical_apply {n : ℕ} (r : RadicalLattice) (k : LineQ n →ₗ[ℂ] LineV n)
    (q : LineQ n) :
    Representation.linHom (lineQRep n) (lineVRep n) (goodLineRadicalInclusion r) k q =
      lineVRep n (goodLineRadicalInclusion r) (k q) := by
  rw [Representation.linHom_apply]
  change lineVRep n (goodLineRadicalInclusion r)
    (k (lineQRep n (goodLineRadicalInclusion r)⁻¹ q)) = _
  rw [lineQRep_eq_self (γ := (goodLineRadicalInclusion r)⁻¹)
    (by rw [map_inv, goodLineLeviProjection_radical, inv_one])]

/-- The radical lattice acts on `V` by the rational coefficient action of the lower unipotent. -/
theorem lineVRep_radical {n : ℕ} (r : RadicalLattice) (w : LineV n) :
    lineVRep n (goodLineRadicalInclusion r) w =
      rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) w := rfl

/-- The radical coboundary `ρ(u r) w - w` of a vector `w`. -/
def lineBoundaryValue (n : ℕ) (w : LineV n) (r : RadicalLattice) : LineV n :=
  rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) w - w

/-- **The Kostant law.**  The generator values `lam e₀ q`, `lam e₁ q` of the radical cocycle, taken
to their infinitesimal (logarithmic) pair by the inverse average equivalence, have lower-radical
coordinate `c q`.  For the genuine radical cocycle of the line parabolic at the lattice `3ℤ²` the
generator values are the `x₃`-free forms `-3 ∂₁ q` and `3 ∂₀ q`, and `c = -3 (n + 1)`
(`lineKostantLaw_of_derivative`). -/
def LineKostantLaw (n : ℕ) (lam : RadicalLattice → (LineQ n →ₗ[ℂ] LineV n)) (c : ℂ) : Prop :=
  ∀ q : LineQ n,
    lowerRadicalCoordinate n
        (fun i => (lowerRadicalAverageEquiv n i).symm (lam (radicalLatticeGenerator i) q)) =
      c • q

/-- The radical coboundary has trivial lower-radical coordinate. -/
theorem lineBoundary_coordinate_zero (n : ℕ) (pos : 0 < n) (w : LineV n) :
    lowerRadicalCoordinate n
        (fun i => (lowerRadicalAverageEquiv n i).symm
          (lineBoundaryValue n w (radicalLatticeGenerator i))) = 0 := by
  have h := lowerRadicalCocycleCoordinate_value
    (oneBoundaryCycle (lowerRadicalLatticeRep n) w)
  rw [lowerRadicalCocycleCoordinate_oneBoundary n pos w] at h
  exact h.symm

namespace LineCupData

variable {n : ℕ} (D : LineCupData n)
  {Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent n trivialCharacter)}

/-- The difference `a (s m) - a 1` of the Levi potential at the Levi section. -/
def leviDelta (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : LineQ n :=
  D.a (goodLineLeviSection m).val - D.a 1

/-- The value `l (s m) (a (s m) - a 1)` of the radical potential at the Levi section. -/
def leviVec (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : LineV n :=
  D.l (goodLineLeviSection m).val (D.leviDelta m)

/-- The mixed edge term at the radical lattice point `r`. -/
def edgeValue (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) : LineV n :=
  D.lam r (D.leviDelta m) + lineBoundaryValue n (D.leviVec m) r

/-- The values of the group two-cocycle of a cocycle representing the cup product. -/
theorem group_apply (hZ : D.Represents Z) (g h : LineStab) :
    ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) Z (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

theorem group_radical_left_zero (hZ : D.Represents Z) (r : RadicalLattice) (h : LineStab) :
    ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) Z
        (goodLineRadicalInclusion r, h) = 0 := by
  rw [D.group_apply hZ, D.a_radical, sub_self]
  exact map_zero _

/-- The cup cocycle as a relative two-cocycle: it vanishes on pairs of radical elements. -/
theorem cup_relative (hZ : D.Represents Z) :
    ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n trivialCharacter) Z ∈
      relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n) := by
  intro first second
  exact D.group_radical_left_zero hZ first (goodLineRadicalInclusion second)

/-- The cocycle as a relative two-cocycle for the radical lattice. -/
def lineCupRelative (hZ : D.Represents Z) :
    relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n) :=
  ⟨ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent n trivialCharacter) Z, D.cup_relative hZ⟩

theorem relative_apply (hZ : D.Represents Z) (g h : LineStab) :
    (D.lineCupRelative hZ).val (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

/-- The right-hand mixed term `c (u r, s m)` vanishes. -/
theorem edge_term_right (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    (D.lineCupRelative hZ).val (goodLineRadicalInclusion r, goodLineLeviSection m) = 0 :=
  D.group_radical_left_zero hZ r (goodLineLeviSection m)

/-- The left-hand mixed term `c (s m, u (m · r))`. -/
theorem edge_term_left (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    (D.lineCupRelative hZ).val (goodLineLeviSection m,
        goodLineRadicalInclusion (lowerLeviLatticeInput m r)) =
      D.lam r (D.leviDelta m) +
        (rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) (D.leviVec m) -
          D.leviVec m) := by
  have hval : (goodLineLeviSection m).val *
      (goodLineRadicalInclusion (lowerLeviLatticeInput m r)).val =
        (goodLineRadicalInclusion r).val * (goodLineLeviSection m).val :=
    (congrArg Subtype.val (goodLine_radical_commute m r)).symm
  rw [D.relative_apply hZ, hval, D.l_radical r (goodLineLeviSection m),
    LinearMap.sub_apply, LinearMap.add_apply, lineHom_radical_apply, lineVRep_radical]
  exact add_sub_assoc _ _ _

/-- **The edge value.**  The mixed term of the edge cocycle at the radical lattice point `r`. -/
theorem edge_value (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    ((D.lineCupRelative hZ).val (goodLineLeviSection m,
          goodLineRadicalInclusion (lowerLeviLatticeInput m r)) -
        (D.lineCupRelative hZ).val (goodLineRadicalInclusion r, goodLineLeviSection m) :
      LineV n) = D.edgeValue m r := by
  rw [D.edge_term_right hZ, sub_zero]
  exact D.edge_term_left hZ m r

/-- The binary edge cocycle is the lower-radical coordinate of the edge values. -/
theorem coordinate_edge (hZ : D.Represents Z) (pos : 0 < n)
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineBinaryEdgeCycle n pos (D.lineCupRelative hZ) m : LineQ n) =
      lowerRadicalCoordinate n
        (fun i => (lowerRadicalAverageEquiv n i).symm
          (D.edgeValue m (radicalLatticeGenerator i))) := by
  rw [goodLineBinaryEdgeCycle_value]
  exact congrArg (lowerRadicalCoordinate n)
    (funext fun i => congrArg (fun v => (lowerRadicalAverageEquiv n i).symm v)
      (D.edge_value hZ m (radicalLatticeGenerator i)))

/-- **The binary edge cocycle, pointwise, under the Kostant law.** -/
theorem edgeCycle_value (hZ : D.Represents Z) (pos : 0 < n) {c : ℂ}
    (hK : LineKostantLaw n D.lam c) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineBinaryEdgeCycle n pos (D.lineCupRelative hZ) m : LineQ n) = c • D.leviDelta m := by
  rw [D.coordinate_edge hZ pos m]
  have hsplit : (fun i : Fin 2 => (lowerRadicalAverageEquiv n i).symm
        (D.edgeValue m (radicalLatticeGenerator i))) =
      (fun i : Fin 2 => (lowerRadicalAverageEquiv n i).symm
        (D.lam (radicalLatticeGenerator i) (D.leviDelta m))) +
      (fun i : Fin 2 => (lowerRadicalAverageEquiv n i).symm
        (lineBoundaryValue n (D.leviVec m) (radicalLatticeGenerator i))) := by
    funext i
    exact map_add (lowerRadicalAverageEquiv n i).symm _ _
  rw [hsplit, map_add, hK (D.leviDelta m), lineBoundary_coordinate_zero n pos (D.leviVec m),
    add_zero]

end LineCupData

end TernaryPeriodPolynomials.SourceConstruction
