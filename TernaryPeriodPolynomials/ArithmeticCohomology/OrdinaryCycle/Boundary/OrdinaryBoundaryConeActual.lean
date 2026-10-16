module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeMVZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.Groups

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology OrdinaryParabolicGroups
open OrdinaryBoundaryCommonRoot OrdinaryCovectors PolynomialGLAction

/-- The actual full integral GL3 representation, with all 26 covectors and polynomial action. -/
abbrev actualCoefficients (n : ℕ) (e : ℤ) := Rep.of (coefficientAction n e)

abbrev actualComplex (n : ℕ) (e : ℤ) := complex (actualCoefficients n e) P Q
abbrev actualCycles (n : ℕ) (e : ℤ) := Z1 (actualCoefficients n e) P Q
abbrev actualH1 (n : ℕ) (e : ℤ) := H1 (actualCoefficients n e) P Q
abbrev actualChains (n : ℕ) (e : ℤ) := Chains1 (actualCoefficients n e) P Q
abbrev actualChainComplex (n : ℕ) (e : ℤ) := chainComplex (actualCoefficients n e) P Q

/-- The generic face representation is literally the full P representation, not only its radical. -/
theorem actual_faceP (n : ℕ) (e : ℤ) :
    faceP (actualCoefficients n e) P = Rep.of (planeParabolicCoefficients n e) := rfl

theorem actual_faceQ (n : ℕ) (e : ℤ) :
    faceQ (actualCoefficients n e) Q = Rep.of (lineParabolicCoefficients n e) := rfl

theorem actual_corner (n : ℕ) (e : ℤ) :
    corner (actualCoefficients n e) P Q = Rep.of (BCoefficients n e) := rfl

/-- Literal triples and compatibility equation on B=P∩Q. -/
theorem actual_cycle_iff (n : ℕ) (e : ℤ)
    (c : (P → Coefficients n) × (Q → Coefficients n) × Coefficients n) :
    c ∈ actualCycles n e ↔
      c.1 ∈ cocycles₁ (Rep.of (planeParabolicCoefficients n e)) ∧
      c.2.1 ∈ cocycles₁ (Rep.of (lineParabolicCoefficients n e)) ∧
      ∀ b : B, d₀₁ (Rep.of (BCoefficients n e)) c.2.2 b = c.1 (BToP b)-c.2.1 (BToQ b) :=
  mem_Z1_iff (actualCoefficients n e) P Q c

/-- The first cohomology is the homology of the actual explicit cone complex. -/
def actualHomologyIso (n : ℕ) (e : ℤ) :
    (actualComplex n e).homology ≅ ModuleCat.of ℚ (actualH1 n e) :=
  homologyIso (actualCoefficients n e) P Q

/-- The full degree-zero/one MV exactness statements with the actual coefficient system. -/
theorem actual_mv_exact (n : ℕ) (e : ℤ) :
    LinearMap.range (invariantDiagonal (actualCoefficients n e) P Q) =
      LinearMap.ker (invariantDifference (actualCoefficients n e) P Q) ∧
    LinearMap.range (invariantDifference (actualCoefficients n e) P Q) =
      LinearMap.ker (connecting (actualCoefficients n e) P Q) ∧
    LinearMap.range (connecting (actualCoefficients n e) P Q) =
      LinearMap.ker (toFaces (actualCoefficients n e) P Q) ∧
    LinearMap.range (toFaces (actualCoefficients n e) P Q) =
      LinearMap.ker (restrictionDifference (actualCoefficients n e) P Q) :=
  ⟨range_invariantDiagonal_eq_ker_invariantDifference (actualCoefficients n e) P Q,
    range_invariantDifference_eq_ker_connecting (actualCoefficients n e) P Q,
    range_connecting_eq_ker_toFaces (actualCoefficients n e) P Q,range_toFaces_eq_ker_restrictionDifference (actualCoefficients n e) P Q⟩

/-- Actual cochain/finite-bar-chain adjunction in degree zero. -/
theorem actual_adjunction0 (n : ℕ) (e : ℤ) (v : Coefficients n × Coefficients n)
    (z : actualChains n e) :
    pair1 (actualCoefficients n e) P Q (d0 (actualCoefficients n e) P Q v) z =
      pair0 (actualCoefficients n e) v (chainBoundary1 (actualCoefficients n e) P Q z) :=
  cone_adjunction0 (actualCoefficients n e) P Q v z

/-- Actual cochain/finite-bar-chain adjunction in degree one. -/
theorem actual_adjunction1 (n : ℕ) (e : ℤ) (c : C1 (actualCoefficients n e) P Q)
    (z : Chains2 (actualCoefficients n e) P Q) :
    pair2 (actualCoefficients n e) P Q (d1 (actualCoefficients n e) P Q c) z =
      pair1 (actualCoefficients n e) P Q c (chainBoundary2 (actualCoefficients n e) P Q z) :=
  cone_adjunction1 (actualCoefficients n e) P Q c z

/-- Gauge-invariant evaluation on actual finite cone cycles. -/
theorem actual_gauge_pair_cycle (n : ℕ) (e : ℤ) (c : actualCycles n e)
    (v : Coefficients n × Coefficients n) (z : actualChains n e)
    (hz : chainBoundary1 (actualCoefficients n e) P Q z = 0) :
    pair1 (actualCoefficients n e) P Q (gauge (actualCoefficients n e) P Q c v).val z =
      pair1 (actualCoefficients n e) P Q c.val z :=
  gauge_pair_cycle (actualCoefficients n e) P Q c v z hz

/-- A literal component of the cone coboundary retains the permutation of all covectors. -/
theorem actual_d0_plane_apply (n : ℕ) (e : ℤ) (v : Coefficients n × Coefficients n)
    (g : P) (r : NonzeroCovector) :
    (d0 (actualCoefficients n e) P Q v).1 g r =
      integralAction n e g.val (v.1 (rowMove g.val r))-v.1 r := rfl

end TernaryPoly.OrdinaryBoundaryCone
