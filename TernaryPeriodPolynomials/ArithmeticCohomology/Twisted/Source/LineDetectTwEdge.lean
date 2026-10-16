module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.LowerRadicalDerivative

@[expose] public section


/-!
# The binary edge of a cocycle representing a cup product, at the good line

Good-line analogue of `DetectTwEdge` for a rank-one character `χ` with `χ(-1_∞) = -1`.  The
stabilizer `Λ₁` of the good line acts on `V = HomogeneousPoly n` through
`rationalCoefficientComponent n χ` (`lineVRepTw`) and on binary forms `Q` of degree `n + 1` through
its Levi quotient `GL₂(ℤ)` with the determinant twist `-1` (`lineQRepTw`), the Levi module of the twisted
good-line edge `goodLineBinaryEdgeCycleT` of `AxiomCodeTwisted`.

`LineCupDataTw n χ` consists of the two potentials `a`, `l` on the vertex set `GL₃(ℚ)` and the
radical cocycle `lam` on the lower radical lattice.  A degree-two cocycle `Z` of `Λ₁` represents
their cup product (`LineCupDataTw.Represents`) if its values on the vertex triples `(1, g, g h)` are
`(l (g h) - l g) (a g - a 1)`.  Then `Z` is a relative two-cocycle for the lower radical lattice
(`LineCupDataTw.cup_relative`).  The lower radical lattice has step three, so the edge averages the
radical values over the unit interval; the averaging is inverted on the value `lam r Δ` thanks to
`lam_free` (the radical cocycle is free of `x₂`) and is killed by the lower radical coordinate on the
coboundary part (`lowerRadicalCoordinate_lowerShear`).  Under the Kostant law
(`LowerKostant n lam c`) the twisted binary edge cocycle is `m ↦ c • (a (s m) - a 1)`
(`LineCupDataTw.edgeCycle_value`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Twisted
  (goodLineCoefficientRepT goodLineBinaryEdgeCycleT goodLineBinaryEdgeCycle_valueT
    rho_lowerRadicalLattice)
open TernaryPeriodPolynomials.AnalyticClasses
  (lowerShear lowerShear_val lowerRadicalCoordinate_lowerShear)

noncomputable section

attribute [local instance] complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.TwistedSource

/-- The stabilizer of the good line in the arithmetic level group. -/
abbrev LineStabTw : Type :=
  ↥(flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))

/-- The binary forms of degree `n + 1`. -/
abbrev LineQTw (n : ℕ) : Type := Binary.HomogeneousPoly (n + 1)

/-- The ternary coefficient module of degree `n`. -/
abbrev LineVTw (n : ℕ) : Type := HomogeneousPoly n

/-- The coefficient action of the good-line stabilizer on `V`, for the character `χ`. -/
def lineVRepTw (n : ℕ) (χ : RankOneCharacter) : Representation ℂ LineStabTw (LineVTw n) :=
  (rationalCoefficientComponent n χ).comp
    (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)).subtype

/-- The action of the good-line stabilizer on binary forms, through the Levi quotient, with
determinant twist `-1` (the Levi module `arithmeticBinaryRep (n + 1) (-1)` of the twisted edge). -/
def lineQRepTw (n : ℕ) : Representation ℂ LineStabTw (LineQTw n) :=
  ((Binary.homogeneousAction (n + 1) (-1)).comp
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ))).comp goodLineLeviProjection

theorem lineQRepTw_apply {n : ℕ} (γ : LineStabTw) (q : LineQTw n) :
    lineQRepTw n γ q =
      (arithmeticBinaryRep (n + 1) (-1)).ρ (goodLineLeviProjection γ) q := rfl

theorem lineQRepTw_eq_self {n : ℕ} {γ : LineStabTw} (h : goodLineLeviProjection γ = 1)
    (q : LineQTw n) : lineQRepTw n γ q = q := by
  rw [lineQRepTw_apply, h, map_one]
  rfl

/-- The group element `u r · s m` is `s m · u (m · r)`. -/
theorem line_radical_commute (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineRadicalInclusion r * goodLineLeviSection m =
      goodLineLeviSection m * goodLineRadicalInclusion (lowerLeviLatticeInput m r) :=
  Subtype.ext (lowerLeviLatticeInput_conjugation m r)

/-- The radical lattice acts on `Hom(Q, V)` through its action on `V` alone. -/
theorem linHom_radical_applyLineTw {n : ℕ} (χ : RankOneCharacter) (r : RadicalLattice)
    (k : LineQTw n →ₗ[ℂ] LineVTw n) (q : LineQTw n) :
    Representation.linHom (lineQRepTw n) (lineVRepTw n χ) (goodLineRadicalInclusion r) k q =
      lineVRepTw n χ (goodLineRadicalInclusion r) (k q) := by
  rw [Representation.linHom_apply]
  change lineVRepTw n χ (goodLineRadicalInclusion r)
    (k (lineQRepTw n (goodLineRadicalInclusion r)⁻¹ q)) = _
  rw [lineQRepTw_eq_self (γ := (goodLineRadicalInclusion r)⁻¹)
    (by rw [map_inv, goodLineLeviProjection_radical, inv_one])]

theorem radicalLatticeGenerator_zero : radicalLatticeGenerator 0 = radicalLatticeFirst := by
  simp [radicalLatticeGenerator]

theorem radicalLatticeGenerator_one : radicalLatticeGenerator 1 = radicalLatticeSecond := by
  simp [radicalLatticeGenerator]

/-- The generators of the radical lattice act on `V` by the exponential of the nilpotent lower
radical generators. -/
theorem lineVRepTw_radicalGenerator {n : ℕ} (χ : RankOneCharacter) (i : Fin 2) :
    lineVRepTw n χ (goodLineRadicalInclusion (radicalLatticeGenerator i)) =
      IsNilpotent.exp (lowerRadicalGenerator n i) := by
  revert i
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [radicalLatticeGenerator_zero]
    exact (rho_lowerRadicalLattice n χ radicalLatticeFirst).trans (lowerRadicalLatticeRep_first n)
  · rw [radicalLatticeGenerator_one]
    exact (rho_lowerRadicalLattice n χ radicalLatticeSecond).trans (lowerRadicalLatticeRep_second n)

/-- The lower radical generator is three times the derivative `lowerShear`. -/
theorem lowerRadicalGenerator_eq_smul_lowerShear (n : ℕ) (i : Fin 2) :
    lowerRadicalGenerator n i = (3 : ℂ) • lowerShear n i := by
  rw [lowerRadicalGenerator, lowerShear, smul_smul]
  norm_num

theorem lowerShear_eq_zero_of_free {n : ℕ} (i : Fin 2) {v : HomogeneousPoly n}
    (h : MvPolynomial.pderiv 2 v.val = 0) : lowerShear n i v = 0 :=
  Subtype.ext (by rw [lowerShear_val, h, mul_zero, neg_zero]; rfl)

/-- The exponential average fixes every vector killed by the operator. -/
theorem average_eq_self_of_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N : Module.End ℂ V) (cutoff : ℕ) (x : V) (hx : N x = 0) :
    nilpotentExponentialAverage N (cutoff + 1) x = x := by
  have comm : Commute N (∑ index ∈ Finset.range cutoff, ((index + 2).factorial : ℚ)⁻¹ • N ^ index) := by
    apply Commute.sum_right
    intro index _
    exact ((Commute.refl N).pow_right index).smul_right _
  have h : (nilpotentExponentialAverage N (cutoff + 1) - 1) x = 0 := by
    rw [nilpotentExponentialAverage_remainder, comm.eq, Module.End.mul_apply, hx, map_zero]
  rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h

/-- The Kostant law at the good line: the lower radical coordinate of the values of the radical
cocycle on the two generators of the radical lattice is `c • Q`. -/
def LowerKostant (n : ℕ) (lam : RadicalLattice → (LineQTw n →ₗ[ℂ] LineVTw n)) (c : ℂ) : Prop :=
  ∀ Q : LineQTw n, lowerRadicalCoordinate n (fun i => lam (radicalLatticeGenerator i) Q) = c • Q

/-- Under the Kostant law, the lower radical coordinate of the pair `λ(e_i) Δ + N_i w` is `c • Δ`:
the second summand is the infinitesimal coboundary of `w`. -/
theorem lowerRadicalCoordinate_kostant {n : ℕ}
    {lam : RadicalLattice → (LineQTw n →ₗ[ℂ] LineVTw n)} {c : ℂ} (hK : LowerKostant n lam c)
    (Δ : LineQTw n) (w : LineVTw n) :
    lowerRadicalCoordinate n
        (fun i => lam (radicalLatticeGenerator i) Δ + lowerRadicalGenerator n i w) = c • Δ := by
  have hfun : (fun i : Fin 2 => lam (radicalLatticeGenerator i) Δ + lowerRadicalGenerator n i w) =
      (fun i => lam (radicalLatticeGenerator i) Δ) + (3 : ℂ) • (fun i => lowerShear n i w) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, lowerRadicalGenerator_eq_smul_lowerShear,
      LinearMap.smul_apply]
  rw [hfun, map_add, map_smul, lowerRadicalCoordinate_lowerShear, smul_zero, add_zero]
  exact hK Δ

/-- The two potentials whose cup product is the line source cocycle at the good line, with the laws
used by the binary edge, for the character `χ`.  `lam` is the radical cocycle on the lower radical
lattice, free of `x₂`. -/
structure LineCupDataTw (n : ℕ) (χ : RankOneCharacter) where
  /-- The Levi potential. -/
  a : RationalGL3 → LineQTw n
  /-- The radical potential. -/
  l : RationalGL3 → (LineQTw n →ₗ[ℂ] LineVTw n)
  /-- The radical cocycle on the radical lattice, the coboundary of `l`. -/
  lam : RadicalLattice → (LineQTw n →ₗ[ℂ] LineVTw n)
  /-- The Levi potential does not see the radical lattice. -/
  a_radical : ∀ r : RadicalLattice, a (goodLineRadicalInclusion r).val = a 1
  /-- The cocycle law of the radical potential along the radical lattice. -/
  l_radical : ∀ (r : RadicalLattice) (g : LineStabTw),
    l ((goodLineRadicalInclusion r).val * g.val) =
      lam r + Representation.linHom (lineQRepTw n) (lineVRepTw n χ)
        (goodLineRadicalInclusion r) (l g.val)
  /-- The radical cocycle takes values free of `x₂`. -/
  lam_free : ∀ (r : RadicalLattice) (Q : LineQTw n), MvPolynomial.pderiv 2 (lam r Q).val = 0

/-- A degree-two cocycle of the good-line stabilizer **represents the cup product** of the
potentials: on the vertex triples `(1, g, g h)` it takes the values `(l (g h) - l g) (a g - a 1)`. -/
def LineCupDataTw.Represents {n : ℕ} {χ : RankOneCharacter} (D : LineCupDataTw n χ)
    (Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n χ)) : Prop :=
  ∀ g h : LineStabTw, Z.val.val ![1, g.val, g.val * h.val] =
    (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)

namespace LineCupDataTw

variable {n : ℕ} {χ : RankOneCharacter} (D : LineCupDataTw n χ)
  {Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent n χ)}

/-- The values of the group two-cocycle of a cocycle representing the cup product. -/
theorem group_apply (hZ : D.Represents Z) (g h : LineStabTw) :
    ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ) Z (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

theorem group_radical_left_zero (hZ : D.Represents Z) (r : RadicalLattice) (h : LineStabTw) :
    ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ) Z (goodLineRadicalInclusion r, h) = 0 := by
  rw [D.group_apply hZ, D.a_radical, sub_self]
  exact map_zero _

/-- The cup cocycle as a relative two-cocycle: it vanishes on pairs of radical elements. -/
theorem cup_relative (hZ : D.Represents Z) :
    ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent n χ) Z ∈
      relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ) := by
  intro first second
  exact D.group_radical_left_zero hZ first (goodLineRadicalInclusion second)

/-- The cocycle as a relative two-cocycle for the lower radical lattice. -/
def lineCupRelative (hZ : D.Represents Z) :
    relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRepT n χ) :=
  ⟨ambientCocycleToGroup (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent n χ) Z, D.cup_relative hZ⟩

theorem relative_apply (hZ : D.Represents Z) (g h : LineStabTw) :
    (D.lineCupRelative hZ).val (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

/-- The right-hand mixed term `c (u r, s m)` vanishes. -/
theorem edge_term_right (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    (D.lineCupRelative hZ).val (goodLineRadicalInclusion r, goodLineLeviSection m) = 0 :=
  D.group_radical_left_zero hZ r (goodLineLeviSection m)

/-- The left-hand mixed term: `λ(r) Δ + (ρ(u r) - 1)(l(s m) Δ)`. -/
theorem edge_term_left (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    (D.lineCupRelative hZ).val (goodLineLeviSection m,
        goodLineRadicalInclusion (lowerLeviLatticeInput m r)) =
      D.lam r (D.a (goodLineLeviSection m).val - D.a 1) +
        (lineVRepTw n χ (goodLineRadicalInclusion r)
            (D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1)) -
          D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1)) := by
  have hval : (goodLineLeviSection m).val *
      (goodLineRadicalInclusion (lowerLeviLatticeInput m r)).val =
        (goodLineRadicalInclusion r).val * (goodLineLeviSection m).val :=
    (congrArg Subtype.val (line_radical_commute m r)).symm
  rw [D.relative_apply hZ, hval, D.l_radical r (goodLineLeviSection m),
    LinearMap.sub_apply, LinearMap.add_apply, linHom_radical_applyLineTw]
  abel

/-- **The edge pair.**  The inverse exponential average of the mixed term in the direction `e_i` is
`λ(e_i) Δ + N_i (l(s m) Δ)`, where `N_i` is the nilpotent generator of the lower radical. -/
theorem edge_average (hZ : D.Represents Z) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) (i : Fin 2) :
    (lowerRadicalAverageEquiv n i).symm
        ((D.lineCupRelative hZ).val (goodLineLeviSection m,
            goodLineRadicalInclusion (lowerLeviLatticeInput m (radicalLatticeGenerator i))) -
          (D.lineCupRelative hZ).val (goodLineRadicalInclusion (radicalLatticeGenerator i),
            goodLineLeviSection m)) =
      D.lam (radicalLatticeGenerator i) (D.a (goodLineLeviSection m).val - D.a 1) +
        lowerRadicalGenerator n i
          (D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1)) := by
  rw [D.edge_term_right hZ, sub_zero, D.edge_term_left hZ, lineVRepTw_radicalGenerator,
    LinearEquiv.symm_apply_eq, map_add]
  have hx : lowerRadicalGenerator n i
      (D.lam (radicalLatticeGenerator i) (D.a (goodLineLeviSection m).val - D.a 1)) = 0 := by
    rw [lowerRadicalGenerator_eq_smul_lowerShear, LinearMap.smul_apply,
      lowerShear_eq_zero_of_free i (D.lam_free _ _), smul_zero]
  have h1 : lowerRadicalAverageEquiv n i
      (D.lam (radicalLatticeGenerator i) (D.a (goodLineLeviSection m).val - D.a 1)) =
        D.lam (radicalLatticeGenerator i) (D.a (goodLineLeviSection m).val - D.a 1) :=
    average_eq_self_of_kernel (lowerRadicalGenerator n i) n _ hx
  have h2 : lowerRadicalAverageEquiv n i
      (lowerRadicalGenerator n i
        (D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1))) =
      IsNilpotent.exp (lowerRadicalGenerator n i)
          (D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1)) -
        D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1) := by
    have difference := nilpotent_difference_apply (lowerRadicalGenerator n i) n
      (lowerRadicalGenerator_power_zero n i)
      (D.l (goodLineLeviSection m).val (D.a (goodLineLeviSection m).val - D.a 1))
    rw [LinearMap.sub_apply, Module.End.one_apply] at difference
    rw [exp_inst_irrel _ Algebra.toModule]
    exact difference.symm
  rw [h1, h2]

/-- **The edge value.**  Under the Kostant law the twisted binary edge cocycle of the cup cocycle is
`m ↦ c • (a (s m) - a 1)`. -/
theorem edgeCycle_value (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (positive : 0 < n)
    (hZ : D.Represents Z) {c : ℂ} (hK : LowerKostant n D.lam c)
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineBinaryEdgeCycleT n χ hχ positive (D.lineCupRelative hZ) m).val =
      c • (D.a (goodLineLeviSection m).val - D.a 1).val := by
  rw [goodLineBinaryEdgeCycle_valueT]
  exact (congrArg (fun v : Fin 2 → HomogeneousPoly n => (lowerRadicalCoordinate n v).val)
    (funext fun i => D.edge_average hZ m i)).trans
      (congrArg Subtype.val (lowerRadicalCoordinate_kostant hK _ _))

end LineCupDataTw

end TernaryPeriodPolynomials.TwistedSource
