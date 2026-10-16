module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Edge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global

@[expose] public section


/-!
# Cup products of two potentials on the good-plane stabilizer

The good-plane analogue of `DetectSetup`/`DetectEdge`/`DetectBridge`.  In the block coordinates of
`GoodPlaneFrame` the stabilizer of the good plane is `Λ = ΛG = g⁻¹ Γ_F g`, `g = gF`, a split extension
`ℤ² ⋊ (Γ₁'(3) × ℤˣ)` (`goodPlaneExtension`); its radical lattice is the standard one, so the radical
potential and the Kostant law are literally those of the identity plane (`KostantLaw`).

`GoodPlaneCupData n` is the data of two potentials `a` (Levi) and `l` (radical) on `GL₃(ℚ)` with the two
laws along the radical lattice `goodPlaneExtension.inl`.  A degree-two cocycle `Z` of `ΛG`
**represents the cup product** of the potentials if on the vertex triples `(1, g, g h)` it takes the
values `(l (g h) - l g) (a g - a 1)` (`GoodPlaneCupData.Represents`).  Then:

* the group two-cocycle of `Z` is a relative two-cocycle (`GoodPlaneCupData.relative`);
* its good-plane edge cocycle is `m ↦ Φ (c • (a (Pg 0 m 1) - a 1))` under the Kostant law
  (`GoodPlaneCupData.edgeVal_eq`, `GoodPlaneEdge2.goodPlaneEdgeCocycle`), `Φ = Sym^{n+1}(δ)`;
* hence `goodPlaneEdgeH2` of the class of `Z` is nonzero as soon as `c ≠ 0` and the Levi potential
  `m ↦ Φ (a (Pg 0 m 1) - a 1)` is not a crossed coboundary of `levelRep (n + 1) (-1)`
  (`GoodPlaneCupData.edge_ne_zero`);
* a source whose values at the good-plane flag, on the `gF`-translated rational vertices, are the
  `gF`-translate of the cup chain has nonzero good-plane Shapiro coordinate
  (`cuspRes_plane_true_ne_zero`, `cuspRes_plane_true_ne_zero_of_evaluates`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls qcls_eq_zero_iff)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel cuspRes)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag goodPlaneFrame)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- **The potentials of a cup-product cocycle on the good-plane stabilizer** (in block
coordinates).  `a` is the Levi potential, constant on the radical orbit of `1`; `l` the radical
potential, with the cocycle law `l (u r · g) = lam r + u r · l g` along the radical lattice. -/
structure GoodPlaneCupData (n : ℕ) where
  /-- The Levi potential. -/
  a : RationalGL3 → Binary.HomogeneousPoly (n + 1)
  /-- The radical potential. -/
  l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)
  /-- The radical cocycle on the radical lattice. -/
  lam : RadicalLattice → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)
  /-- The Levi potential does not see the radical lattice. -/
  a_radical : ∀ r : RadicalLattice, a (goodPlaneExtension.inl r).val = a 1
  /-- The cocycle law of the radical potential along the radical lattice. -/
  l_radical : ∀ (r : RadicalLattice) (g : RationalGL3) (Q : Binary.HomogeneousPoly (n + 1)),
    l ((goodPlaneExtension.inl r).val * g) Q = lam r Q +
      rationalCoefficientComponent n trivialCharacter (goodPlaneExtension.inl r).val (l g Q)

/-- A degree-two cocycle of `ΛG` **represents the cup product** of the potentials: on the vertex
triples `(1, g, g h)` it takes the values `(l (g h) - l g) (a g - a 1)`. -/
def GoodPlaneCupData.Represents {n : ℕ} (D : GoodPlaneCupData n)
    (Z : cocycles ΛG (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∀ g h : ΛG, Z.val.val ![1, g.val, g.val * h.val] =
    (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1)

/-- The Levi potential after the coefficient transport `Φ = Sym^{n+1}(δ)`:
`m ↦ Φ (a (Pg 0 m 1) - a 1)`, the value of the Levi cocycle at the section `m ↦ Pg 0 m 1`. -/
def GoodPlaneCupData.leviDelta {n : ℕ} (D : GoodPlaneCupData n) (m : binaryArithmeticLevel) :
    Binary.HomogeneousPoly (n + 1) :=
  Phi n (D.a (Pg 0 m 1) - D.a 1)

/-- The Levi potential is **not a crossed coboundary** of `levelRep (n + 1) (-1)`; for a Levi
cocycle this is `[φ] ≠ 0` in `CrossedH1 (levelRep (n + 1) (-1))`. -/
def GoodPlaneCupData.NotCoboundary {n : ℕ} (D : GoodPlaneCupData n) : Prop :=
  ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
    D.leviDelta m = levelRep (n + 1) (-1) m w - w

/-- The coefficient action of `gF⁻¹` inverts that of `gF`. -/
theorem rho_gF_inv_apply {n : ℕ} (v : HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter gF⁻¹
      (rationalCoefficientComponent n trivialCharacter gF v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel, map_one, Module.End.one_apply]

/-- The radical lattice does not change the restriction `x₂ = 0`. -/
theorem restrict_radical {n : ℕ} (r : RadicalLattice) (w : HomogeneousPoly n) :
    binaryHomogeneousRestrict n
      (rationalCoefficientComponent n trivialCharacter (goodPlaneExtension.inl r).val w) =
    binaryHomogeneousRestrict n w := by
  have e : (goodPlaneExtension.inl r).val = upperRadicalLattice r := rfl
  rw [e]
  exact binaryHomogeneousRestrict_upperLattice n r w

namespace GoodPlaneCupData

variable {n : ℕ} (D : GoodPlaneCupData n)
  {Z : cocycles ΛG (rationalCoefficientComponent n trivialCharacter)}

/-- The values of the group two-cocycle of a cocycle representing the cup product. -/
theorem group_apply (hZ : D.Represents Z) (g h : ΛG) :
    ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter) Z (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

theorem group_radical_left_zero (hZ : D.Represents Z) (r : RadicalLattice) (h : ΛG) :
    ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter) Z
        (goodPlaneExtension.inl r, h) = 0 := by
  rw [D.group_apply hZ, D.a_radical, sub_self]
  exact map_zero _

/-- The cup cocycle as a relative two-cocycle: it vanishes on pairs of radical elements. -/
theorem cup_relative (hZ : D.Represents Z) :
    ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter) Z ∈
      relativeTwoCocycles goodPlaneExtension.inl (coefRep n) := by
  intro first second
  exact D.group_radical_left_zero hZ first (goodPlaneExtension.inl second)

/-- The cocycle as a relative two-cocycle for the radical lattice. -/
def relative (hZ : D.Represents Z) : relativeTwoCocycles goodPlaneExtension.inl (coefRep n) :=
  ⟨ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter) Z,
    D.cup_relative hZ⟩

theorem relative_apply (hZ : D.Represents Z) (g h : ΛG) :
    (D.relative hZ).val (g, h) =
      (D.l (g.val * h.val) - D.l g.val) (D.a g.val - D.a 1) := hZ g h

/-- The right-hand mixed term `c (u r, s ℓ)` vanishes. -/
theorem edge_term_right (hZ : D.Represents Z) (ℓ : Levi) (r : RadicalLattice) :
    (D.relative hZ).val (goodPlaneExtension.inl r, goodPlaneSplitting ℓ) = 0 :=
  D.group_radical_left_zero hZ r (goodPlaneSplitting ℓ)

/-- The left-hand mixed term `c (s ℓ, u (ℓ⁻¹ · r))`. -/
theorem edge_term_left (hZ : D.Represents Z) (ℓ : Levi) (r : RadicalLattice) :
    (D.relative hZ).val (goodPlaneSplitting ℓ,
        goodPlaneExtension.inl (splitRadicalInput goodPlaneSplitting ℓ r)) =
      D.lam r (D.a (goodPlaneSplitting ℓ).val - D.a 1) +
        rationalCoefficientComponent n trivialCharacter (goodPlaneExtension.inl r).val
          (D.l (goodPlaneSplitting ℓ).val (D.a (goodPlaneSplitting ℓ).val - D.a 1)) -
        D.l (goodPlaneSplitting ℓ).val (D.a (goodPlaneSplitting ℓ).val - D.a 1) := by
  have hval : (goodPlaneSplitting ℓ).val *
      (goodPlaneExtension.inl (splitRadicalInput goodPlaneSplitting ℓ r)).val =
        (goodPlaneExtension.inl r).val * (goodPlaneSplitting ℓ).val :=
    (congrArg Subtype.val (splitRadicalInput_commute goodPlaneSplitting ℓ r)).symm
  rw [D.relative_apply hZ, hval, LinearMap.sub_apply, D.l_radical r]

/-- The restricted mixed edge term at the radical lattice point `r`. -/
theorem res_edge (hZ : D.Represents Z) (ℓ : Levi) (r : RadicalLattice) :
    binaryHomogeneousRestrict n
        (splitEdgeCycle goodPlaneSplitting (coefRep n) ℓ (D.relative hZ) r) =
      binaryHomogeneousRestrict n (D.lam r (D.a (goodPlaneSplitting ℓ).val - D.a 1)) := by
  rw [splitEdgeCycle_apply goodPlaneSplitting (coefRep n) ℓ (D.relative hZ) r,
    D.edge_term_right hZ ℓ r, sub_zero, D.edge_term_left hZ ℓ r, map_sub, map_add,
    restrict_radical]
  abel

/-- **The edge value at a Levi element of `Γ₁'(3)`, under the Kostant law.** -/
theorem edgeVal_eq (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c)
    (m : binaryArithmeticLevel) :
    edgeVal (D.relative hZ) (m, 1) = c • (D.a (Pg 0 m 1) - D.a 1) := by
  apply Subtype.ext
  have h := upperRadicalCocycleCoordinate_value (degree := n)
    (splitEdgeCycle goodPlaneSplitting (coefRep n) (m, 1) (D.relative hZ))
  have f1 := congrArg Subtype.val (D.res_edge hZ (m, 1) radicalLatticeFirst)
  have f2 := congrArg Subtype.val (D.res_edge hZ (m, 1) radicalLatticeSecond)
  refine h.trans ((congrArg₂ (fun (u v : Binary.Poly) => ((n : ℂ) + 1)⁻¹ •
      (MvPolynomial.X 0 * u + MvPolynomial.X 1 * v)) f1 f2).trans ?_)
  exact hK (D.a (Pg 0 m 1) - D.a 1)

/-- The good-plane edge of the class of a cocycle representing the cup product is the class of
the edge cocycle of its relative two-cocycle. -/
theorem goodPlaneEdgeH2_cup (hn : 0 < n) (hZ : D.Represents Z) :
    goodPlaneEdgeH2 hn (classOf ΛG (rationalCoefficientComponent n trivialCharacter) Z) =
      qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle (D.relative hZ)) :=
  goodPlaneEdgeH2_apply hn Z (D.relative hZ) rfl

/-- **The good-plane edge of a cup-product class is nonzero** when the Kostant constant is
nonzero and the Levi potential is not a crossed coboundary. -/
theorem edge_ne_zero (hn : 0 < n) (hZ : D.Represents Z) {c : ℂ} (hK : KostantLaw n D.lam c)
    (hc : c ≠ 0) (hN : D.NotCoboundary) :
    goodPlaneEdgeH2 hn (classOf ΛG (rationalCoefficientComponent n trivialCharacter) Z) ≠ 0 := by
  rw [D.goodPlaneEdgeH2_cup hn hZ]
  intro h0
  rw [qcls_eq_zero_iff] at h0
  obtain ⟨w, hw⟩ := h0
  refine hN ⟨c⁻¹ • w, fun m => ?_⟩
  have hm := congrFun (congrArg Subtype.val hw) m
  change levelRep (n + 1) (-1) m w - w = Phi n (edgeVal (D.relative hZ) (m, 1)) at hm
  rw [D.edgeVal_eq hZ hK m, map_smul] at hm
  show Phi n (D.a (Pg 0 m 1) - D.a 1) = levelRep (n + 1) (-1) m (c⁻¹ • w) - c⁻¹ • w
  rw [map_smul]
  exact ((eq_inv_smul_iff₀ hc).mpr hm.symm).trans (smul_sub c⁻¹ _ _)

end GoodPlaneCupData

/-- **The good-plane Shapiro coordinate of a class whose values on the `gF`-translated vertices
represent the cup product is nonzero.**  The hypothesis `hz` says that the cocycle `z` at the
reference good-plane flag, on the vertex triples `gF · y`, is the `gF`-translate of the cup chain
of the potentials; the conclusion holds when the Kostant constant is nonzero and the Levi
potential is not a crossed coboundary. -/
theorem cuspRes_plane_true_ne_zero {n : ℕ} (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (hn : 0 < n) (D : GoodPlaneCupData n) {c : ℂ} (hK : KostantLaw n D.lam c) (hc : c ≠ 0)
    (hN : D.NotCoboundary)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane))
    (hz : ∀ y : Fin 3 → RationalGL3,
      z.val.val (fun i => gF * y i) (cuspFlag .plane true) =
        rationalCoefficientComponent n χ gF ((D.l (y 2) - D.l (y 1)) (D.a (y 1) - D.a (y 0)))) :
    cuspRes n χ .plane true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) z) ≠
        0 := by
  subst hχ
  intro h0
  have h1 : classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter)
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .plane true) z) = 0 :=
    (TernaryPeriodPolynomials.Separation.cuspRes_classOf trivialCharacter .plane
      true z).symm.trans h0
  have hZc : D.Represents (TernaryPeriodPolynomials.LevelThree.GoodPlaneConj.conjCycle
      (rationalCoefficientComponent n trivialCharacter) gF (cuspLevel .plane true) ΛG hH_conj
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .plane true) z)) := by
    intro g h
    have e1 := hz ![1, g.val, g.val * h.val]
    exact (congrArg (rationalCoefficientComponent n trivialCharacter gF⁻¹) e1).trans
      (rho_gF_inv_apply _)
  apply D.edge_ne_zero hn hZc hK hc hN
  have h3 : psiG (n := n) (classOf (cuspLevel .plane true)
      (rationalCoefficientComponent n trivialCharacter)
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .plane true) z)) = 0 := by
    rw [h1]
    exact LinearEquiv.map_zero _
  have h4 : goodPlaneEdgeH2 hn (psiG (n := n) (classOf (cuspLevel .plane true)
      (rationalCoefficientComponent n trivialCharacter)
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (cuspFlag .plane true) z))) = 0 := by
    rw [h3]
    exact map_zero _
  exact h4

/-- **The same for a source evaluated at the good-plane flag in the sense of `Evaluates`**: it
suffices that the source, at the adelic argument `rationalGroup (goodPlaneFrame)⁻¹`, on the
`gF`-translated rational vertices, is the `gF`-translate of the cup chain of the potentials. -/
theorem cuspRes_plane_true_ne_zero_of_evaluates {n : ℕ} (E : InducingData n)
    (hχ : E.chi = trivialCharacter) (hn : 0 < n) (D : GoodPlaneCupData n) {c : ℂ}
    (hK : KostantLaw n D.lam c) (hc : c ≠ 0) (hN : D.NotCoboundary)
    {source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n E.chi) .plane)}
    (hz : Evaluates E .plane source z)
    (hsource : ∀ y : Fin 3 → RationalGL3,
      source (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (gF * y i))
          (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) =
        rationalCoefficientComponent n E.chi gF
          ((D.l (y 2) - D.l (y 1)) (D.a (y 1) - D.a (y 0)))) :
    cuspRes n E.chi .plane true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .plane)
        z) ≠ 0 :=
  cuspRes_plane_true_ne_zero E.chi hχ hn D hK hc hN z
    (fun y => (hz (fun i => gF * y i) (rational goodPlaneFrame)).trans (hsource y))

end TernaryPeriodPolynomials.SourceConstruction
