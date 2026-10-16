module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOdd

@[expose] public section


/-!
# The Levi cocycle of the dual plane of the bad line is the transported good-plane edge

The dual plane of the bad line `L₀` is the good plane `F = longWeyl ⟨e₀, e₁⟩`.  Let `y` be a plane
cocycle of the maximal stratum, `η(x) = y(φ x)(F)` the plane cocycle of the fiber integration, and
`θ_U` a `U`-equivariant primitive of `η` over the lattice `U` of `L₀`.  The cocycle of the
good-plane stabilizer in block coordinates (`GoodPlaneEdge3.psiG`) is
`D(x) = ρ(τ⁻¹) y(τ x)(F)`, with `τ = q g_F` (`BadIdentPlaneFrame`), because `q` carries the
reference good-plane flag to `F`.  The primitive `θ_U ∘ φ` of `y(·)(F)` is transported to
`ω_G(a, b) = ρ(τ⁻¹) θ_U(φ(τ a), φ(τ b))`, a primitive of `D` which is equivariant over the standard
radical lattice of `Λ_G`, since `τ u(p) τ⁻¹ = φ(u_L(σ p))`.

The Levi identity (`ParabolicDualityIdentCore`) for the relative representative of `D` at the Levi
element `P(0, κ(α γ), 1)`, with `τ P(0, κ(α γ), 1) τ⁻¹ = φ(diag(1, γ))`, gives the edge cocycle in
terms of the Levi cocycle `A'(k_γ⁻¹)` of `θ_U`, up to a coboundary which does not change the radical
coordinate.  Comparing with the rotated coordinate `Ψ` of the bridge (the exchange `σ` in the
lattice coordinates is the Levi translate by `q`), one obtains, *exactly*, for every `γ ∈ Γ₁'(3)`:

  `badX' γ = - E (goodPlaneEdgeCocycle c (α γ))`,    `E = σ_var ∘ rot ∘ Sym(σ) ∘ Φ⁻¹`,

where `c` is the relative representative of the good-plane cocycle and `α` the involution of
`Γ₁'(3)` exchanging the cusps (`BadIdentPlaneFrame`).  The linear map `E` intertwines
`Sym^{n+1} ⊗ det⁻¹` at `α γ` with `Sym^{n+1}` at `γ` for even `n`
(`planeComparison_intertwines`).  The class of `c` is the good-plane edge of the Shapiro coordinate
of the plane class at the good-plane cusp (`goodPlaneEdge_cusp_eq`), so `badX'` is a parabolic
cocycle when this coordinate is a local joint generalized eigenclass
(`badX'_mem_parabolicCrossed`).  For odd `n` the same computation applies to the cocycle `badXOdd'`
of the odd-degree bridge, which has coefficients `Sym^{n+1} ⊗ det⁻¹` (`badXOdd'_apply`,
`planeComparison_intertwines_odd`, `badXOdd'_mem_parabolicCrossed`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open scoped Matrix
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (GL2Z)
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel cuspRes localJoint)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (gF ΛG Pg kap)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
  (act act_zero Pg_mul Gel goodPlaneExtension goodPlaneSplitting coefRep upperRadicalLattice_eq)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
  (Phi PhiInv Phi_PhiInv PhiInv_Phi levelRep_Phi Mk goodPlaneEdgeCocycle edgeVal)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (goodPlaneEdgeH2 goodPlaneEdgeH2_apply goodPlaneEdge hH_conj psiG)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₀)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains (leviCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (invT badLevi swapZ badDualLevi badDualLevi_relation badFrame uCocycle_leviCocycle_bad wBad PsiBad
    upperTotalBad upperTotalBad_eq badX' badXOdd' binarySwap binarySwapVar binarySwapVar_action_twist
    swap_conj_conj swapUnit levi_relation_complex binarySwap_homogeneousAction
    homogeneousAction_even_twist coord_upper_eq_of_shift asUp eq_of_closed eq_sub_of_closed)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
  (cocycle_vec3 relCocycleOn relCocycleOn_apply levi_identity relOn relOn_H2)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad

/-! ### Elementary lemmas -/

/-- Composition of the coefficient actions. -/
theorem rho_mul (n : ℕ) (a b : RationalGL3) (w : HomogeneousPoly n) :
    ρn n a (ρn n b w) = ρn n (a * b) w :=
  TernaryPeriodPolynomials.LevelThree.GoodPlaneConj.rho_apply_apply (ρn n) a b w

/-- The radical lattice of the standard good-plane coordinates, as a subgroup of `GL₃(ℚ)`. -/
abbrev planeRad : Subgroup RationalGL3 := upperRadicalLattice.range

/-- **The value of a `U`-equivariant one-cocycle on `(w, u w)`** in terms of its values at the
base vertex. -/
theorem ucocycle_base_change {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ RationalGL3 V} {U : Subgroup RationalGL3}
    {f : (Fin 2 → RationalGL3) → V} (hf : UCocycle ρ U f) {u : RationalGL3} (hu : u ∈ U)
    (w : RationalGL3) : f ![w, u * w] = f ![1, u] + (ρ u (f ![1, w]) - f ![1, w]) := by
  have c1 := hf.2 ![1, w, u * w]
  have c2 := hf.2 ![1, u, u * w]
  have e := hf.1 u hu 1 w
  rw [mul_one] at e
  change f ![w, u * w] - f ![1, u * w] + f ![1, w] = 0 at c1
  change f ![u, u * w] - f ![1, u * w] + f ![1, u] = 0 at c2
  rw [e] at c2
  have s1 := eq_sub_of_closed c1
  have s2 := eq_of_closed c2
  rw [s1, s2]
  abel

/-- The conjugation of a displayed triple of vertices. -/
theorem vec3_mul' (g a b c : RationalGL3) :
    (fun i => g * (![a, b, c] : Fin 3 → RationalGL3) i) = ![g * a, g * b, g * c] := by
  funext i
  fin_cases i <;> rfl

/-- The Levi element of `Λ_G` normalizes the standard radical lattice. -/
theorem Pg_normalizes (m : binaryArithmeticLevel) :
    ∀ u ∈ planeRad, Pg 0 m 1 * u * (Pg 0 m 1)⁻¹ ∈ planeRad := by
  rintro u ⟨p, rfl⟩
  have e1 : Pg 0 m 1 * Pg p.toAdd 1 1 = Pg (act m 1 p.toAdd) 1 1 * Pg 0 m 1 := by
    rw [Pg_mul, Pg_mul]
    simp [act_zero]
  refine ⟨Multiplicative.ofAdd (act m 1 p.toAdd), ?_⟩
  rw [upperRadicalLattice_eq, upperRadicalLattice_eq, eq_mul_inv_iff_mul_eq, toAdd_ofAdd]
  exact e1.symm

/-! ### The plane cocycle at the dual plane -/

/-- The dual plane of the bad line is `longWeyl ⟨e₀, e₁⟩`. -/
theorem dualFlag_eq (n : ℕ) :
    (dualityData n trivialCharacter).dualFlag L₀ = (QuotientGroup.mk longWeyl : Flags .plane) :=
  CuspDualL2.dualFlag_L₀

/-- Equivariance of a plane cocycle of the maximal stratum under the arithmetic level. -/
theorem plane_smul {n : ℕ}
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (g : RationalGL3) (hg : g ∈ rationalLevel) (x : Fin 3 → RationalGL3) (f : Flags .plane) :
    y.val.val (fun i => g * x i) f =
      ρn n g (y.val.val x (g⁻¹ • f)) := by
  have h := congrFun (y.val.property ⟨g, hg⟩ x) f
  change y.val.val (fun i => g * x i) f =
    rationalCoefficientComponent n trivialCharacter g (y.val.val x (g⁻¹ • f)) at h
  exact h

/-- The value of a plane cocycle at the reference good-plane flag in terms of its value at the dual
plane of the bad line. -/
theorem plane_at_cusp {n : ℕ}
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (x : Fin 3 → RationalGL3) :
    y.val.val x (cuspFlag .plane true) =
      ρn n swapQ⁻¹ (y.val.val (fun i => swapQ * x i) (QuotientGroup.mk longWeyl)) := by
  have h := plane_smul y swapQ swapQ_mem_level x (QuotientGroup.mk longWeyl)
  have hf : swapQ⁻¹ • (QuotientGroup.mk longWeyl : Flags .plane) = cuspFlag .plane true := by
    rw [inv_smul_eq_iff]
    exact swapQ_smul_cuspFlag.symm
  rw [hf] at h
  rw [h, rho_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- **The cocycle of the good-plane stabilizer in block coordinates** attached to a plane cocycle of
the maximal stratum: the conjugation by `g_F` of its value at the reference good-plane flag. -/
def cocycleAtGoodPlane (n : ℕ)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)) :
    cocycles ΛG (ρn n) :=
  TernaryPeriodPolynomials.LevelThree.GoodPlaneConj.conjCycle
    (rationalCoefficientComponent n trivialCharacter) gF (cuspLevel .plane true) ΛG hH_conj
    (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .plane true) y)

/-- The Shapiro coordinate of a plane class at the good-plane cusp, in block coordinates. -/
theorem psiG_cuspRes {n : ℕ}
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)) :
    psiG (n := n) (cuspRes n trivialCharacter .plane true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) =
      classOf ΛG (ρn n) (cocycleAtGoodPlane n y) := rfl

/-- **The values of the block cocycle**: `D(x) = ρ(τ⁻¹) y(τ x)(F)`. -/
theorem cocycleAtGoodPlane_apply {n : ℕ}
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (x : Fin 3 → RationalGL3) :
    (cocycleAtGoodPlane n y).val.val x =
      ρn n tauF⁻¹ (y.val.val (fun i => tauF * x i) (QuotientGroup.mk longWeyl)) := by
  have h := plane_at_cusp y (fun i => gF * x i)
  change ρn n gF⁻¹ (y.val.val (fun i => gF * x i) (cuspFlag .plane true)) = _
  rw [h, rho_mul]
  have e1 : gF⁻¹ * swapQ⁻¹ = tauF⁻¹ := (mul_inv_rev swapQ gF).symm
  have e2 : (fun i => swapQ * (gF * x i)) = fun i => tauF * x i :=
    funext fun i => (mul_assoc swapQ gF (x i)).symm
  rw [e1, e2]

/-- The values of the block cocycle on displayed triples. -/
theorem cocycleAtGoodPlane_apply3 {n : ℕ}
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (a b c : RationalGL3) :
    (cocycleAtGoodPlane n y).val.val ![a, b, c] =
      ρn n tauF⁻¹ (y.val.val ![tauF * a, tauF * b, tauF * c] (QuotientGroup.mk longWeyl)) := by
  rw [cocycleAtGoodPlane_apply, vec3_mul']

/-! ### The transported primitive -/

/-- **The primitive of the block cocycle** obtained from the primitive `θ_U` of the plane cocycle of
the fiber integration: `ω_G(a, b) = ρ(τ⁻¹) θ_U(φ(τ a), φ(τ b))`. -/
def omegaG (n : ℕ) (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) :
    (Fin 2 → RationalGL3) → HomogeneousPoly n :=
  fun x => ρn n tauF⁻¹ (θU ![dualInvolution (tauF * x 0), dualInvolution (tauF * x 1)])

/-- `φ(τ u(p) x) = u_L(σ p) φ(τ x)`. -/
theorem phi_tau_upper (p : RadicalLattice) (x : RationalGL3) :
    dualInvolution (tauF * (upperRadicalLattice p * x)) =
      radL p * dualInvolution (tauF * x) := by
  have h := tau_upper p
  calc dualInvolution (tauF * (upperRadicalLattice p * x))
      = dualInvolution ((tauF * upperRadicalLattice p * tauF⁻¹) * (tauF * x)) :=
        congrArg dualInvolution (by group)
    _ = dualInvolution (dualInvolution (radL p) * (tauF * x)) := by rw [h]
    _ = radL p * dualInvolution (tauF * x) := by rw [map_mul, dualInvolution_involutive]

/-- **`ω_G` is a primitive of the block cocycle.** -/
theorem omegaG_d {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane)) :
    ∀ a b c, differentialOneRaw (omegaG n θU) ![a, b, c] =
      (cocycleAtGoodPlane n y).val.val ![a, b, c] := by
  intro a b c
  have h1 := hF.thetaU_d (dualInvolution (tauF * a)) (dualInvolution (tauF * b))
    (dualInvolution (tauF * c))
  have h2 : η ![dualInvolution (tauF * a), dualInvolution (tauF * b), dualInvolution (tauF * c)] =
      y.val.val ![dualInvolution (dualInvolution (tauF * a)), dualInvolution (dualInvolution (tauF * b)),
        dualInvolution (dualInvolution (tauF * c))] (QuotientGroup.mk longWeyl) := hη _
  simp only [dualInvolution_involutive] at h2
  have h1' : θU ![dualInvolution (tauF * b), dualInvolution (tauF * c)] -
      θU ![dualInvolution (tauF * a), dualInvolution (tauF * c)] +
      θU ![dualInvolution (tauF * a), dualInvolution (tauF * b)] =
      η ![dualInvolution (tauF * a), dualInvolution (tauF * b), dualInvolution (tauF * c)] := h1
  change ρn n tauF⁻¹ (θU ![dualInvolution (tauF * b), dualInvolution (tauF * c)]) -
      ρn n tauF⁻¹ (θU ![dualInvolution (tauF * a), dualInvolution (tauF * c)]) +
      ρn n tauF⁻¹ (θU ![dualInvolution (tauF * a), dualInvolution (tauF * b)]) = _
  rw [← map_sub, ← map_add, h1', h2, cocycleAtGoodPlane_apply3]

/-- **`ω_G` is equivariant over the standard radical lattice.** -/
theorem omegaG_equiv {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) :
    ∀ g ∈ planeRad, ∀ a b, omegaG n θU ![g * a, g * b] = ρn n g (omegaG n θU ![a, b]) := by
  rintro g ⟨p, rfl⟩ a b
  change ρn n tauF⁻¹ (θU ![dualInvolution (tauF * (upperRadicalLattice p * a)),
      dualInvolution (tauF * (upperRadicalLattice p * b))]) =
    ρn n (upperRadicalLattice p) (ρn n tauF⁻¹ (θU ![dualInvolution (tauF * a),
      dualInvolution (tauF * b)]))
  rw [phi_tau_upper, phi_tau_upper, hF.thetaU_eq (radL p) (radL_mem p)]
  change ρn n tauF⁻¹ (ρn n (dualInvolution (radL p)) (θU ![dualInvolution (tauF * a),
      dualInvolution (tauF * b)])) = _
  rw [← tau_upper p, rho_mul, rho_mul]
  have e : tauF⁻¹ * (tauF * upperRadicalLattice p * tauF⁻¹) = upperRadicalLattice p * tauF⁻¹ := by
    group
  rw [e]

/-- **The relative representative of the block cocycle** over the standard radical lattice. -/
def relG {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane)) :
    relativeTwoCocycles goodPlaneExtension.inl (coefRep n) :=
  relOn ΛG (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y) (omegaG_d hF y hη) (omegaG_equiv hF)
    goodPlaneExtension.inl (fun p => ⟨p, rfl⟩)

/-- The relative representative has the class of the block cocycle. -/
theorem relG_H2 {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane)) :
    groupCohomology.H2π (coefRep n) (relG hF y hη).val =
      groupCohomology.H2π (coefRep n) (ambientCocycleToGroup ΛG (ρn n) (cocycleAtGoodPlane n y)) :=
  relOn_H2 ΛG (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y) (omegaG_d hF y hη)
    (omegaG_equiv hF) goodPlaneExtension.inl (fun p => ⟨p, rfl⟩)

/-- **The good-plane edge of the Shapiro coordinate is the class of the edge cocycle of the
relative representative.** -/
theorem goodPlaneEdge_cusp_eq {n : ℕ} (hn : 0 < n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane)) :
    goodPlaneEdge hn (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) =
      qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle (relG hF y hη)) :=
  (congrArg (goodPlaneEdgeH2 hn) (psiG_cuspRes y)).trans
    (goodPlaneEdgeH2_apply hn (cocycleAtGoodPlane n y) (relG hF y hη) (relG_H2 hF y hη))

/-! ### The Levi identity on `Λ_G` -/

/-- The mixed radical value of the relative representative at the Levi element `P(0, κ(m), 1)`. -/
def edgeTerm (n : ℕ) (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (m : binaryArithmeticLevel) (p : RadicalLattice) : HomogeneousPoly n :=
  relCocycleOn ΛG (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y)
      (goodPlaneSplitting (m, 1),
        goodPlaneExtension.inl (splitRadicalInput goodPlaneSplitting (m, 1) p)) -
    relCocycleOn ΛG (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y)
      (goodPlaneExtension.inl p, goodPlaneSplitting (m, 1))

/-- The edge cocycle of the relative representative is `edgeTerm`. -/
theorem splitEdgeCycle_relG {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (m : binaryArithmeticLevel) (p : RadicalLattice) :
    (splitEdgeCycle goodPlaneSplitting (coefRep n) (m, 1) (relG hF y hη) p : HomogeneousPoly n) =
      edgeTerm n θU y m p :=
  rfl

/-- **The Levi identity** for the edge cochain of the relative representative of the block cocycle. -/
theorem edge_add_levi_plane {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (m : binaryArithmeticLevel) (p : RadicalLattice) :
    edgeTerm n θU y m p +
        leviCocycle (ρn n) (omegaG n θU) (Pg 0 m 1)⁻¹ ![1, upperRadicalLattice p] =
      ρn n (upperRadicalLattice p)
          (-(ρn n (Pg 0 m 1) (leviCocycle (ρn n) (omegaG n θU) (Pg 0 m 1) ![1, (Pg 0 m 1)⁻¹]))) -
        (-(ρn n (Pg 0 m 1) (leviCocycle (ρn n) (omegaG n θU) (Pg 0 m 1) ![1, (Pg 0 m 1)⁻¹]))) := by
  have hd := omegaG_d hF y hη
  have key := levi_identity (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y).val.val hd
    (omegaG_equiv hF) (k := Pg 0 m 1)
    (cocycle_vec3 ΛG (ρn n) (cocycleAtGoodPlane n y) (Gel 0 m 1).property)
    (Pg_normalizes m) (u := upperRadicalLattice p)
    (u'' := (goodPlaneExtension.inl (splitRadicalInput goodPlaneSplitting (m, 1) p)).val)
    ⟨p, rfl⟩ ⟨_, rfl⟩
    (congrArg Subtype.val (splitRadicalInput_commute goodPlaneSplitting (m, 1) p))
  unfold edgeTerm
  rw [relCocycleOn_apply ΛG (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y) hd,
    relCocycleOn_apply ΛG (ρn n) (omegaG n θU) (cocycleAtGoodPlane n y) hd]
  exact key

/-! ### The Levi cocycle through the frame -/

/-- **The Levi cocycle of the transported primitive** is the transport of the Levi cocycle of
`θ_U` at the element `h'` with `φ(h') = τ h τ⁻¹`. -/
theorem leviG_eq {n : ℕ} (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) (h h' : RationalGL3)
    (hh : dualInvolution h' = tauF * h * tauF⁻¹) (a b : RationalGL3) :
    leviCocycle (ρn n) (omegaG n θU) h ![a, b] =
      ρn n tauF⁻¹ (leviCocycle (dualRep (dualityData n trivialCharacter)) θU h'
        ![dualInvolution (tauF * a), dualInvolution (tauF * b)]) := by
  have hv : ∀ x, h' * dualInvolution (tauF * x) = dualInvolution (tauF * (h * x)) := fun x => by
    have e : h' = dualInvolution (tauF * h * tauF⁻¹) := by
      rw [← hh, dualInvolution_involutive]
    rw [e, ← map_mul]
    exact congrArg dualInvolution (by group)
  have eg : h⁻¹ * tauF⁻¹ = tauF⁻¹ * dualInvolution h'⁻¹ := by
    rw [map_inv, hh]
    group
  have key : ∀ w : HomogeneousPoly n,
      ρn n h⁻¹ (ρn n tauF⁻¹ w) = ρn n tauF⁻¹ (ρn n (dualInvolution h'⁻¹) w) := fun w => by
    rw [rho_mul, rho_mul, eg]
  change ρn n h⁻¹ (ρn n tauF⁻¹ (θU ![dualInvolution (tauF * (h * a)),
        dualInvolution (tauF * (h * b))])) -
      ρn n tauF⁻¹ (θU ![dualInvolution (tauF * a), dualInvolution (tauF * b)]) =
    ρn n tauF⁻¹ (ρn n (dualInvolution h'⁻¹) (θU ![h' * dualInvolution (tauF * a),
        h' * dualInvolution (tauF * b)]) -
      θU ![dualInvolution (tauF * a), dualInvolution (tauF * b)])
  rw [hv a, hv b, map_sub, key]

/-- The dual Levi element at the transported Levi element. -/
theorem hh_levi (γ : binaryArithmeticLevel) :
    dualInvolution (badLevi γ)⁻¹ = tauF * (Pg 0 (alpha γ) 1)⁻¹ * tauF⁻¹ := by
  rw [map_inv, ← tau_levi γ]
  group

/-- **Decomposition of the Levi cocycle of the transported primitive** on the radical lattice. -/
theorem levi_plane_decomp {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (γ : binaryArithmeticLevel) (p : RadicalLattice) :
    leviCocycle (ρn n) (omegaG n θU) (Pg 0 (alpha γ) 1)⁻¹ ![1, upperRadicalLattice p] =
      ρn n tauF⁻¹ (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹
          ![1, radL p]) +
        (ρn n (upperRadicalLattice p) (ρn n tauF⁻¹
            (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹
              ![1, dualInvolution (tauF * 1)])) -
          ρn n tauF⁻¹ (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹
            ![1, dualInvolution (tauF * 1)])) := by
  have hA' := (uCocycle_leviCocycle_bad hF γ).2
  rw [leviG_eq θU _ _ (hh_levi γ) 1 (upperRadicalLattice p)]
  have hφ : dualInvolution (tauF * upperRadicalLattice p) =
      radL p * dualInvolution (tauF * 1) := by
    have h := phi_tau_upper p 1
    rwa [mul_one] at h
  have hx : ∀ X : HomogeneousPoly n,
      ρn n tauF⁻¹ (dualRep (dualityData n trivialCharacter) (radL p) X) =
        ρn n (upperRadicalLattice p) (ρn n tauF⁻¹ X) := fun X => by
    change ρn n tauF⁻¹ (ρn n (dualInvolution (radL p)) X) = _
    rw [← tau_upper p, rho_mul, rho_mul,
      show tauF⁻¹ * (tauF * upperRadicalLattice p * tauF⁻¹) = upperRadicalLattice p * tauF⁻¹ by
        group]
  rw [hφ, ucocycle_base_change hA' (radL_mem p) (dualInvolution (tauF * 1)), map_add, map_sub, hx]

/-- The constant of the coboundary in the identity for the edge cocycle. -/
def shiftVec {n : ℕ} (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) (γ : binaryArithmeticLevel) :
    HomogeneousPoly n :=
  -(ρn n (Pg 0 (alpha γ) 1) (leviCocycle (ρn n) (omegaG n θU) (Pg 0 (alpha γ) 1)
      ![1, (Pg 0 (alpha γ) 1)⁻¹])) -
    ρn n tauF⁻¹ (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹
      ![1, dualInvolution (tauF * 1)])

/-- **The cocycle of the radical lattice** attached to the Levi cocycle of `θ_U`: the Levi translate
by `q` of the cocycle `wBad`, with the sign. -/
def zPlane {n : ℕ} {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  -(upperRadicalCocycleLevi n swapZ (wBad n hg))

/-- The values of `zPlane`. -/
theorem zPlane_apply {n : ℕ} {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) (p : RadicalLattice) :
    (zPlane hg p : HomogeneousPoly n) = -(ρn n tauF⁻¹ (g ![1, radL p])) := by
  have e : ρn n tauF⁻¹ (g ![1, radL p]) = ρn n swapQ (ρn n badFrame⁻¹ (g ![1, radL p])) := by
    rw [rho_mul, tauF_inv_eq]
  rw [e]
  rfl

/-- The value of `zPlane` as a polynomial. -/
def zPlaneV {n : ℕ} {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) (p : RadicalLattice) :
    HomogeneousPoly n :=
  zPlane hg p

theorem zPlaneV_apply {n : ℕ} {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) (p : RadicalLattice) :
    zPlaneV hg p = -(ρn n tauF⁻¹ (g ![1, radL p])) :=
  zPlane_apply hg p

/-- **The edge cocycle differs from `zPlane` by a coboundary of the radical lattice.** -/
theorem edgeCycle_shift {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (γ : binaryArithmeticLevel) (p : RadicalLattice) :
    (splitEdgeCycle goodPlaneSplitting (coefRep n) (alpha γ, 1) (relG hF y hη) p :
        HomogeneousPoly n) =
      zPlaneV (uCocycle_leviCocycle_bad hF γ).2 p +
        (ρn n (upperRadicalLattice p) (shiftVec θU γ) - shiftVec θU γ) := by
  have key := edge_add_levi_plane hF y hη (alpha γ) p
  have dec := levi_plane_decomp hF γ p
  have e1 := eq_sub_of_add_eq key
  rw [splitEdgeCycle_relG hF y hη (alpha γ) p, e1, dec, zPlaneV_apply]
  simp only [shiftVec, map_sub, map_neg]
  abel

/-- **The coordinate of the edge cocycle at the Levi element `P(0, κ(α γ), 1)`** is minus the Levi
translate by the exchange matrix of the coordinate of the Levi cocycle of `θ_U`. -/
theorem edgeVal_alpha {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (γ : binaryArithmeticLevel) :
    edgeVal (relG hF y hη) (alpha γ, 1) =
      -(Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
        (upperTotalBad n (leviCocycle (dualRep (dualityData n trivialCharacter)) θU
          (badLevi γ)⁻¹))) := by
  have hA' := (uCocycle_leviCocycle_bad hF γ).2
  change upperRadicalCocycleCoordinate n
    (splitEdgeCycle goodPlaneSplitting (coefRep n) (alpha γ, 1) (relG hF y hη)) = _
  rw [coord_upper_eq_of_shift n
      (splitEdgeCycle goodPlaneSplitting (coefRep n) (alpha γ, 1) (relG hF y hη)) (zPlane hA')
      (asUp n (shiftVec θU γ)) (fun p => edgeCycle_shift hF y hη γ p),
    zPlane, map_neg, upperRadicalCocycleCoordinate_equivariant, upperTotalBad_eq n hA']

/-! ### The comparison of the coefficient modules -/

/-- The involution `Sym^{n+1}(σ) ⊗ det⁻¹` of the binary forms is an involution. -/
theorem act_swap_involutive (n : ℕ) (x : Binary.HomogeneousPoly (n + 1)) :
    Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
        (Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
          x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, swapZ_mul_self, map_one, map_one,
    Module.End.one_apply]

/-- **The comparison map** `E = σ_var ∘ rot ∘ Sym(σ) ∘ Φ⁻¹` from the coefficients
`Sym^{n+1} ⊗ det⁻¹` of the good-plane edge to the coefficients of the bridge. -/
def planeComparison (n : ℕ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (binarySwapVar (n + 1)).comp ((binarySwap (n + 1)).comp
    ((Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)).comp
      (PhiInv n)))

/-- The dual Levi element intertwines the exchange `σ` with the inverse transpose. -/
theorem badDualLevi_mul_swapZ (γ : binaryArithmeticLevel) :
    badDualLevi γ * swapZ = swapZ * invT γ.1 := by
  unfold badDualLevi
  rw [mul_assoc (swapZ * invT γ.1) swapZ swapZ, swapZ_mul_self, mul_one]

/-- The matrix relation behind the rotation of the dual coordinate. -/
theorem levi_relation_swap (γ : binaryArithmeticLevel) :
    ((swapUnit * binaryIntegralComplex γ.1 * swapUnit⁻¹ : Binary.GL2) :
      Matrix (Fin 2) (Fin 2) ℂ) *
      ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ) : Binary.GL2) :
        Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 1 :=
  levi_relation_complex γ.1 (badDualLevi γ) (badDualLevi_relation γ)

/-- **The rotation of the dual plane coordinate is equivariant** (even `n`): the exchange of the
variables composed with the rotation intertwines the action of the dual Levi element with `γ` on
`Sym^{n+1}`. -/
theorem eplane_equivariant (n : ℕ) (heven : Even n) (γ : binaryArithmeticLevel)
    (x : Binary.HomogeneousPoly (n + 1)) :
    binarySwapVar (n + 1) (binarySwap (n + 1)
        (Binary.homogeneousAction (n + 1) (-1)
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ)) x)) =
      binaryArithmeticRepresentation n γ (binarySwapVar (n + 1) (binarySwap (n + 1) x)) := by
  have hEven : Even (((n + 1 : ℕ) : ℤ) - (-1) - 0) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨(k : ℤ) + 1, by omega⟩
  rw [binarySwap_homogeneousAction (n + 1) (-1) (swapUnit * binaryIntegralComplex γ.1 * swapUnit⁻¹)
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ)) (levi_relation_swap γ),
    binarySwapVar_action_twist, swap_conj_conj]
  exact LinearMap.congr_fun
    (homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1)) 0 hEven γ.1) _

/-- **The rotation of the dual plane coordinate is equivariant** (odd `n`): it intertwines the
action of the dual Levi element with `γ` on `Sym^{n+1} ⊗ det⁻¹`. -/
theorem eplane_equivariant_odd (n : ℕ) (hodd : Odd n) (γ : binaryArithmeticLevel)
    (x : Binary.HomogeneousPoly (n + 1)) :
    binarySwapVar (n + 1) (binarySwap (n + 1)
        (Binary.homogeneousAction (n + 1) (-1)
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ)) x)) =
      levelRep (n + 1) (-1) γ (binarySwapVar (n + 1) (binarySwap (n + 1) x)) := by
  have hEven : Even (((n + 1 : ℕ) : ℤ) - (-1) - (-1)) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨(k : ℤ) + 2, by omega⟩
  rw [binarySwap_homogeneousAction (n + 1) (-1) (swapUnit * binaryIntegralComplex γ.1 * swapUnit⁻¹)
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ)) (levi_relation_swap γ),
    binarySwapVar_action_twist, swap_conj_conj]
  exact LinearMap.congr_fun
    (homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1)) (-1) hEven γ.1) _

/-- **The comparison map transports the coefficient action at `α γ` to the action of the dual Levi
element on the rotated coordinate.** -/
theorem planeComparison_levelRep (n : ℕ) (γ : binaryArithmeticLevel)
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeComparison n (levelRep (n + 1) (-1) (alpha γ) v) =
      binarySwapVar (n + 1) (binarySwap (n + 1)
        (Binary.homogeneousAction (n + 1) (-1)
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ))
          (Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
            (PhiInv n v)))) := by
  have h1 : PhiInv n (levelRep (n + 1) (-1) (alpha γ) v) =
      Mk n (alpha γ) (PhiInv n v) := by
    have h := levelRep_Phi n (alpha γ) (PhiInv n v)
    rw [Phi_PhiInv] at h
    rw [h, PhiInv_Phi]
  have h2 : Mk n (alpha γ) (PhiInv n v) =
      Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ.1))
        (PhiInv n v) :=
    congrArg (fun A : GL2Z => Binary.homogeneousAction (n + 1) (-1) (binaryIntegralComplex A)
      (PhiInv n v)) (kap_alpha γ)
  have hGL : Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ *
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ.1) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ) *
        Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ := by
    rw [← map_mul, ← map_mul, badDualLevi_mul_swapZ]
  have h3 : ∀ u : Binary.HomogeneousPoly (n + 1),
      Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
          (Binary.homogeneousAction (n + 1) (-1)
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ.1)) u) =
        Binary.homogeneousAction (n + 1) (-1)
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ))
          (Binary.homogeneousAction (n + 1) (-1)
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ) u) := fun u => by
    calc Binary.homogeneousAction (n + 1) (-1) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ)
          (Binary.homogeneousAction (n + 1) (-1)
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ.1)) u)
        = Binary.homogeneousAction (n + 1) (-1)
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ *
            Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (invT γ.1)) u := by
          rw [map_mul, Module.End.mul_apply]
      _ = Binary.homogeneousAction (n + 1) (-1)
          (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) (badDualLevi γ) *
            Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) swapZ) u := by rw [hGL]
      _ = _ := by rw [map_mul, Module.End.mul_apply]
  simp only [planeComparison, LinearMap.comp_apply]
  rw [h1, h2, h3]

/-- **The comparison map intertwines the coefficients of the good-plane edge at `α γ` with the
coefficients `Sym^{n+1}` of the even-degree bridge at `γ`.** -/
theorem planeComparison_intertwines (n : ℕ) (heven : Even n) (γ : binaryArithmeticLevel)
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeComparison n (levelRep (n + 1) (-1) (alpha γ) v) =
      binaryArithmeticRepresentation n γ (planeComparison n v) := by
  rw [planeComparison_levelRep, eplane_equivariant n heven]
  rfl

/-- **The comparison map intertwines the coefficients of the good-plane edge at `α γ` with the
coefficients `Sym^{n+1} ⊗ det⁻¹` of the odd-degree bridge at `γ`.** -/
theorem planeComparison_intertwines_odd (n : ℕ) (hodd : Odd n) (γ : binaryArithmeticLevel)
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeComparison n (levelRep (n + 1) (-1) (alpha γ) v) =
      levelRep (n + 1) (-1) γ (planeComparison n v) := by
  rw [planeComparison_levelRep, eplane_equivariant_odd n hodd]
  rfl

/-! ### The identification -/

/-- **The coordinate of the Levi cocycle of the dual plane is minus the transported good-plane edge
cocycle**: `Ψ(A'(k_γ⁻¹)) = - E (goodPlaneEdgeCocycle c (α γ))`, exactly (any parity). -/
theorem PsiBad_apply {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (γ : binaryArithmeticLevel) :
    PsiBad n (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹) =
      -(planeComparison n ((goodPlaneEdgeCocycle (relG hF y hη)).val (alpha γ))) := by
  have h1 : PsiBad n (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹) =
      binarySwapVar (n + 1) (binarySwap (n + 1)
        (upperTotalBad n (leviCocycle (dualRep (dualityData n trivialCharacter)) θU
          (badLevi γ)⁻¹))) := rfl
  have h2 : (goodPlaneEdgeCocycle (relG hF y hη)).val (alpha γ) =
      Phi n (edgeVal (relG hF y hη) (alpha γ, 1)) := rfl
  rw [h1, h2, edgeVal_alpha hF y hη γ]
  simp only [planeComparison, LinearMap.comp_apply]
  rw [PhiInv_Phi, map_neg, act_swap_involutive, map_neg, map_neg, neg_neg]

/-- **The cocycle `badX'` of the even-degree bridge is minus the transported good-plane edge
cocycle**: `badX' γ = - E (goodPlaneEdgeCocycle c (α γ))`, exactly. -/
theorem badX'_apply {n : ℕ} (heven : Even n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (γ : binaryArithmeticLevel) :
    (badX' heven hF).val γ =
      -(planeComparison n ((goodPlaneEdgeCocycle (relG hF y hη)).val (alpha γ))) :=
  PsiBad_apply hF y hη γ

/-- **The cocycle `badXOdd'` of the odd-degree bridge is minus the transported good-plane edge
cocycle**: `badXOdd' γ = - E (goodPlaneEdgeCocycle c (α γ))`, exactly. -/
theorem badXOdd'_apply {n : ℕ} (hodd : Odd n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (γ : binaryArithmeticLevel) :
    (badXOdd' hodd hF).val γ =
      -(planeComparison n ((goodPlaneEdgeCocycle (relG hF y hη)).val (alpha γ))) :=
  PsiBad_apply hF y hη γ

/-! ### Parabolicity -/

/-- A crossed cocycle whose class is parabolic is parabolic (generic form). -/
theorem mem_parabolicCrossed_of_qcls {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ binaryArithmeticLevel V) (e : crossedCocycles ρ)
    (h : qcls ρ e ∈ ParabolicDuality.LevelThree.parabolicCrossedH1 ρ) :
    e ∈ ParabolicDuality.LevelThree.parabolicCrossed ρ :=
  ParabolicDuality.LevelThree.mem_parabolicCrossed_of_mem ρ h

/-- **Transport of a coboundary condition through a comparison map.** -/
theorem pullback_coboundary {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (ρ₁ : Representation ℂ binaryArithmeticLevel V₁)
    (ρ₂ : Representation ℂ binaryArithmeticLevel V₂) (E : V₁ →ₗ[ℂ] V₂)
    (a : binaryArithmeticLevel → binaryArithmeticLevel)
    (hE : ∀ γ v, E (ρ₁ (a γ) v) = ρ₂ γ (E v)) (e : crossedCocycles ρ₁) (x : crossedCocycles ρ₂)
    (hx : ∀ γ, x.1 γ = -E (e.1 (a γ))) (γ g : binaryArithmeticLevel) (hg : a γ = g⁻¹) (u : V₁)
    (hu : e.1 g = ρ₁ g u - u) : x.1 γ = ρ₂ γ (-E u) - (-E u) := by
  have h1 : e.1 1 = 0 := by
    have h := e.2 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    exact add_eq_left.mp h.symm
  have h2 : e.1 g⁻¹ = -ρ₁ g⁻¹ (e.1 g) := by
    have h := e.2 g⁻¹ g
    rw [inv_mul_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have h3 : ρ₁ g⁻¹ (ρ₁ g u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h4 : E (ρ₁ g⁻¹ u) = ρ₂ γ (E u) := by
    rw [← hg]
    exact hE γ u
  rw [hx γ, hg, h2, hu, map_neg, map_sub, map_sub, h3, h4]
  simp only [map_neg]
  abel

/-- **A pulled-back crossed cocycle of a parabolic cocycle is parabolic.**  If `x γ = - E (e (α γ))`
with `E` intertwining the coefficients and `e` parabolic, then `x` is parabolic, because `α`
exchanges the two cusps. -/
theorem parabolic_pullback {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (ρ₁ : Representation ℂ binaryArithmeticLevel V₁)
    (ρ₂ : Representation ℂ binaryArithmeticLevel V₂) (E : V₁ →ₗ[ℂ] V₂)
    (hE : ∀ γ v, E (ρ₁ (alpha γ) v) = ρ₂ γ (E v)) (e : crossedCocycles ρ₁)
    (he : e ∈ ParabolicDuality.LevelThree.parabolicCrossed ρ₁) (x : crossedCocycles ρ₂)
    (hx : ∀ γ, x.1 γ = -E (e.1 (alpha γ))) :
    x ∈ ParabolicDuality.LevelThree.parabolicCrossed ρ₂ := by
  obtain ⟨⟨uT, huT⟩, ⟨uL, huL⟩⟩ := (ParabolicDuality.LevelThree.mem_parabolicCrossed_iff _ _).mp he
  refine (ParabolicDuality.LevelThree.mem_parabolicCrossed_iff _ _).mpr
    ⟨⟨-E uL, ?_⟩, ⟨-E uT, ?_⟩⟩
  · exact pullback_coboundary ρ₁ ρ₂ E alpha hE e x hx (upper 1) (lower 1) alpha_upper uL huL
  · exact pullback_coboundary ρ₁ ρ₂ E alpha hE e x hx (lower 1) (upper 1) alpha_lower uT huT

/-- **The good-plane edge cocycle of the relative representative is parabolic** when the Shapiro
coordinate of the plane class at the good-plane cusp is a local joint generalized eigenclass with a
small `T₂`-eigenvalue. -/
theorem goodPlaneEdgeCocycle_mem_parabolic {n : ℕ} (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TernaryPeriodPolynomials.Spectral.TpExistence.tp
      TernaryPeriodPolynomials.Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane))
    (hy : cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
      localJoint n trivialCharacter c .plane true) :
    goodPlaneEdgeCocycle (relG hF y hη) ∈
      ParabolicDuality.LevelThree.parabolicCrossed (levelRep (n + 1) (-1)) := by
  have hcls : qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle (relG hF y hη)) ∈
      ParabolicDuality.LevelThree.parabolicCrossedH1 (levelRep (n + 1) (-1)) := by
    rw [← goodPlaneEdge_cusp_eq (by omega : 0 < n) hF y hη]
    exact ParabolicDuality.LevelThree.goodPlaneEdge_mem_parabolicCrossedH1 n hn c hc hy
  exact mem_parabolicCrossed_of_qcls (levelRep (n + 1) (-1)) _ hcls

/-- The dual plane of the bad line, in the form of the fiber hypotheses. -/
theorem hη_flag {n : ℕ} {η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) :
    ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane) := fun x =>
  (hη x).trans (congrArg (fun F : Flags .plane => y.val.val ![dualInvolution (x 0),
    dualInvolution (x 1), dualInvolution (x 2)] F) (dualFlag_eq n))

/-- **`badX'` is a parabolic cocycle** (even degree) when the Shapiro coordinate of the plane class at
the good-plane cusp is a local joint generalized eigenclass with a small `T₂`-eigenvalue. -/
theorem badX'_mem_parabolicCrossed {n : ℕ} (hn : 1 ≤ n) (heven : Even n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TernaryPeriodPolynomials.Spectral.TpExistence.tp
      TernaryPeriodPolynomials.Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀))
    (hy : cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
      localJoint n trivialCharacter c .plane true) :
    badX' heven hF ∈
      ParabolicDuality.LevelThree.parabolicCrossed (binaryArithmeticRepresentation n) :=
  parabolic_pullback (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n) (planeComparison n)
    (planeComparison_intertwines n heven) _
    (goodPlaneEdgeCocycle_mem_parabolic hn c hc hF y (hη_flag y hη) hy) _
    (badX'_apply heven hF y (hη_flag y hη))

/-- **`badXOdd'` is a parabolic cocycle** (odd degree) when the Shapiro coordinate of the plane class
at the good-plane cusp is a local joint generalized eigenclass with a small `T₂`-eigenvalue. -/
theorem badXOdd'_mem_parabolicCrossed {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TernaryPeriodPolynomials.Spectral.TpExistence.tp
      TernaryPeriodPolynomials.Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀))
    (hy : cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
      localJoint n trivialCharacter c .plane true) :
    badXOdd' hodd hF ∈
      ParabolicDuality.LevelThree.parabolicCrossed (levelRep (n + 1) (-1)) :=
  parabolic_pullback (levelRep (n + 1) (-1)) (levelRep (n + 1) (-1)) (planeComparison n)
    (planeComparison_intertwines_odd n hodd) _
    (goodPlaneEdgeCocycle_mem_parabolic hn c hc hF y (hη_flag y hη) hy) _
    (badXOdd'_apply hodd hF y (hη_flag y hη))

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad

end
