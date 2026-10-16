module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EdgeSurjIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCosets

@[expose] public section


/-!
# The good-plane edge map is surjective

The good-plane stabilizer is the split extension `Λ = U ⋊ (Γ₁'(3) × ℤˣ)`, `U ≅ ℤ²` the upper radical,
with Levi section `(m, d) ↦ diag(κ(m), d)`.  Its edge map sends `H²(Λ, Sym^n)` to
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` through the radical coordinate and the transport `Φ = Sym^{n+1}(δ)`.

The gradient section `σ(Q) = (∂₀ Q, ∂₁ Q)` of the radical cohomology is equivariant for the whole
Levi group at the level of cocycles:
* for `d = 1` the Levi element `diag(κ(m), 1)` is the identity-plane Levi element of `κ(m)`, so
  `σ(Sym^{n+1}(κ m) Q) = diag(κ m, 1) · σ(Q)` (`EdgeSurjIdentity.cocycleSection_levi`);
* the element `z = diag(1, 1, -1)` inverts the radical, acts on `Sym^n` by `f ↦ -f(X₀, X₁, -X₂)` and
  anticommutes with the radical generators `-X₂ ∂ₖ`; the gradient pair is free of `X₂`, so
  `z · σ(Q) = σ(Q)` (`splitAction_unit_invariant`).
Hence every crossed one-cocycle `w` of `Γ₁'(3)` gives the strict family
`(m, d) ↦ σ(Φ⁻¹ w(m))`, whose mixed relative two-cocycle has edge cocycle exactly `w`.  The edge map
`H²(Λ, V) → H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` and the good-plane cusp edge `goodPlaneEdge` are therefore
surjective, hence bijective (`goodPlaneEdge_surjective`, `goodPlaneEdge_bijective`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjSplit
open TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjIdentity

namespace TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjGoodPlane

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (CuspH2)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates (P P_val)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets (icast)
open TernaryPeriodPolynomials.Spectral.AmbientHecke (liftCocycle ambientCocycleToGroup_lift)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneRestriction
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

variable (n : ℕ)

/-! ### The Levi elements with `d = 1` are identity-plane Levi elements -/

/-- The Levi section at `(m, 1)` is the identity-plane Levi element of `κ(m)`. -/
theorem secL_levi (m : binaryArithmeticLevel) :
    ((secL (m, 1) : ΛG) : RationalGL3) = arithmeticLevi (kap m) := by
  change P (icast 0) (integralEmbed (kap m)) (uq 1) = arithmeticLevi (kap m)
  rw [uq_one]
  exact (congrArg Subtype.val (IdentityPlaneEdge.splitting_eq (kap m))).symm

/-- The radical input of `(m, 1)` is the identity-plane radical input of `κ(m)`. -/
theorem splitRadicalInput_levi (m : binaryArithmeticLevel) (radical : RadicalLattice) :
    splitRadicalInput goodPlaneSplitting (m, 1) radical = upperLeviLatticeInput (kap m) radical := by
  apply upperRadicalLattice_injective
  have commute := congrArg Subtype.val (splitRadicalInput_commute goodPlaneSplitting (m, 1) radical)
  change upperRadicalLattice radical * ((secL (m, 1) : ΛG) : RationalGL3) =
    ((secL (m, 1) : ΛG) : RationalGL3) *
      upperRadicalLattice (splitRadicalInput goodPlaneSplitting (m, 1) radical) at commute
  rw [secL_levi] at commute
  exact mul_left_cancel (commute.symm.trans (upperLeviLatticeInput_conjugation (kap m) radical))

/-- On radical cocycles, `(m, 1)` acts as the identity-plane Levi element `κ(m)`. -/
theorem splitAction_levi_one (m : binaryArithmeticLevel)
    (cycle : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (coefRep n))) :
    splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, 1) cycle =
      upperRadicalCocycleLevi n (kap m) cycle := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  have h2 := upperRadicalCocycleLevi_apply n (kap m) cycle radical
  refine (splitRadicalCocycleAction_apply goodPlaneSplitting (coefRep n) (m, 1) cycle radical).trans
    (Eq.trans ?_ h2.symm)
  rw [splitRadicalInput_levi]
  change rationalCoefficientComponent n trivialCharacter ((secL (m, 1) : ΛG) : RationalGL3) _ =
    rationalCoefficientComponent n trivialCharacter (arithmeticLevi (kap m)) _
  rw [secL_levi]
  rfl

/-! ### The element `z = diag(1, 1, -1)` -/

/-- The complexification of `z = diag(1, 1, -1)`. -/
theorem map_Pg_unit : GeneralLinearGroup.map (algebraMap ℚ ℂ) (Pg 0 1 (-1)) =
    planeLevi (1 : Binary.GL2) (-1 : ℂˣ) := by
  apply Units.ext
  ext i j
  have hB : integralEmbed (kap (1 : binaryArithmeticLevel)) = 1 := by simp
  have hd : ((uq (-1) : ℚˣ) : ℚ) = -1 := by
    rw [uq_val]
    simp
  change algebraMap ℚ ℂ ((P (icast 0) (integralEmbed (kap 1)) (uq (-1))).val i j) =
    planeBlock (1 : Binary.GL2).val (-1 : ℂˣ).val i j
  rw [hB, P_val, hd]
  fin_cases i <;> fin_cases j <;> simp [planeBlock, icast]

/-- The substitution `X₂ ↦ -X₂`. -/
abbrev unitSubstitution : Poly →ₐ[ℂ] Poly :=
  substitute (planeBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) (-1))

/-- `z` acts on `Sym^n` by `f ↦ -f(X₀, X₁, -X₂)`. -/
theorem rho_DK_val (v : HomogeneousPoly n) :
    ((coefRep n).ρ DK v).val = -unitSubstitution v.val := by
  change (IdentityPlaneCoordinate.ρn n (Pg 0 1 (-1)) v).val = _
  rw [IdentityPlaneCoordinate.rho_coe, map_Pg_unit, action_apply]
  have inverse : (((planeLevi (1 : Binary.GL2) (-1 : ℂˣ))⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) =
      planeBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) (-1) := by
    rw [planeLevi_inverse, planeLevi_value]
    simp
  have character : determinantCharacter (-1) (planeLevi (1 : Binary.GL2) (-1 : ℂˣ)) = -1 := by
    rw [planeLevi_determinantCharacter]
    simp
  rw [inverse, character]
  exact neg_one_smul ℂ _

theorem unitSubstitution_X_two (polynomial : Poly) :
    unitSubstitution (X 2 * polynomial) = -(X 2 * unitSubstitution polynomial) := by
  rw [map_mul, substitute_X, planeBlock_linearForm_third, map_neg, C_1]
  ring

theorem pderiv_unitSubstitution (coordinate : Fin 2) (polynomial : Poly) :
    pderiv coordinate.castSucc (unitSubstitution polynomial) =
      unitSubstitution (pderiv coordinate.castSucc polynomial) := by
  rw [pderiv_substitute_planeBlock_binary, Fin.sum_univ_two]
  fin_cases coordinate <;> simp <;> simp [Matrix.one_apply]

theorem unitSubstitution_lift (polynomial : Binary.Poly) :
    unitSubstitution (binaryPolynomialLift polynomial) = binaryPolynomialLift polynomial := by
  rw [substitute_planeBlock_lift, Binary.substitute_one]
  rfl

theorem rho_DK_involutive (v : HomogeneousPoly n) : (coefRep n).ρ DK ((coefRep n).ρ DK v) = v := by
  have h : (coefRep n).ρ DK * (coefRep n).ρ DK = 1 := by rw [← map_mul, DK_mul_self, map_one]
  exact LinearMap.congr_fun h v

theorem rho_DK_injective : Function.Injective ((coefRep n).ρ DK) := by
  intro first second equality
  rw [← rho_DK_involutive n first, ← rho_DK_involutive n second, equality]

/-- The coefficients of the inverse of a radical generator. -/
theorem generator_inv_combination {W : Type*} [AddCommGroup W] [Module ℂ W] (pair : Fin 2 → W)
    (coordinate : Fin 2) :
    ((((radicalLatticeGenerator coordinate)⁻¹).toAdd.1 : ℤ) : ℂ) • pair 0 +
        ((((radicalLatticeGenerator coordinate)⁻¹).toAdd.2 : ℤ) : ℂ) • pair 1 = -pair coordinate := by
  fin_cases coordinate <;> simp [radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]

theorem upperRadicalGenerator_val (coordinate : Fin 2) (v : HomogeneousPoly n) :
    (upperRadicalGenerator n coordinate v).val =
      (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc v.val) := rfl

theorem upperRadicalGenerator_neg_val (coordinate : Fin 2) (v : HomogeneousPoly n) :
    (-(upperRadicalGenerator n coordinate v)).val =
      -((-1 : ℂ) • (X 2 * pderiv coordinate.castSucc v.val)) := rfl

theorem rho_DK_anticommutes (coordinate : Fin 2) (v : HomogeneousPoly n) :
    upperRadicalGenerator n coordinate ((coefRep n).ρ DK v) =
      (coefRep n).ρ DK (-(upperRadicalGenerator n coordinate v)) := by
  apply Subtype.ext
  have h1 : ((coefRep n).ρ DK v).val = -unitSubstitution v.val := rho_DK_val n v
  have h2 : ((coefRep n).ρ DK (-(upperRadicalGenerator n coordinate v))).val =
      -unitSubstitution (-(upperRadicalGenerator n coordinate v)).val := rho_DK_val n _
  calc (upperRadicalGenerator n coordinate ((coefRep n).ρ DK v)).val
      = (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc ((coefRep n).ρ DK v).val) :=
        upperRadicalGenerator_val n coordinate _
    _ = (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc (-unitSubstitution v.val)) := by rw [h1]
    _ = -unitSubstitution (-((-1 : ℂ) • (X 2 * pderiv coordinate.castSucc v.val))) := by
        rw [map_neg (pderiv (R := ℂ) coordinate.castSucc), pderiv_unitSubstitution,
          map_neg unitSubstitution,
          map_smul, unitSubstitution_X_two]
        simp only [neg_neg, neg_one_smul, mul_neg]
    _ = -unitSubstitution (-(upperRadicalGenerator n coordinate v)).val := by
        rw [upperRadicalGenerator_neg_val]
    _ = ((coefRep n).ρ DK (-(upperRadicalGenerator n coordinate v))).val := h2.symm

/-- `z` anticommutes with the radical generators. -/
theorem rho_DK_intertwines (coordinate : Fin 2) :
    (upperRadicalGenerator n coordinate).comp ((coefRep n).ρ DK) =
      ((coefRep n).ρ DK).comp (latticeInfinitesimal (upperRadicalGenerator n 0)
        (upperRadicalGenerator n 1) (radicalLatticeGenerator coordinate)⁻¹) := by
  have combination : latticeInfinitesimal (upperRadicalGenerator n 0) (upperRadicalGenerator n 1)
      (radicalLatticeGenerator coordinate)⁻¹ = -upperRadicalGenerator n coordinate :=
    generator_inv_combination (fun index => upperRadicalGenerator n index) coordinate
  apply LinearMap.ext
  intro v
  exact (rho_DK_anticommutes n coordinate v).trans
    (congrArg ((coefRep n).ρ DK) (LinearMap.congr_fun combination v)).symm

/-- `z` acts by `-1` on the gradient pair. -/
theorem rho_DK_gradient (polynomial : Binary.HomogeneousPoly (n + 1)) (coordinate : Fin 2) :
    (coefRep n).ρ DK (binaryGradientPair polynomial coordinate) =
      -binaryGradientPair polynomial coordinate := by
  apply Subtype.ext
  rw [rho_DK_val]
  change -unitSubstitution (pderiv coordinate.castSucc (binaryPolynomialLift polynomial.val)) =
    -pderiv coordinate.castSucc (binaryPolynomialLift polynomial.val)
  rw [binaryPolynomialLift_pderiv, unitSubstitution_lift]

theorem splitRadicalInput_unit (radical : RadicalLattice) :
    splitRadicalInput goodPlaneSplitting (1, -1) radical = radical⁻¹ := by
  rw [LevelThree.GoodPlaneEdge.splitRadicalInput_apply, inv_one, act_one]
  apply Multiplicative.toAdd.injective
  simp

/-- **The gradient section is invariant under `z = diag(1, 1, -1)` at the level of cocycles.** -/
theorem splitAction_unit_invariant (polynomial : Binary.HomogeneousPoly (n + 1)) :
    splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (1, -1) (cocycleSection n polynomial) =
      cocycleSection n polynomial := by
  apply (upperRadicalCocycleEquiv n).injective
  apply Subtype.ext
  funext coordinate
  have gradient : upperRadicalCocyclePair n (cocycleSection n polynomial) = binaryGradientPair polynomial :=
    congrArg Subtype.val (toInfinitesimal_cocycleSection n polynomial)
  have key := latticeCocycle_direction_natural (upperRadicalLatticeRep n) (cocycleSection n polynomial)
    (upperRadicalGenerator n 0) (upperRadicalGenerator n 1)
    (upperRadicalCocyclePair n (cocycleSection n polynomial) 0)
    (upperRadicalCocyclePair n (cocycleSection n polynomial) 1)
    (upperRadicalGenerators_commute n) (upperRadicalCocyclePair_generator_closed (cocycleSection n polynomial))
    n n (upperRadicalGenerator_power_zero n 0) (upperRadicalGenerator_power_zero n 1)
    ((upperRadicalLatticeRep_first n).trans (exp_inst_irrel _ _ _))
    ((upperRadicalLatticeRep_second n).trans (exp_inst_irrel _ _ _))
    (upperRadicalCocyclePair_average (cocycleSection n polynomial) 0).symm
    (upperRadicalCocyclePair_average (cocycleSection n polynomial) 1).symm
    (upperRadicalGenerator n coordinate) ((coefRep n).ρ DK) (rho_DK_injective n)
    (radicalLatticeGenerator coordinate)⁻¹ (rho_DK_intertwines n coordinate) n
    (upperRadicalGenerator_power_zero n coordinate)
  rw [gradient] at key
  change upperRadicalCocyclePair n (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (1, -1)
      (cocycleSection n polynomial)) coordinate =
    upperRadicalCocyclePair n (cocycleSection n polynomial) coordinate
  rw [gradient]
  change (upperRadicalAverageEquiv n coordinate).symm ((coefRep n).ρ DK
      ((cocycleSection n polynomial) (splitRadicalInput goodPlaneSplitting (1, -1)
        (radicalLatticeGenerator coordinate)))) = binaryGradientPair polynomial coordinate
  rw [splitRadicalInput_unit]
  refine key.trans ?_
  exact (congrArg ((coefRep n).ρ DK) (generator_inv_combination (binaryGradientPair polynomial)
    coordinate)).trans ((map_neg _ _).trans
      ((congrArg Neg.neg (rho_DK_gradient n polynomial coordinate)).trans (neg_neg _)))

/-! ### Equivariance for the whole Levi group -/

/-- `Sym^{n+1} ⊗ det⁻¹` through `κ`, as a representation of the Levi group `Γ₁'(3) × ℤˣ`. -/
def levelW : Rep ℂ Levi :=
  Rep.of ((Binary.homogeneousAction (n + 1) (-1)).comp
    ((binaryIntegralComplex.comp kap).comp (MonoidHom.fst binaryArithmeticLevel ℤˣ)))

/-- The gradient section with values in the radical cocycles of the good-plane extension. -/
def goodSection : levelW n →ₗ[ℂ]
    groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (coefRep n)) :=
  cocycleSection n

theorem splitAction_unit (d : ℤˣ) (polynomial : Binary.HomogeneousPoly (n + 1)) :
    splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (1, d) (cocycleSection n polynomial) =
      cocycleSection n polynomial := by
  rcases Int.units_eq_one_or d with rfl | rfl
  · exact splitRadicalCocycleAction_one goodPlaneSplitting (coefRep n) _
  · exact splitAction_unit_invariant n polynomial

/-- **The gradient section is Levi-equivariant at the level of cocycles.** -/
theorem goodSection_equivariant (levi : Levi) (polynomial : levelW n) :
    goodSection n ((levelW n).ρ levi polynomial) =
      splitRadicalCocycleAction goodPlaneSplitting (coefRep n) levi (goodSection n polynomial) := by
  obtain ⟨m, d⟩ := levi
  show cocycleSection n (Binary.homogeneousAction (n + 1) (-1)
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (kap m)) polynomial) =
    splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) (cocycleSection n polynomial)
  have split : splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, d) (cocycleSection n polynomial) =
      splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (m, 1)
        (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) (1, d) (cocycleSection n polynomial)) := by
    have e : ((m, 1) : Levi) * (1, d) = (m, d) := by
      rw [Prod.mk_mul_mk, mul_one, one_mul]
    exact (congrArg (fun l : Levi =>
      splitRadicalCocycleAction goodPlaneSplitting (coefRep n) l (cocycleSection n polynomial)) e).symm.trans
      (splitRadicalCocycleAction_mul goodPlaneSplitting (coefRep n) (m, 1) (1, d)
        (cocycleSection n polynomial))
  rw [split, splitAction_unit n d polynomial, splitAction_levi_one n m (cocycleSection n polynomial)]
  exact cocycleSection_levi n (kap m) polynomial

/-! ### Realising crossed cocycles -/

/-- The cocycle law of `w ↦ Φ⁻¹ w(m)` on the level group. -/
theorem leviCocycle_law (cocycle : crossedCocycles (levelRep (n + 1) (-1)))
    (a b : binaryArithmeticLevel) :
    PhiInv n (cocycle.val (a * b)) = Mk n a (PhiInv n (cocycle.val b)) + PhiInv n (cocycle.val a) := by
  have law : cocycle.val (a * b) = cocycle.val a + levelRep (n + 1) (-1) a (cocycle.val b) :=
    cocycle.property a b
  rw [law, map_add]
  refine (add_comm _ _).trans ?_
  refine congrArg (fun x => x + PhiInv n (cocycle.val a)) ?_
  apply Phi_injective n
  rw [Phi_PhiInv, ← levelRep_Phi, Phi_PhiInv]

/-- The Levi one-cocycle `(m, d) ↦ Φ⁻¹ w(m)` of a crossed cocycle `w` of `Γ₁'(3)`. -/
def leviCocycle (cocycle : crossedCocycles (levelRep (n + 1) (-1))) :
    groupCohomology.cocycles₁ (levelW n) :=
  ⟨fun levi => PhiInv n (cocycle.val levi.1),
    (groupCohomology.mem_cocycles₁_iff _).mpr
      (fun first second => leviCocycle_law n cocycle first.1 second.1)⟩

/-- The relative two-cocycle of `Λ` realising a crossed cocycle of `Γ₁'(3)`. -/
def goodRelative (cocycle : crossedCocycles (levelRep (n + 1) (-1))) :
    relativeTwoCocycles goodPlaneExtension.inl (coefRep n) :=
  sectionRelative goodPlaneSplitting (coefRep n) (levelW n) (goodSection n) (goodSection_equivariant n)
    (leviCocycle n cocycle)

/-- **The edge cocycle of `goodRelative w` is `w`.** -/
theorem goodPlaneEdgeCocycle_goodRelative (cocycle : crossedCocycles (levelRep (n + 1) (-1))) :
    goodPlaneEdgeCocycle (goodRelative n cocycle) = cocycle := by
  apply Subtype.ext
  funext m
  exact (congrArg (fun radicalCycle => Phi n (upperRadicalCocycleCoordinate n radicalCycle))
    (splitEdgeCycle_sectionRelative goodPlaneSplitting (coefRep n) (levelW n) (goodSection n)
      (goodSection_equivariant n) (leviCocycle n cocycle) (m, 1))).trans
    ((congrArg (Phi n) (coordinate_cocycleSection n (PhiInv n (cocycle.val m)))).trans
      (Phi_PhiInv n (cocycle.val m)))

variable {n}

/-- **The good-plane edge on the ambient `H²(Λ, V)` is surjective.** -/
theorem goodPlaneEdgeH2_surjective (hn : 0 < n) : Function.Surjective (goodPlaneEdgeH2 hn) := by
  intro target
  induction target using Submodule.Quotient.induction_on with
  | _ cocycle =>
  refine ⟨classOf ΛG (IdentityPlaneCoordinate.ρn n)
    (liftCocycle (LevelThree.GoodPlaneCosets.goodPlaneCosets ⟨2, Nat.prime_two⟩ (by decide))
      (IdentityPlaneCoordinate.ρn n) (goodRelative n cocycle).val), ?_⟩
  rw [goodPlaneEdgeH2_apply hn _ (goodRelative n cocycle)
    (congrArg (groupCohomology.H2π (coefRep n))
      (ambientCocycleToGroup_lift (LevelThree.GoodPlaneCosets.goodPlaneCosets ⟨2, Nat.prime_two⟩ (by decide))
        (IdentityPlaneCoordinate.ρn n) (goodRelative n cocycle).val)).symm,
    goodPlaneEdgeCocycle_goodRelative]
  rfl

/-- **The good-plane cusp edge `H²(Γ_F, V) → H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` is surjective.** -/
theorem goodPlaneEdge_surjective (hn : 0 < n) : Function.Surjective (goodPlaneEdge hn) :=
  (goodPlaneEdgeH2_surjective hn).comp (psiG (n := n)).surjective

/-- **The good-plane cusp edge is bijective.** -/
theorem goodPlaneEdge_bijective (hn : 0 < n) : Function.Bijective (goodPlaneEdge hn) :=
  ⟨goodPlaneEdge_injective hn, goodPlaneEdge_surjective hn⟩

/-- The good-plane cusp edge as a linear equivalence
`H²(Γ_F, Sym^n) ≃ H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
def goodPlaneEdgeEquiv (hn : 0 < n) :
    CuspH2 n trivialCharacter .plane true ≃ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  LinearEquiv.ofBijective (goodPlaneEdge hn) (goodPlaneEdge_bijective hn)

theorem goodPlaneEdgeEquiv_apply (hn : 0 < n) (x : CuspH2 n trivialCharacter .plane true) :
    goodPlaneEdgeEquiv hn x = goodPlaneEdge hn x := rfl

end TernaryPeriodPolynomials.BoundaryDuality.EdgeSurjGoodPlane
