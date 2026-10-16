module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.ParabolicL0
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing

@[expose] public section


/-!
# The typed bridge for the even bad-line value

* `crossedBinaryEquiv`, `parabolicBinaryEquiv`: the two spellings `binaryArithmeticRepresentation n`
  and `levelRep (n + 1) 0` of the bad-line Levi representation give literally the same crossed `H¹`,
  so that sums and Hecke operators can be written at one carrier;
* `mkQ_badX'_eq_planeTransport`: the class of the cocycle `badX'` of the bridge
  `levelThreeBridgeBad` is the transported good-plane edge class;
* `lineValue_of_classes`: from the classes of `badX`, `badX'`, the local value at the bad line is
  `(n+1)!/3` times the even pairing, proved for abstract classes to keep the unifier away from the
  concrete carrier;
* `lineValue_eq_pairing_bridge`: the local value at the bad line is `(n+1)!/3` times the even
  pairing of the line edge class and the good-plane edge class.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (TwistedPairing parabolicCrossed parabolicCrossedH1 parabolicPairing mem_parabolicCrossed_of_mem
    twistedPairing_binaryArithmeticRepresentation)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (relG goodPlaneEdge_cusp_eq badX'_apply alpha planeComparison planeComparison_intertwines)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badX badX' levelThreeBridgeBad)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3 (goodPlaneEdge)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (goodPlaneEdgeCocycle)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (badLevelHecke)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (latL0 latL0_le latL0_le_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L₀ endpoint_line_e₀)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
  (exists_omegaU exists_thetaU)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL0 (fiberHyp_line)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0
  (lineValue_badLine_parabolicPairing)

variable {n : ℕ}

/-! ### The two spellings of the bad-line carrier -/

section Carrier

variable (n)

/-- The crossed `H¹` of `binaryArithmeticRepresentation n` is that of `levelRep (n + 1) 0`. -/
def crossedBinaryEquiv :
    CrossedH1 (binaryArithmeticRepresentation n) ≃ₗ[ℂ] CrossedH1 (levelRep (n + 1) 0) :=
  LinearEquiv.refl ℂ _

/-- The carrier equivalence does nothing. -/
theorem crossedBinaryEquiv_apply (x : CrossedH1 (binaryArithmeticRepresentation n)) :
    (crossedBinaryEquiv n x : CrossedH1 (levelRep (n + 1) 0)) = x := rfl

/-- The inverse carrier equivalence does nothing. -/
theorem crossedBinaryEquiv_symm_apply (x : CrossedH1 (levelRep (n + 1) 0)) :
    ((crossedBinaryEquiv n).symm x : CrossedH1 (binaryArithmeticRepresentation n)) = x := rfl

/-- The parabolic submodules at the two spellings agree. -/
theorem parabolicCrossedH1_binary_eq :
    parabolicCrossedH1 (binaryArithmeticRepresentation n) =
      parabolicCrossedH1 (levelRep (n + 1) 0) := rfl

/-- The parabolic classes at the two spellings are the same module. -/
def parabolicBinaryEquiv :
    parabolicCrossedH1 (binaryArithmeticRepresentation n) ≃ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) 0) :=
  LinearEquiv.refl ℂ _

/-- The parabolic carrier equivalence does nothing. -/
theorem parabolicBinaryEquiv_apply (x : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
    ((parabolicBinaryEquiv n x : parabolicCrossedH1 (levelRep (n + 1) 0)) :
      CrossedH1 (levelRep (n + 1) 0)) =
        (x : CrossedH1 (binaryArithmeticRepresentation n)) := rfl

/-- The bad-line Hecke operator, on classes, at the `levelRep` carrier. -/
theorem badLevelHecke_eq (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (x : CrossedH1 (binaryArithmeticRepresentation n)) :
    badLevelHecke p hp3 n x =
      TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1.levelHecke (n + 1) 0 p
        hp3 x := rfl

/-- The parabolic bad-line Hecke operator is the restriction of `badLevelHecke`. -/
theorem heckeBad_coe (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
    ((heckeBad p hp3 x : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
      CrossedH1 (binaryArithmeticRepresentation n)) =
        badLevelHecke p hp3 n (x : CrossedH1 (binaryArithmeticRepresentation n)) := rfl

end Carrier

/-! ### The classes of the bridge cocycles -/

/-- Membership transports along an equality. -/
theorem mem_of_eq_bridge {M : Type} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} {a b : M}
    (h : a = b) (hb : b ∈ S) : a ∈ S := h ▸ hb

/-- **The class of the dual-coordinate cocycle `badX'` is the transported good-plane edge.** -/
theorem mkQ_badX'_eq_planeTransport {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n} (heven : Even n) (hn0 : 0 < n)
    (hF : ParabolicDuality.IdentBad.BadLineFiber n Λe ζ η ω ωU θU)
    (y : MaximalCycles n trivialCharacter .plane)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      (QuotientGroup.mk longWeyl : Flags .plane)) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX' heven hF) =
      planeTransportH1 heven (goodPlaneEdge hn0 (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y))) := by
  rw [goodPlaneEdge_cusp_eq hn0 hF y hη]
  change _ = (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ
    (transportCocycles (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n) alpha alpha_mul
      (planeComparison n) (planeComparison_intertwines n heven)
      (goodPlaneEdgeCocycle (relG hF y hη)))
  congr 1
  apply Subtype.ext
  funext γ
  exact badX'_apply heven hF y hη γ

section Generic

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ binaryArithmeticLevel V} {ρ' : Representation ℂ binaryArithmeticLevel W}
  {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- A crossed cocycle whose class equals a parabolic class is parabolic. -/
theorem mem_parabolicCrossed_of_class {x : crossedCocycles ρ} {X : CrossedH1 ρ}
    (hX : (crossedBoundaries ρ).mkQ x = X) (hmem : X ∈ parabolicCrossedH1 ρ) :
    x ∈ parabolicCrossed ρ :=
  mem_parabolicCrossed_of_mem ρ (hX ▸ hmem)

/-- The parabolic pairing only depends on the classes of its cocycle arguments. -/
theorem parabolicPairing_mk_congr (P : TwistedPairing ρ ρ' B) {x : crossedCocycles ρ}
    {x' : crossedCocycles ρ'} (hx : x ∈ parabolicCrossed ρ) (hx' : x' ∈ parabolicCrossed ρ')
    {X : parabolicCrossedH1 ρ} {Y : parabolicCrossedH1 ρ'}
    (hX : (crossedBoundaries ρ).mkQ x = (X : CrossedH1 ρ))
    (hY : (crossedBoundaries ρ').mkQ x' = (Y : CrossedH1 ρ')) :
    parabolicPairing P ⟨(crossedBoundaries ρ).mkQ x, Submodule.mem_map_of_mem hx⟩
        ⟨(crossedBoundaries ρ').mkQ x', Submodule.mem_map_of_mem hx'⟩ =
      parabolicPairing P X Y :=
  congrArg₂ (fun u v => parabolicPairing P u v) (Subtype.ext hX) (Subtype.ext hY)

end Generic

section Abstract

/-- **The local value from the classes of the bridge cocycles**: if the classes of `badX`, `badX'`
are `X` and the transport of `Y`, the local value at the bad line is `(n+1)!/3` times the even
pairing of `X` and `Y`. -/
theorem lineValue_of_classes {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n} (heven : Even n) (hn0 : 0 < n)
    (hF : ParabolicDuality.IdentBad.BadLineFiber n Λe ζ η ω ωU θU)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] =
        rationalCoefficientComponent n trivialCharacter ((dualityData n trivialCharacter).φ γ)
          (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀))
    (X : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (Y : parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (hx : badX hn0 hF ∈ parabolicCrossed (binaryArithmeticRepresentation n))
    (hx' : badX' heven hF ∈ parabolicCrossed (binaryArithmeticRepresentation n))
    (hX : (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn0 hF) =
      (X : CrossedH1 (binaryArithmeticRepresentation n)))
    (hY : (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX' heven hF) =
      planeTransportH1 heven (Y : CrossedH1 (levelRep (n + 1) (-1)))) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (((n + 1).factorial : ℂ) / 3) * badGoodPairingEven heven X Y := by
  have key := lineValue_badLine_parabolicPairing (dualityData n trivialCharacter) z w y hw
    (StabilizerVanishing.topVanishing_levelStabilizer L₀) ωU hωU hdωU θU hθU hdθU
    (twistedPairing_binaryArithmeticRepresentation n heven) hx hx'
    (levelThreeBridgeBad hn0 heven hF)
  have e3 := parabolicPairing_mk_congr (twistedPairing_binaryArithmeticRepresentation n heven)
    hx hx' hX (hY.trans (planeTransportPar_coe heven Y).symm)
  exact key.trans ((congrArg (fun t => (((n + 1).factorial : ℂ) / 3) * t) e3).trans
    (congrArg (fun t => (((n + 1).factorial : ℂ) / 3) * t)
      (badGoodPairingEven_apply heven _ _).symm))

end Abstract

section Value

variable (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
  (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
  (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)

include cusp coh hecke hhecke hn hne in
/-- The `U`-primitive `ωU` of the line cocycle on the lattice of `L₀`. -/
theorem omegaU_exists (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line) :
    ∃ ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ latL0.sub, ∀ a b,
        ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b])) ∧
      ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀ :=
  exists_omegaU z L₀ latL0.sub latL0_le
    (HeckeAdjointMembershipBad.classOf_lineRestriction_L₀_eq_zero cusp coh hecke hhecke hn hne z
      hz)

end Value

section Plane

/-- The `U`-primitive `θU` of the plane cocycle on the lattice of `L₀`. -/
theorem thetaU_exists (hn0 : 0 < n) (y : MaximalCycles n trivialCharacter .plane) :
    ∃ θU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ latL0.sub, ∀ a b,
        θU ![γ * a, γ * b] =
          rationalCoefficientComponent n trivialCharacter ((dualityData n trivialCharacter).φ γ)
            (θU ![a, b])) ∧
      ∀ a b c, differentialOneRaw θU ![a, b, c] =
        y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
          (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀) :=
  exists_thetaU (dualityData n trivialCharacter) y L₀ latL0.sub latL0_le
    (HeckeAdjointMembershipPlane.classOf_planeRestriction_L₀_eq_zero hn0 y)

end Plane

section Value2

variable (cusp : CuspidalRepresentation) (coh : Cohomological cusp n)
  (hecke : BoundaryHecke n trivialCharacter) (hhecke : ActualBoundaryHecke n trivialCharacter hecke)
  (hn : 3 ≤ n) (hne : associatePair (trivialData cusp coh) ≠ ⊥)

include cusp coh hecke hhecke hn hne in
/-- **The local value at the bad line**, for given primitives `ωU`, `θU`. -/
theorem lineValue_of_primitives (heven : Even n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (hw : EdgePrimitive z w)
    (hyP : goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL0.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₀)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hθU : ∀ γ ∈ latL0.sub, ∀ a b,
      θU ![γ * a, γ * b] =
        rationalCoefficientComponent n trivialCharacter ((dualityData n trivialCharacter).φ γ)
          (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₀)) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (((n + 1).factorial : ℂ) / 3) *
        badGoodPairingEven heven (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩)
          ⟨goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
            hyP⟩ := by
  have hn0 : 0 < n := by omega
  have hF := fiberHyp_line (dualityData n trivialCharacter) endpoint_line_e₀ latL0_le latL0_le_e₀
    z w y hw ωU hωU hdωU θU hθU hdθU
  have hη' := ParabolicDuality.IdentBad.hη_flag
    (η := fun x => y.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
      ((dualityData n trivialCharacter).dualFlag L₀)) y (fun x => rfl)
  have hxcls : (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn0 hF) =
      ((lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩ :
        parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
        CrossedH1 (binaryArithmeticRepresentation n)) :=
    ParabolicDuality.IdentBad.mkQ_badX_eq_neg_badLineEdge_cusp hn0 hF z (fun x => rfl)
  have hx : badX hn0 hF ∈ parabolicCrossed (binaryArithmeticRepresentation n) :=
    mem_parabolicCrossed_of_class hxcls (lineEdge cusp coh hecke hhecke hn hne _).2
  have hycls := mkQ_badX'_eq_planeTransport heven hn0 hF y hη'
  have hx' : badX' heven hF ∈ parabolicCrossed (binaryArithmeticRepresentation n) :=
    mem_parabolicCrossed_of_class hycls (planeTransportH1_mem heven hyP)
  exact lineValue_of_classes heven hn0 hF z w y hw hωU hdωU hθU hdθU
    (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩) ⟨_, hyP⟩ hx hx' hxcls hycls

include cusp coh hecke hhecke hn hne in
/-- **The local value at the bad line is a multiple of the pairing of the edge classes.** -/
theorem lineValue_eq_pairing_bridge (heven : Even n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (hw : EdgePrimitive z w)
    (hyP : goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 0 z w y =
      (((n + 1).factorial : ℂ) / 3) *
        badGoodPairingEven heven (lineEdge cusp coh hecke hhecke hn hne ⟨_, hz⟩)
          ⟨goodPlaneEdge (by omega : 0 < n) (cuspRes n trivialCharacter .plane true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
            hyP⟩ :=
  (omegaU_exists cusp coh hecke hhecke hn hne z hz).elim fun _ hω =>
    (thetaU_exists (by omega : 0 < n) y).elim fun _ hθ =>
      lineValue_of_primitives cusp coh hecke hhecke hn hne heven z w y hz hw hyP _ hω.1 hω.2 _
        hθ.1 hθ.2

end Value2

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
