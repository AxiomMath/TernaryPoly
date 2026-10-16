module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1TrivialPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1OddSwap
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentGoodLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Parabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipGood

@[expose] public section


/-!
# The local value at the good line `L₁`, trivial character

For a line class `z` (with edge primitive `w`) and a plane class `y` whose coordinates at the good line
and at the identity plane are local joint generalized eigenclasses of a character `c` with
`‖c(T₂) - 1‖ ≤ 3/4`, the fiber integration at `L₁` expresses the local value as `-c₀` times the
parabolic cup pairing of `GL₂(ℤ)` of the classes of the two bridge cocycles
(`FiberParabolic.lineValue_goodLine_parabolicPairing`), where `c₀ = -(n+1)!`.  The `U`-primitives
exist because the restrictions of the line and plane cocycles to the lattice of `L₁` are exact
(`HeckeAdjointMembershipGood`); the bridge is `Kostant.levelOneBridgeTrivial`; the class of the line
bridge cocycle is minus the good-line edge of the coordinate of `z`
(`Ident.projectH1_bridgeX_eq_neg_phiL`) and the class of the plane bridge cocycle is minus the
identity-plane edge of the coordinate of `y` (`Ident.bridgeX'_apply_trivial` together with the
class-level swap lemma `LocalPairingCaseL1OddSwap.swapPullback_projectH1_eq_neg`).  Hence the local
value is `(n+1)!` times the cup pairing of the edge images (`lineValue_goodLine_trivial_eq`), and it
is nonzero when that pairing is (`lineValue_ne_zero`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1 latL1_le)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (bridgeX bridgeX' phiTwist_trivial psiTwist_trivial levelOneBridgeTrivial)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembership (trivialData)

variable {n : ℕ}

/-- **The class of the plane bridge cocycle** is minus the identity-plane edge of the coordinate of
the plane class. -/
theorem projectH1_bridgeX'_eq_neg_edge (hn : 0 < n) (hodd : Odd n)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (y : MaximalCycles n trivialCharacter .plane)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁)) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1)) (bridgeX' (-1) (psiTwist_trivial hodd) hF) =
      -IdentityPlaneHecke.edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)) := by
  have hη' := eta_eq_cocycleAtPlane n trivialCharacter y hη
  have h1 := LocalPairingCaseL1OddSwap.swapPullback_projectH1_eq_neg (n := n) hodd (-1)
    (F := identityPlaneBinaryEdgeCycle n (relOfP hF (cocycleAtPlane n trivialCharacter y) hη'))
    (Z := bridgeX' (-1) (psiTwist_trivial hodd) hF)
    (bridgeX'_apply_trivial hodd hF (cocycleAtPlane n trivialCharacter y) hη')
  have h2 := projectH1_edgeCycle_eq_edgeH2 hn hodd hF (cocycleAtPlane n trivialCharacter y) hη'
  exact h1.trans (congrArg Neg.neg h2)

/-- **The cup pairing of the bridge classes**, in terms of the edge images. -/
theorem pairing_bridge_eq (hn : 0 < n) (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (z : MaximalCycles n trivialCharacter .line) (y : MaximalCycles n trivialCharacter .plane)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hζ : ∀ x, ζ x = z.val.val x L₁)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁))
    (hzl : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        localJoint n trivialCharacter c .line true)
    (hyp : cuspRes n trivialCharacter .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
        localJoint n trivialCharacter c .plane false)
    (hxpar : bridgeX hn 0 (phiTwist_trivial n) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0))
    (hx'par : bridgeX' (-1) (psiTwist_trivial hodd) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1))) :
    parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF),
          Submodule.mem_map_of_mem hxpar⟩
        ⟨projectH1 (arithmeticBinaryRep (n + 1) (-1))
          (bridgeX' (-1) (psiTwist_trivial hodd) hF), Submodule.mem_map_of_mem hx'par⟩ =
      parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨LocalUniqueness.phiL n hn
          ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
            LocalUniqueness.localJoint_le_ML c hc hzl⟩,
          phiL_mem_parabolicH1 n hn c hc hzl⟩
        ⟨IdentityPlaneHecke.edgeH2 n hn hodd
          (cuspRes n trivialCharacter .plane false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
          edgeH2_mem_parabolicH1 n hn hodd c hc hyp⟩ := by
  have hx_cls := projectH1_bridgeX_eq_neg_phiL hn c hc z hzl hF hζ
  have hx'_cls := projectH1_bridgeX'_eq_neg_edge hn hodd hF y hη
  have e1 : (⟨projectH1 (arithmeticBinaryRep (n + 1) 0)
      (bridgeX hn 0 (phiTwist_trivial n) hF), Submodule.mem_map_of_mem hxpar⟩ :
        parabolicH1 (arithmeticBinaryRep (n + 1) 0)) =
      -⟨LocalUniqueness.phiL n hn
          ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
            LocalUniqueness.localJoint_le_ML c hc hzl⟩,
          phiL_mem_parabolicH1 n hn c hc hzl⟩ := Subtype.ext hx_cls
  have e2 : (⟨projectH1 (arithmeticBinaryRep (n + 1) (-1))
      (bridgeX' (-1) (psiTwist_trivial hodd) hF), Submodule.mem_map_of_mem hx'par⟩ :
        parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) =
      -⟨IdentityPlaneHecke.edgeH2 n hn hodd
          (cuspRes n trivialCharacter .plane false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
          edgeH2_mem_parabolicH1 n hn hodd c hc hyp⟩ := Subtype.ext hx'_cls
  refine (congrArg₂ (fun u v => parabolicPairing (twistedPairing_goodLine_trivial hodd) u v)
    e1 e2).trans ?_
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- The `U`-primitive of the line cocycle at `L₁`, trivial character. -/
theorem exists_omegaU_trivial (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (z : MaximalCycles n trivialCharacter .line)
    (hzl : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        localJoint n trivialCharacter c .line true) :
    ∃ ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ latL1.sub, ∀ a b,
        ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b])) ∧
      ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁ :=
  FiberExact.exists_omegaU z L₁ latL1.sub latL1_le
    (HeckeAdjointMembershipGood.classOf_lineRestriction_goodLine_eq_zero z L₁
      HeckeAdjointMembershipGood.L₁_eq_goodLine latL1.sub latL1_le
      HeckeAdjointMembershipGood.latL1_mem_rad (LocalUniqueness.localJoint_le_ML c hc hzl))

/-- The `U`-primitive of the plane cocycle at `L₁`, trivial character. -/
theorem exists_thetaU_trivial (hn : 0 < n) (hodd : Odd n)
    (y : MaximalCycles n trivialCharacter .plane) :
    ∃ θU : (Fin 2 → RationalGL3) → HomogeneousPoly n,
      (∀ γ ∈ latL1.sub, ∀ a b,
        θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
          ((dualityData n trivialCharacter).φ γ) (θU ![a, b])) ∧
      ∀ a b c, differentialOneRaw θU ![a, b, c] =
        y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
          (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₁) :=
  FiberExact.exists_thetaU (dualityData n trivialCharacter) y L₁ latL1.sub latL1_le
    (HeckeAdjointMembershipGood.classOf_planeRestriction_L₁_eq_zero_odd hn hodd y)

/-- The fiber formula at `L₁` for the trivial character, in terms of the bridge classes. -/
theorem lineValue_goodLine_trivial_eq_bridge (hn : 0 < n) (hodd : Odd n)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₁))
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hxpar : bridgeX hn 0 (phiTwist_trivial n) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0))
    (hx'par : bridgeX' (-1) (psiTwist_trivial hodd) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1))) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      -(-((n + 1).factorial : ℂ)) * parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF),
          Submodule.mem_map_of_mem hxpar⟩
        ⟨projectH1 (arithmeticBinaryRep (n + 1) (-1))
          (bridgeX' (-1) (psiTwist_trivial hodd) hF), Submodule.mem_map_of_mem hx'par⟩ :=
  FiberParabolic.lineValue_goodLine_parabolicPairing (dualityData n trivialCharacter)
    z w y hw (StabilizerVanishing.topVanishing_levelStabilizer L₁) ωU hωU hdωU θU hθU hdθU
    (twistedPairing_goodLine_trivial hodd) hxpar hx'par (levelOneBridgeTrivial hodd hF)

/-- The local value at `L₁`, trivial character, given a fiber hypothesis. -/
theorem lineValue_goodLine_trivial_eq_of_fiber (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (hzl : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        localJoint n trivialCharacter c .line true)
    (hyp : cuspRes n trivialCharacter .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
        localJoint n trivialCharacter c .plane false)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₁))
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hζ : ∀ x, ζ x = z.val.val x L₁)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁)) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      ((n + 1).factorial : ℂ) * parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨LocalUniqueness.phiL n hn
          ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
            LocalUniqueness.localJoint_le_ML c hc hzl⟩,
          phiL_mem_parabolicH1 n hn c hc hzl⟩
        ⟨IdentityPlaneHecke.edgeH2 n hn hodd
          (cuspRes n trivialCharacter .plane false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
          edgeH2_mem_parabolicH1 n hn hodd c hc hyp⟩ := by
  have hxpar := bridgeX_mem_parabolicCocycles hn c hc z hzl hF hζ
  have hx'par := bridgeX'_mem_parabolicCocycles_trivial hn hodd c hc y hyp hF hη
  have hb := lineValue_goodLine_trivial_eq_bridge hn hodd z w y hw ωU θU hωU hdωU hθU hdθU hF
    hxpar hx'par
  have hp := pairing_bridge_eq hn hodd c hc z y hF hζ hη hzl hyp hxpar hx'par
  exact hb.trans ((congrArg (fun t => -(-((n + 1).factorial : ℂ)) * t) hp).trans
    (congrArg (fun t => t * _) (neg_neg _)))

/-- The local value at `L₁`, trivial character, given the two `U`-primitives. -/
theorem lineValue_goodLine_trivial_eq_of_primitives (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (hzl : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        localJoint n trivialCharacter c .line true)
    (hyp : cuspRes n trivialCharacter .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
        localJoint n trivialCharacter c .plane false)
    (ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hωU : ∀ γ ∈ latL1.sub, ∀ a b,
      ωU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter γ (ωU ![a, b]))
    (hdωU : ∀ a b c, differentialOneRaw ωU ![a, b, c] = z.val.val ![a, b, c] L₁)
    (hθU : ∀ γ ∈ latL1.sub, ∀ a b,
      θU ![γ * a, γ * b] = rationalCoefficientComponent n trivialCharacter
        ((dualityData n trivialCharacter).φ γ) (θU ![a, b]))
    (hdθU : ∀ a b c, differentialOneRaw θU ![a, b, c] =
      y.val.val ![(dualityData n trivialCharacter).φ a, (dualityData n trivialCharacter).φ b,
        (dualityData n trivialCharacter).φ c] ((dualityData n trivialCharacter).dualFlag L₁)) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      ((n + 1).factorial : ℂ) * parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨LocalUniqueness.phiL n hn
          ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
            LocalUniqueness.localJoint_le_ML c hc hzl⟩,
          phiL_mem_parabolicH1 n hn c hc hzl⟩
        ⟨IdentityPlaneHecke.edgeH2 n hn hodd
          (cuspRes n trivialCharacter .plane false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
          edgeH2_mem_parabolicH1 n hn hodd c hc hyp⟩ := by
  exact lineValue_goodLine_trivial_eq_of_fiber hn hodd c hc z w y hw hzl hyp ωU θU hωU hdωU hθU
    hdθU (FiberL1.fiberHyp_goodLine (dualityData n trivialCharacter) z w y hw ωU hωU hdωU θU hθU
      hdθU) (fun _ => rfl) (fun _ => rfl)

/-- **The local value at `L₁` for the trivial character** is `(n+1)!` times the parabolic cup pairing
of the good-line edge of the line coordinate and the identity-plane edge of the plane coordinate. -/
theorem lineValue_goodLine_trivial_eq (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (hw : EdgePrimitive z w)
    (hzl : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        localJoint n trivialCharacter c .line true)
    (hyp : cuspRes n trivialCharacter .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
        localJoint n trivialCharacter c .plane false) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y =
      ((n + 1).factorial : ℂ) * parabolicPairing (twistedPairing_goodLine_trivial hodd)
        ⟨LocalUniqueness.phiL n hn
          ⟨cuspRes n trivialCharacter .line true
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z),
            LocalUniqueness.localJoint_le_ML c hc hzl⟩,
          phiL_mem_parabolicH1 n hn c hc hzl⟩
        ⟨IdentityPlaneHecke.edgeH2 n hn hodd
          (cuspRes n trivialCharacter .plane false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
          edgeH2_mem_parabolicH1 n hn hodd c hc hyp⟩ := by
  refine (exists_omegaU_trivial c hc z hzl).elim fun ωU hω => ?_
  refine (exists_thetaU_trivial hn hodd y).elim fun θU hθ => ?_
  exact lineValue_goodLine_trivial_eq_of_primitives hn hodd c hc z w y hw hzl hyp ωU θU hω.1 hω.2
    hθ.1 hθ.2

variable {cusp : CuspidalRepresentation} {coh : Cohomological cusp n}
  {hecke : BoundaryHecke n trivialCharacter}
  {hhecke : ActualBoundaryHecke n trivialCharacter hecke}

/-- **The local value at `L₁` is nonzero** when the cup pairing of the edge images of the line
summand class and of the plane class is. -/
theorem lineValue_ne_zero (hn : 3 ≤ n) (hodd : Odd n)
    (hne : associatePair (trivialData cusp coh) ≠ ⊥)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (trivialData cusp coh) .line)
    (hw : EdgePrimitive z w)
    (hyJ : cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke) .plane
        false)
    (hnz : parabolicPairing (twistedPairing_goodLine_trivial hodd)
        (lineEdge (hecke := hecke) (hhecke := hhecke) hn hne ⟨_, hz⟩)
        ⟨IdentityPlaneHecke.edgeH2 n (by omega) hodd
          (cuspRes n trivialCharacter .plane false
            (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y)),
          edgeH2_mem_parabolicH1 n (by omega) hodd
            (pairCharacter (trivialData cusp coh) hecke hhecke)
            (pair_two_sub_one (hecke := hecke) (hhecke := hhecke) hn hne) hyJ⟩ ≠ 0) :
    lineValue traceDataL2 (dualityData n trivialCharacter) 1 z w y ≠ 0 := by
  have hc := pair_two_sub_one (hecke := hecke) (hhecke := hhecke) hn hne
  have hzJ : cuspRes n trivialCharacter .line true
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
      localJoint n trivialCharacter (pairCharacter (trivialData cusp coh) hecke hhecke) .line
        true :=
    Separation.cuspRes_mem_localJoint_of_mem (trivialData cusp coh) hecke hhecke .line
      true hz
  intro h0
  have heq := lineValue_goodLine_trivial_eq (by omega) hodd _ hc z w y hw hzJ hyJ
  exact (mul_ne_zero (by exact_mod_cast (Nat.factorial_pos (n + 1)).ne') hnz)
    (heq.symm.trans h0)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1Trivial

end
