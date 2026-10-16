module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL1OddSwap
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Parabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentGoodLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipGood
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.StabilizerVanishing

@[expose] public section


/-!
# The local value at the good line for an odd character is the parabolic cup pairing of the edges

For a character `χ` with `χ(-1_∞) = -1`, odd `n`, and line and plane cocycles `z`, `y` whose
Shapiro coordinates at the good-line cusp and the identity-plane cusp are local joint generalized
eigenclasses of a character `c` with `‖c(T₂) + 1‖ ≤ 3/4`, the local value at `L₁` is

  `lineValue z w y = (n+1)! · ⟨E_L ψ [z], E_P [y]⟩_par`,

the parabolic cup pairing of `GL₂(ℤ)` of the twisted good-line edge `E_L ∘ ψ` of the line
coordinate and the twisted identity-plane edge `E_P` of the plane coordinate
(`lineValue_goodLine_odd_eq`). The proof assembles the fiber integration formula of the level-one
bridge (`FiberParabolic.lineValue_goodLine_parabolicPairing`, `Kostant.levelOneBridgeOdd`), the
vanishing of the radical restrictions (`HeckeAdjointMembershipGood`), the identifications of the
bridge cocycles with the edge classes (`ParabolicDualityIdentGoodLine`,
`ParabolicDualityIdentPlane`) and the fact that the swap pullback acts as `-1`
(`LocalPairingCaseL1OddSwap`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddValue

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1 latL1_le)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.Spectral.CuspReduction

variable {n : ℕ} {χ : RankOneCharacter}

/-- The pairing of two classes which are the negatives of two other classes. -/
theorem pairing_neg_neg {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] {S : Submodule ℂ V} {S' : Submodule ℂ V'} (π : S →ₗ[ℂ] S' →ₗ[ℂ] ℂ)
    {u u' : V} {v v' : V'} (hu : u = -u') (hv : v = -v') (hu0 : u ∈ S) (hu1 : u' ∈ S)
    (hv0 : v ∈ S') (hv1 : v' ∈ S') : π ⟨u, hu0⟩ ⟨v, hv0⟩ = π ⟨u', hu1⟩ ⟨v', hv1⟩ := by
  subst hu hv
  have h1 : (⟨-u', hu0⟩ : S) = -⟨u', hu1⟩ := rfl
  have h2 : (⟨-v', hv0⟩ : S') = -⟨v', hv1⟩ := rfl
  rw [h1, h2]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- **The class of `bridgeX'` is minus the twisted identity-plane edge of the plane coordinate.** -/
theorem projectH1_bridgeX'_eq_neg_edgeH2T (hneg : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (y : MaximalCycles n χ .plane)
    (hη : ∀ x, η x = y.val.val
      ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
        ((dualityData n χ).dualFlag L₁)) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX' 0 (psiTwist_odd hodd hneg) hF) =
      -Twisted.edgeH2T n χ hneg hn hodd (cuspRes n χ .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n χ) .plane) y)) := by
  have hη' := eta_eq_cocycleAtPlane n χ y hη
  have h1 := LocalPairingCaseL1OddSwap.swapPullback_projectH1_eq_neg (n := n) hodd 0
    (F := Twisted.identityPlaneBinaryEdgeCycleT n χ hneg
      (relOfPT hF (cocycleAtPlane n χ y) hη'))
    (Z := bridgeX' 0 (psiTwist_odd hodd hneg) hF)
    (bridgeX'_apply_odd hneg hodd hF (cocycleAtPlane n χ y) hη')
  have h2 := projectH1_edgeCycleT_eq_edgeH2T hneg hn hodd hF (cocycleAtPlane n χ y) hη'
  exact h1.trans (congrArg Neg.neg h2)

/-- Closing algebra. -/
theorem value_close {L X Y k : ℂ} (key : L = - -k * X) (h : X = Y) : L = k * Y := by
  rw [key, h, neg_neg]

/-- **The bridge pairing is the pairing of the edges.** -/
theorem pairing_bridge_eq_edges (hneg : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (z : MaximalCycles n χ .line)
    (y : MaximalCycles n χ .plane)
    (hζ : ∀ x, ζ x = z.val.val x L₁)
    (hη : ∀ x, η x = y.val.val
      ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
        ((dualityData n χ).dualFlag L₁))
    (hzl : cuspRes n χ .line true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) ∈
        localJoint n χ c .line true)
    (hyp : cuspRes n χ .plane false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) ∈
        localJoint n χ c .plane false)
    (hxpar : bridgeX hn (-1) (phiTwist_odd hneg) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)))
    (hx'par : bridgeX' 0 (psiTwist_odd hodd hneg) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0)) :
    parabolicPairing (twistedPairing_goodLine_odd hodd)
      ⟨projectH1 (arithmeticBinaryRep (n + 1) (-1))
        (bridgeX hn (-1) (phiTwist_odd hneg) hF), Submodule.mem_map_of_mem hxpar⟩
      ⟨projectH1 (arithmeticBinaryRep (n + 1) 0)
        (bridgeX' 0 (psiTwist_odd hodd hneg) hF), Submodule.mem_map_of_mem hx'par⟩ =
      parabolicPairing (twistedPairing_goodLine_odd hodd)
        ⟨Twisted.edgeH2LT n χ hneg hn (Twisted.psiLT n χ
          (cuspRes n χ .line true (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n χ) .line) z))),
          edgeH2LT_mem_parabolicH1 n χ hneg hn c hc hzl⟩
        ⟨Twisted.edgeH2T n χ hneg hn hodd
          (cuspRes n χ .plane false (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n χ) .plane) y)),
          edgeH2T_mem_parabolicH1 n χ hneg hn hodd c hc hyp⟩ := by
  have hx_cls := projectH1_bridgeX_eq_neg_edgeH2LT_psiLT hneg hn z hF hζ
  have hx'_cls := projectH1_bridgeX'_eq_neg_edgeH2T hneg hn hodd hF y hη
  have e1 : (⟨projectH1 (arithmeticBinaryRep (n + 1) (-1))
      (bridgeX hn (-1) (phiTwist_odd hneg) hF), Submodule.mem_map_of_mem hxpar⟩ :
        parabolicH1 (arithmeticBinaryRep (n + 1) (-1))) =
      -⟨Twisted.edgeH2LT n χ hneg hn (Twisted.psiLT n χ
          (cuspRes n χ .line true (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n χ) .line) z))),
          edgeH2LT_mem_parabolicH1 n χ hneg hn c hc hzl⟩ := Subtype.ext hx_cls
  have e2 : (⟨projectH1 (arithmeticBinaryRep (n + 1) 0)
      (bridgeX' 0 (psiTwist_odd hodd hneg) hF), Submodule.mem_map_of_mem hx'par⟩ :
        parabolicH1 (arithmeticBinaryRep (n + 1) 0)) =
      -⟨Twisted.edgeH2T n χ hneg hn hodd (cuspRes n χ .plane false
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n χ) .plane) y)),
          edgeH2T_mem_parabolicH1 n χ hneg hn hodd c hc hyp⟩ := Subtype.ext hx'_cls
  exact (congrArg₂ (fun u v => parabolicPairing (twistedPairing_goodLine_odd hodd) u v) e1 e2).trans
    (by simp only [map_neg, LinearMap.neg_apply, neg_neg])

/-- **The local value at the good line `L₁` for an odd character** is `(n+1)!` times the parabolic
cup pairing of the twisted good-line edge of the line coordinate and the twisted identity-plane
edge of the plane coordinate. -/
theorem lineValue_goodLine_odd_eq (hneg : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) (y : MaximalCycles n χ .plane)
    (hw : EdgePrimitive z w)
    (hzl : cuspRes n χ .line true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) ∈
        localJoint n χ c .line true)
    (hyp : cuspRes n χ .plane false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) ∈
        localJoint n χ c .plane false) :
    lineValue traceDataL2 (dualityData n χ) 1 z w y =
      ((n + 1).factorial : ℂ) * parabolicPairing (twistedPairing_goodLine_odd hodd)
        ⟨Twisted.edgeH2LT n χ hneg hn (Twisted.psiLT n χ
          (cuspRes n χ .line true (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n χ) .line) z))),
          edgeH2LT_mem_parabolicH1 n χ hneg hn c hc hzl⟩
        ⟨Twisted.edgeH2T n χ hneg hn hodd
          (cuspRes n χ .plane false (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n χ) .plane) y)),
          edgeH2T_mem_parabolicH1 n χ hneg hn hodd c hc hyp⟩ := by
  obtain ⟨ωU, hωU, hdωU⟩ := FiberExact.exists_omegaU z L₁ latL1.sub latL1_le
    (HeckeAdjointMembershipGood.classOf_lineRestriction_L₁_eq_zero_twisted χ hneg z)
  obtain ⟨θU, hθU, hdθU⟩ := FiberExact.exists_thetaU (dualityData n χ) y L₁ latL1.sub latL1_le
    (HeckeAdjointMembershipGood.classOf_planeRestriction_L₁_eq_zero_twisted χ hneg hn y)
  have hF := FiberL1.fiberHyp_goodLine (dualityData n χ) z w y hw ωU hωU hdωU θU hθU hdθU
  have hζ : ∀ x, FiberL1.lineCocycle z x = z.val.val x L₁ := fun _ => rfl
  have hη : ∀ x, FiberL1.planeCocycle (dualityData n χ) y x = y.val.val
      ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]
        ((dualityData n χ).dualFlag L₁) := fun _ => rfl
  have hxpar := bridgeX_odd_mem_parabolicCocycles hneg hn c hc z hzl hF hζ
  have hx'par := bridgeX'_mem_parabolicCocycles_odd hneg hn hodd c hc y hyp hF hη
  have key := FiberParabolic.lineValue_goodLine_parabolicPairing (dualityData n χ) z w y hw
    (StabilizerVanishing.topVanishing_levelStabilizer L₁) ωU hωU hdωU θU hθU hdθU
    (twistedPairing_goodLine_odd hodd) hxpar hx'par (levelOneBridgeOdd hodd hneg hF)
  exact value_close key
    (pairing_bridge_eq_edges hneg hn hodd c hc hF z y hζ hη hzl hyp hxpar hx'par)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL1OddValue

end
