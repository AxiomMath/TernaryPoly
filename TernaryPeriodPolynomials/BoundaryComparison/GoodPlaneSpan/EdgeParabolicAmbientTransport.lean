module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicSigmaPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneConj
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore

@[expose] public section


/-!
# Transporting the `Σ`-primitive into `ΛG` coordinates (step 2b)

Continues `EdgeParabolicSigmaPrimitive.lean`'s step 2a. Transports the ambient cocycle `C`
(on `cuspLevel .plane true`) and the ad hoc primitive (on
`Σ := fixedPointLevel rationalLevel (mk gF : Edges)`) by conjugation with `gF` into `ΛG`'s own
coordinates, where `goodPlaneEdgeCocycle`/`goodPlaneEdge` actually operate, reusing the existing
`GoodPlaneEdge3.hH_conj` transport for the `C`-leg and a new mirror-image subgroup
`edgeParabolicSigmaLambda` (the `gF`-conjugate copy of `Σ`) for the `primitive`-leg.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- The `gF`-conjugate copy of `Σ := fixedPointLevel rationalLevel (mk gF : Edges)`, mirroring
`ΛG`'s own definition pattern (`GoodPlaneFrame.ΛG`) exactly. -/
def edgeParabolicSigmaLambda : Subgroup RationalGL3 :=
  (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges)).comap (MulAut.conj gF).toMonoidHom

theorem edgeParabolic_mem_sigmaLambda (h : RationalGL3) :
    h ∈ edgeParabolicSigmaLambda ↔
      gF * h * gF⁻¹ ∈ fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges) :=
  Iff.rfl

/-- Elements of `edgeParabolicSigmaLambda` conjugate (by `gF`) into `Σ` — the hypothesis
`conjCochain`/`conjCycle` need to transport `Σ`-level data into `edgeParabolicSigmaLambda`'s
world, mirroring `GoodPlaneEdge3.hH_conj`'s role for `ΛG`/`cuspLevel .plane true`. -/
theorem edgeParabolic_sigma_conj :
    ∀ h ∈ edgeParabolicSigmaLambda,
      gF * h * gF⁻¹ ∈ fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges) :=
  fun _ hh => (edgeParabolic_mem_sigmaLambda _).mp hh

theorem edgeParabolic_sigmaLambda_le_ΛG : edgeParabolicSigmaLambda ≤ ΛG := by
  intro h hh
  rw [mem_ΛG]
  exact fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
    cuspFlag_eq.symm ((edgeParabolic_mem_sigmaLambda h).mp hh)

/-- `Pg b 1 1` lies in `parabolic .line` for every `b`: its `(1,0)` entry is
`(kap 1).val 1 0 = 0` since `kap 1 = 1`, and its `(2,0)` entry vanishes unconditionally by
`P_val`'s shape. -/
theorem edgeParabolic_Pg_one_mem_lineParabolic (b : ℤ × ℤ) :
    Pg b 1 1 ∈ parabolic .line := by
  show InLineParabolic (Pg b 1 1)
  unfold InLineParabolic
  have h1 : (kap (1 : binaryArithmeticLevel)) = 1 := map_one kap
  rw [Pg, P_val]
  simp [h1]

/-- **Fact A** (good-plane side): every radical-lattice generator's image under
`goodPlaneExtension.inl` lands in `edgeParabolicSigmaLambda`. Mirrors `GoodPlaneFrame.Pg_mem`'s
stabilizer argument, specialized to `m = 1` (so the `kap`-image is the identity matrix, giving
`lineParabolic` membership for free) and transported to the `Edges`-quotient
(`parabolic .plane ⊓ parabolic .line`) rather than `Flags .plane` alone. -/
theorem edgeParabolic_factA (p : RadicalLattice) :
    (goodPlaneExtension.inl p).val ∈ edgeParabolicSigmaLambda := by
  have hinl : (goodPlaneExtension.inl p : ΛG) = radInc p := rfl
  rw [hinl, radInc_eq]
  rw [edgeParabolic_mem_sigmaLambda]
  show gF * Pg p.toAdd 1 1 * gF⁻¹ ∈ fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hΛ := Pg_mem p.toAdd 1 1
    rw [mem_ΛG] at hΛ
    exact (Subgroup.mem_inf.mp hΛ).1
  · rw [MulAction.mem_stabilizer_iff]
    change (QuotientGroup.mk (gF * Pg p.toAdd 1 1 * gF⁻¹ * gF) : Edges) = QuotientGroup.mk gF
    rw [inv_mul_cancel_right, QuotientGroup.eq]
    have hmem : Pg p.toAdd 1 1 ∈ parabolic .plane ⊓ parabolic .line :=
      Subgroup.mem_inf.mpr
        ⟨Pg_parabolic p.toAdd 1 1, edgeParabolic_Pg_one_mem_lineParabolic p.toAdd⟩
    have hinv := (parabolic .plane ⊓ parabolic .line).inv_mem hmem
    simpa [mul_assoc] using hinv

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
