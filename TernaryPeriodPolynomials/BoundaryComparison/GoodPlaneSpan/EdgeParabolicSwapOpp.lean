module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAmbientTransport

@[expose] public section


/-!
# The swap element `τ` and the opposite edge `mk (gF * τ)`

Introduces the order-two Weyl element `S : GL (Fin 2) ℚ` (swapping the two binary coordinates)
and its good-plane lift `τ := P (0, 0) S 1 : RationalGL3`, used to build the "opposite edge"
`mk (gF * τ) : Edges`. This mirrors, for the lower-leg (`betaZero`) argument, the line-side `binaryEdge`/`binaryCuspLevel` construction
(`InnerCuspidalArithmetic/InnerParabolic.lean`), which is uniform over every cusp frame, via a
*different* edge attached to the *same* cusp flag `cuspFlag .plane true` rather than reusing the
edge `mk gF` itself.

`τ` lies in `parabolic .plane` unconditionally (every `P x B d` has vanishing row-2 off-diagonal
entries, by `P_val`'s shape) and is self-inverse (`S` is self-inverse, and `P_inv` of a zero
translation collapses back to the same shape). Both facts combine, via `cuspFlag_eq` and
`QuotientGroup.eq`, to show `mk (gF * τ)` has the *same* `.plane`-endpoint as `mk gF`, namely
`cuspFlag .plane true` (`endpoint_gF_mul_τ`) — exactly what is needed to reuse the *existing*
`innerBoundary_fixedPointH2_locallyInner` witness (`membership`, inside
`edgeParabolic_sigmaPrimitive_of_innerBoundary`) at this new edge, via `Submodule.mem_iInf`'s
`iInf`-indexing over `{edge // endpoint .plane edge = cuspFlag .plane true}`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-! ### The swap element `S` and its good-plane lift `τ` -/

/-- The order-two Weyl element of `GL (Fin 2) ℚ`, swapping the two binary coordinates. Mirrors
`TernaryPeriodPolynomials.Automorphic.Unimodular.swap`'s construction idiom.

-/
def S : GL (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem S_val : (S : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0] := rfl

theorem S_inv : (S : GL (Fin 2) ℚ)⁻¹ = S := rfl

/-- The good-plane lift of `S`, at the trivial translation and trivial third coordinate. -/
def τ : RationalGL3 := P (0, 0) S 1

theorem τ_val : (τ : Matrix (Fin 3) (Fin 3) ℚ) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  show (P (0, 0) S 1).val = _
  rw [P_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S_val]

/-- `τ` is self-inverse. -/
theorem τ_inv : τ⁻¹ = τ := by
  show (P (0, 0) S 1)⁻¹ = P (0, 0) S 1
  rw [P_inv]
  simp [bmul, S_inv]

/-- `τ` lies in `parabolic .plane`: any `P x B d` has vanishing `(2,0)`/`(2,1)` entries. -/
theorem τ_mem_parabolic_plane : τ ∈ parabolic .plane := by
  show InPlaneParabolic τ
  constructor <;> simp [τ, P_val]

/-! ### The opposite edge `mk (gF * τ)` has the same `.plane`-endpoint as `mk gF` -/

/-- Forgetting the `.plane` endpoint of a complete flag agrees, on a literal class `mk x`, with
the coarser projection `mk x : Flags s`. -/
theorem endpoint_mk (s : Side) (x : RationalGL3) :
    endpoint s (QuotientGroup.mk x : Edges) = (QuotientGroup.mk x : Flags s) := rfl

/-- **The incidence fact**: the opposite edge `mk (gF * τ)` has the same `.plane`-endpoint as
`mk gF`, namely `cuspFlag .plane true`. Reduces, via `endpoint_mk`, `cuspFlag_eq` and
`QuotientGroup.eq`, to `(gF * τ)⁻¹ * gF ∈ parabolic .plane`, which simplifies (group cancellation)
to `τ⁻¹ ∈ parabolic .plane`, i.e. (via `τ_inv`) to `τ ∈ parabolic .plane`. -/
theorem endpoint_gF_mul_τ :
    endpoint .plane (QuotientGroup.mk (gF * τ) : Edges) = cuspFlag .plane true := by
  rw [endpoint_mk, cuspFlag_eq, QuotientGroup.eq]
  have hmem : τ⁻¹ ∈ parabolic .plane := by rw [τ_inv]; exact τ_mem_parabolic_plane
  simpa [mul_assoc] using hmem

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
