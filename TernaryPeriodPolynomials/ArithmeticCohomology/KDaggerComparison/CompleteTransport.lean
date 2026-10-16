module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GoodFlags
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerTransport
public import TernaryPeriodPolynomials.BoundaryComparison.LevelTransfer

@[expose] public section


/-!
# Transport of stabilizer classes along the level group preserves local innerness

`resH2_stabilizerTransportH2`: the transport `stabilizerTransportH2` of the stabilizer cohomology along `q ∈ L` commutes with the
restriction to the smaller stabilizers of points `e`, `e' = q e`.  `stabilizerTransportH2_mem_locallyInner`: transport along `q ∈ K†`
maps the locally inner classes at a flag `F` into those at `q F`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.LevelTransfer

variable {V : Type} [AddCommGroup V] [Module ℂ V] {X Y : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 Y]

/-- Transport along `q ∈ L` commutes with the restriction to the stabilizers of other points. -/
theorem resH2_stabilizerTransportH2 (L : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (q : L) (s t : X) (hst : q.val • s = t) (e e' : Y) (hee : q.val • e = e')
    (hs : fixedPointLevel L e ≤ fixedPointLevel L s) (ht : fixedPointLevel L e' ≤ fixedPointLevel L t)
    (x : H2 (fixedPointLevel L s) ρ) :
    resH2 ρ ht (stabilizerTransportH2 L ρ q s t hst x) =
      stabilizerTransportH2 L ρ q e e' hee (resH2 ρ hs x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- **Transport along `K†` preserves the locally inner classes.** -/
theorem stabilizerTransportH2_mem_locallyInner (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (q : rationalLevel) (F F' : Flags side) (hF : q.val • F = F')
    (x : H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent degree character))
    (hx : x ∈ locallyInnerClasses degree character side F) :
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent degree character) q F F' hF x ∈
      locallyInnerClasses degree character side F' := by
  unfold locallyInnerClasses at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro e'
  have hend : endpoint side (q.val⁻¹ • e'.val) = F := by
    rw [endpoint_smul, e'.property, ← hF, inv_smul_smul]
  have h1 := LinearMap.mem_ker.mp (hx ⟨q.val⁻¹ • e'.val, hend⟩)
  have hee : q.val • (q.val⁻¹ • e'.val) = e'.val := smul_inv_smul _ _
  rw [LinearMap.mem_ker]
  change resH2 (rationalCoefficientComponent degree character)
    (fixedPointLevel_edge_le_flag side e'.val F' e'.property) _ = 0
  have h2 := resH2_stabilizerTransportH2 rationalLevel (rationalCoefficientComponent degree character) q F F' hF
    (q.val⁻¹ • e'.val) e'.val hee (fixedPointLevel_edge_le_flag side _ F hend)
    (fixedPointLevel_edge_le_flag side e'.val F' e'.property) x
  rw [h2]
  change stabilizerTransportH2 rationalLevel (rationalCoefficientComponent degree character) q _ _ hee
    (resH2 (rationalCoefficientComponent degree character) (fixedPointLevel_edge_le_flag side _ F hend) x) = 0
  have h3 : resH2 (rationalCoefficientComponent degree character) (fixedPointLevel_edge_le_flag side _ F hend) x = 0 := h1
  rw [h3, map_zero]

end TernaryPeriodPolynomials.Argument.KDaggerComparison
