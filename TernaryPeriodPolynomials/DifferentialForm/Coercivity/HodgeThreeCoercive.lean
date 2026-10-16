module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleComposite
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleIsometry
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleInvolution
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Positive

@[expose] public section



/-! Degree-three basepoint coercivity of `algebraicHodgeThree`, transported from
`homogeneousHodgeTwo_coercive` via the Hodge-star isometry/involution/composite rules. This
supplies "piece B" flagged by `HodgeThree.lean`'s module docstring: the degree-three analogue of
`TernaryPoly.SL3PolynomialCoercivityPositive.homogeneousHodgeTwo_coercive`. For an alternating,
degree-`n`-homogeneous three-form `a`, set `w := 96 • star3to2 a`; `w` is an alternating
homogeneous two-form with `star2to3 w = a` (INVOLUTION), so
`threePairing (algebraicHodgeThree a) a = threePairing (star2to3 (algebraicHodgeTwo w)) (star2to3 w)`
(COMPOSITE) `= (1/96) * twoPairing (algebraicHodgeTwo w) w` (ISOMETRY)
`≥ (1/96) * (c * twoPairing w w) = c * threePairing a a` (degree-2 coercivity, ISOMETRY again). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- `star2to3` is equivariant for real scalars, by unfolding its explicit double-sum
definition and pushing the scalar through `Finset.smul_sum`. -/
theorem star2to3_smul (c : ℝ) (a : TwoCoordinates) :
    star2to3 (c • a) = c • star2to3 a := by
  funext i j k
  show star2to3 (c • a) i j k = c • star2to3 a i j k
  unfold star2to3
  simp only [Pi.smul_apply, Finset.smul_sum]
  congr 1
  funext l
  congr 1
  funext m
  module

/-- Piece B: `algebraicHodgeThree`'s own basepoint coercivity, the degree-three analogue of
`homogeneousHodgeTwo_coercive`, obtained by transporting the degree-two bound through the
Hodge-star involution/isometry/composite rules. -/
theorem algebraicHodgeThree_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ThreeCoordinates, IsAlternatingThree a →
      (∀ i j k, (a i j k).IsHomogeneous n) →
      c * threePairing a a ≤ threePairing (algebraicHodgeThree a) a := by
  obtain ⟨c, hc, h⟩ := homogeneousHodgeTwo_coercive hn
  refine ⟨c, hc, fun a ha hha => ?_⟩
  let w : TwoCoordinates := (96 : ℝ) • star3to2 a
  have hw_alt : IsAlternatingTwo w := by
    intro p q
    show ((96 : ℝ) • star3to2 a) p q = -(((96 : ℝ) • star3to2 a) q p)
    simp only [Pi.smul_apply, star3to2_alternating a p q, smul_neg]
  have hw_hom : ∀ p q, (w p q).IsHomogeneous n := fun p q =>
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem 96 (star3to2_isHomogeneous a hha p q)
  have haw : star2to3 w = a := by
    show star2to3 ((96 : ℝ) • star3to2 a) = a
    rw [star2to3_smul, hodgeStarRule_involution a ha, smul_smul]
    norm_num
  have hw_alg_alt : IsAlternatingTwo (algebraicHodgeTwo w) := algebraicHodgeTwo_alternating w hw_alt
  have hiso1 : threePairing a a = (1 / 96 : ℝ) * twoPairing w w := by
    rw [← haw, hodgeStarRule_isometry w w hw_alt]
  have hiso2 : threePairing (algebraicHodgeThree a) a =
      (1 / 96 : ℝ) * twoPairing (algebraicHodgeTwo w) w := by
    rw [← haw, hodgeStarRule_composite w hw_alt,
      hodgeStarRule_isometry (algebraicHodgeTwo w) w hw_alg_alt]
  have hraw : c * twoPairing w w ≤ twoPairing (algebraicHodgeTwo w) w :=
    h ⟨w, hw_alt, hw_hom⟩
  rw [hiso1, hiso2]
  nlinarith

end TernaryPeriodPolynomials.Argument.Coercivity
