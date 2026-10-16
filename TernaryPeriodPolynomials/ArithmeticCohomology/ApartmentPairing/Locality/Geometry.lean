module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.LocalDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BoxRank

@[expose] public section


/-!
# Lemma 3.3, G3: product coordinates on the symmetric space

`coordHomeo : Space ≃ₜ ℝ³ × ℝ²` sends a form to its unipotent coordinates `(x, y, z)` (those of
`LocalDegree.unip`, so its first component is `piR3`) and the logarithms of the two positive pivots.
The diagonal flat is `{π = 0}` (`flat`), the identity form is `p0` (`coordHomeo p0 = 0`), and
`boxC ε R`, `boxO ε R` are the closed and open coordinate boxes.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpaceParabolicCoordinates
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- The unipotent coordinates as a homeomorphism onto Euclidean three-space. -/
def uHomeo : Vec3 ≃ₜ R3 := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.symm

/-- The logarithms of the two positive pivots, as a point of the Euclidean plane. -/
def tHomeo : (PositiveScale × PositiveScale) ≃ₜ R2 :=
  (Real.expOrderIso.toHomeomorph.symm.prodCongr Real.expOrderIso.toHomeomorph.symm).trans
    (Homeomorph.finTwoArrow.symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.symm)

/-- **Product coordinates** `(π, t)` of the symmetric space: unipotent coordinates and log-pivots. -/
def coordHomeo : Space ≃ₜ R3 × R2 := ldlHomeomorph.trans (uHomeo.prodCongr tHomeo)

theorem coordHomeo_fst (S : Space) : (coordHomeo S).1 = piR3 S := rfl

/-- The diagonal flat: the zero locus of the unipotent coordinates. -/
def flat : Set Space := {S | piR3 S = 0}

theorem mem_flat_iff (S : Space) : S ∈ flat ↔ (coordHomeo S).1 = 0 := Iff.rfl

/-- The identity form (trace-one normalized). -/
def p0 : Space := coordHomeo.symm (0, 0)

theorem coordHomeo_p0 : coordHomeo p0 = (0, 0) := coordHomeo.apply_symm_apply _

theorem p0_mem_flat : p0 ∈ flat := by
  rw [mem_flat_iff, coordHomeo_p0]

/-- The closed coordinate box. -/
def boxC (ε R : ℝ) : Set Space :=
  coordHomeo ⁻¹' (Metric.closedBall (0 : R3) ε ×ˢ Metric.closedBall (0 : R2) R)

/-- The open coordinate box. -/
def boxO (ε R : ℝ) : Set Space :=
  coordHomeo ⁻¹' (Metric.ball (0 : R3) ε ×ˢ Metric.ball (0 : R2) R)

theorem isCompact_boxC (ε R : ℝ) : IsCompact (boxC ε R) := by
  have : boxC ε R = coordHomeo.symm '' (Metric.closedBall (0 : R3) ε ×ˢ Metric.closedBall (0 : R2) R) := by
    ext S
    simp only [boxC, Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨coordHomeo S, h, by simp⟩
    · rintro ⟨q, hq, rfl⟩; simpa using hq
  rw [this]
  exact ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image coordHomeo.symm.continuous

theorem isOpen_boxO (ε R : ℝ) : IsOpen (boxO ε R) :=
  (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage coordHomeo.continuous

theorem boxO_subset_boxC (ε R : ℝ) : boxO ε R ⊆ boxC ε R := fun _ h =>
  ⟨Metric.ball_subset_closedBall h.1, Metric.ball_subset_closedBall h.2⟩

theorem p0_mem_boxO {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) : p0 ∈ boxO ε R := by
  show coordHomeo p0 ∈ (Metric.ball (0 : R3) ε ×ˢ Metric.ball (0 : R2) R)
  rw [coordHomeo_p0]
  exact ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hR⟩

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
