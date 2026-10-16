module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.HodgeMetric

@[expose] public section



/-! Degree-three-to-four extension of the original authors' abstract array-combinatorics layer
(`TernaryPoly.SL3PolynomialCoercivityHodge`/`...HodgeMetric`, which stops at `ThreeCoordinates`):
`FourCoordinates`, the alternating-sum operator `exteriorThree : ThreeCoordinates →
FourCoordinates`, its metric-contraction adjoint `contractionFour : FourCoordinates →
ThreeCoordinates`, the pairing `fourPairing`, and the pure combinatorial adjointness identity
`exteriorThree_contractionFour_adjoint`, mirroring `exteriorTwo_contractionThree_adjoint` one
degree up. This is new material (not in the original library, which never needed degree-4 array
coordinates), used by `AdjointThree.lean` to build the degree-3 basepoint adjointness that both
clauses (`a : Core n 3` and `a : Core n 4`) of `coercivity_compact_support` depend on. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

abbrev FourCoordinates := Fin 5 → Fin 5 → Fin 5 → Fin 5 → Poly

/-- Antisymmetric under swapping the first two slots; invariant under the (even) 3-cycle on the
first three slots; antisymmetric under the (odd) 4-cycle moving the last slot to the front. These
three relations are exactly what `exteriorThree_contractionFour_adjoint`'s pointwise identity
needs, mirroring `IsAlternatingThree`'s two clauses one degree up. -/
def IsAlternatingFour (a : FourCoordinates) : Prop :=
  (∀ i j k l, a i j k l = -a j i k l) ∧ (∀ i j k l, a i j k l = a k i j l) ∧
    (∀ i j k l, a i j k l = -a l i j k)

/-- Algebraic exterior multiplication by the coefficient action, degree three to four. -/
def exteriorThree (a : ThreeCoordinates) : FourCoordinates := fun i j k l =>
  infinitesimal (tangentFrame i) (a j k l) - infinitesimal (tangentFrame j) (a i k l) +
    infinitesimal (tangentFrame k) (a i j l) - infinitesimal (tangentFrame l) (a i j k)

/-- Metric contraction by the self-adjoint coefficient action, degree four to three. -/
def contractionFour (a : FourCoordinates) : ThreeCoordinates := fun i j k =>
  ∑ l : Fin 5, tangentWeight l • infinitesimal (tangentFrame l) (a l i j k)

def fourPairing (a b : FourCoordinates) : ℝ :=
  (1 / 24 : ℝ) * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
    tangentWeight i * tangentWeight j * tangentWeight k * tangentWeight l *
      factorialPairing (a i j k l) (b i j k l)

theorem fourPairing_smul_left (c : ℝ) (a b : FourCoordinates) :
    fourPairing (c • a) b = c * fourPairing a b := by
  have h : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
      tangentWeight i * tangentWeight j * tangentWeight k * tangentWeight l *
        factorialPairing ((c • a) i j k l) (b i j k l)) =
      c * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
        tangentWeight i * tangentWeight j * tangentWeight k * tangentWeight l *
          factorialPairing (a i j k l) (b i j k l) := by
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [fourPairing, fourPairing, h]
  ring

theorem fourPairing_smul_right (c : ℝ) (a b : FourCoordinates) :
    fourPairing a (c • b) = c * fourPairing a b := by
  have h : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
      tangentWeight i * tangentWeight j * tangentWeight k * tangentWeight l *
        factorialPairing (a i j k l) ((c • b) i j k l)) =
      c * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
        tangentWeight i * tangentWeight j * tangentWeight k * tangentWeight l *
          factorialPairing (a i j k l) (b i j k l) := by
    simp only [Pi.smul_apply, map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [fourPairing, fourPairing, h]
  ring

/-- Pure combinatorial adjointness between `exteriorThree` and `contractionFour` against the
`fourPairing`/`threePairing` metrics, mirroring `exteriorTwo_contractionThree_adjoint` one degree
up: four pointwise self-adjoint moves of `infinitesimal (tangentFrame ·)` across the pairing,
reassembled via the three `IsAlternatingFour` relations into a single quadruple sum shared by both
sides. -/
theorem exteriorThree_contractionFour_adjoint (a : ThreeCoordinates) (b : FourCoordinates)
    (hb : IsAlternatingFour b) :
    fourPairing (exteriorThree a) b = threePairing a (contractionFour b) := by
  set F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ := fun p q r s =>
    tangentWeight p * tangentWeight q * tangentWeight r * tangentWeight s *
      factorialPairing (a p q r) (infinitesimal (tangentFrame s) (b s p q r)) with hF
  have hpoint : ∀ i j k l : Fin 5,
      tangentWeight i * tangentWeight j * tangentWeight k * tangentWeight l *
        factorialPairing (exteriorThree a i j k l) (b i j k l) =
        F j k l i + F i k l j + F i j l k + F i j k l := by
    intro i j k l
    have hj : factorialPairing (infinitesimal (tangentFrame j) (a i k l)) (b i j k l) =
        -factorialPairing (a i k l) (infinitesimal (tangentFrame j) (b j i k l)) := by
      rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem j).1, hb.1 i j k l]
      simp
    have hk : factorialPairing (infinitesimal (tangentFrame k) (a i j l)) (b i j k l) =
        factorialPairing (a i j l) (infinitesimal (tangentFrame k) (b k i j l)) := by
      rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem k).1, hb.2.1 i j k l]
    have hl : factorialPairing (infinitesimal (tangentFrame l) (a i j k)) (b i j k l) =
        -factorialPairing (a i j k) (infinitesimal (tangentFrame l) (b l i j k)) := by
      rw [infinitesimal_symmetric_adjoint _ (tangentFrame_mem l).1, hb.2.2 i j k l]
      simp
    simp only [exteriorThree, map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
      hj, hk, hl, infinitesimal_symmetric_adjoint _ (tangentFrame_mem i).1, hF]
    ring
  have hS1 : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F j k l i) =
      ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F i j k l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have hS2 : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F i k l j) =
      ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F i j k l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have hS3 : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F i j l k) =
      ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F i j k l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  have hRHS : threePairing a (contractionFour b) =
      (1 / 6 : ℝ) * ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, F i j k l := by
    rw [threePairing]
    apply congrArg ((1 / 6 : ℝ) * ·)
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [contractionFour, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, hF]
    ring
  rw [fourPairing]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [hS1, hS2, hS3, hRHS]
  ring

end TernaryPeriodPolynomials.Argument.Coercivity
