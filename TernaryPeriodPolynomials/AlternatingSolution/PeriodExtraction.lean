module

public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Symmetry
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodEquation
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodLift
public import TernaryPeriodPolynomials.AlternatingSolution.ToddLinearity
public import TernaryPeriodPolynomials.Analysis.CoordinateSumQuotient
public import TernaryPeriodPolynomials.PeriodPolynomial.Lift.JetRecovery

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The actual binary period polynomial extracted from an odd alternating solution. -/
def extractedBinaryPeriod (n : ℕ) (f : TernaryPolynomial) : MvPolynomial (Fin 2) ℚ :=
  binaryPeriodPrimitive n (binaryFirstJetPrimitive f)

/-- Every required binary period relation is supplied by the actual ternary equations. -/
theorem extractedBinaryPeriod_relations_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) : BinaryPeriodRelations (extractedBinaryPeriod n f) := by
  have hx := binaryFirstJetPrimitive_even_first_of_todd_derivative hf hodd hc hs hJ
  have hy := binaryFirstJetPrimitive_odd_second_of_todd_derivative hf hodd hc hs hJ
  have haxis := binaryFirstJetPrimitive_axis_first f
  refine ⟨binaryPeriodPrimitive_swap n hy, binaryPeriodPrimitive_even_first n hx hy,
    binaryPeriodPrimitive_even_second n hx hy, binaryPeriodPrimitive_axis_first n haxis,
    binaryPeriodPrimitive_axis_second n haxis, ?_⟩
  exact binaryPeriodPrimitive_period_equation _ _ n
    (binaryFirstJetPrimitive_isHomogeneous hf hodd)
    (binaryFirstJetPrimitive_rotation_pderiv_of_todd_derivative hf hodd hc hs hJ) hx hy haxis
    (binaryBoundary_swap hf hodd hs) (binaryFirstJetPrimitive_difference_of_todd_derivative hf hodd hc hs hJ)

/-- The original norm hypotheses provide the same binary relations. -/
theorem extractedBinaryPeriod_relations {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) : BinaryPeriodRelations (extractedBinaryPeriod n f) :=
  extractedBinaryPeriod_relations_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

/-- The cyclic numerator has a polynomial quotient whose entire Todd expression vanishes. -/
theorem binaryPeriodLift_exists_quotient {q : MvPolynomial (Fin 2) ℚ}
    (hq : BinaryPeriodRelations q) :
    ∃ g : TernaryPolynomial,
      binaryPeriodLift q = (X 0+X 1+X 2)*g ∧ alternatingTodd g = 0 := by
  obtain ⟨g, hg⟩ := coordinate_sum_dvd_binaryPeriodLift hq
  refine ⟨g, hg, ?_⟩
  have hz := alternatingTodd_binaryPeriodLift_eq_zero hq
  rw [hg, show (X 0+X 1+X 2)*g = (X 0+X 1+X 2)^1*g by simp,
    alternatingTodd_W_pow_mul, pow_one] at hz
  have hlin : (X 2-3*X 1 : TernaryPolynomial) ≠ 0 := by
    intro he
    have ht := congrArg (bind₁ (![0,0,1] : Fin 3 → TernaryPolynomial)) he
    simp at ht
  exact (mul_eq_zero.mp hz).resolve_left hlin

/-- The extracted binary polynomial therefore provides a genuine whole-Todd-kernel lift. -/
theorem extractedBinaryPeriod_exists_quotient {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    ∃ g : TernaryPolynomial,
      binaryPeriodLift (extractedBinaryPeriod n f) = (X 0+X 1+X 2)*g ∧
        alternatingTodd g = 0 :=
  binaryPeriodLift_exists_quotient (extractedBinaryPeriod_relations hf hodd hc hs hn)

/-- Extraction from the differential Todd kernel provides a whole-Todd-kernel lift. -/
theorem extractedBinaryPeriod_exists_quotient_of_todd_derivative
    {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    ∃ g : TernaryPolynomial,
      binaryPeriodLift (extractedBinaryPeriod n f) = (X 0+X 1+X 2)*g ∧
        alternatingTodd g = 0 :=
  binaryPeriodLift_exists_quotient
    (extractedBinaryPeriod_relations_of_todd_derivative hf hodd hc hs hJ)

/-- The extracted polynomial has homogeneous degree one greater than its source. -/
theorem extractedBinaryPeriod_isHomogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) :
    (extractedBinaryPeriod n f).IsHomogeneous (n+1) :=
  binaryPeriodPrimitive_isHomogeneous (binaryFirstJetPrimitive_isHomogeneous hf hodd)

/-- Normalized first-jet primitives commute with subtraction. -/
theorem binaryFirstJetPrimitive_sub (f g : TernaryPolynomial) :
    binaryFirstJetPrimitive (f-g) = binaryFirstJetPrimitive f-binaryFirstJetPrimitive g := by
  simp only [binaryFirstJetPrimitive, map_sub, binaryBoundary]
  rw [show pderiv 0 f-pderiv 0 g+(pderiv 1 f-pderiv 1 g) =
    (pderiv 0 f+pderiv 1 f)-(pderiv 0 g+pderiv 1 g) by abel]
  simp only [map_sub, neg_sub_neg, neg_sub]

/-- The extracted whole-Todd-kernel lift matches the original primitive and degree. -/
theorem extractedBinaryPeriod_lift_data {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    ∃ l : TernaryPolynomial,
      binaryPeriodLift (extractedBinaryPeriod n f) = (X 0+X 1+X 2)*l ∧
      l.IsHomogeneous n ∧ C l = l ∧ S l = -l ∧ alternatingTodd l = 0 ∧
      binaryFirstJetPrimitive (f-l) = 0 := by
  obtain ⟨l, hl, hj⟩ := extractedBinaryPeriod_exists_quotient_of_todd_derivative hf hodd hc hs hJ
  have hq := extractedBinaryPeriod_relations_of_todd_derivative hf hodd hc hs hJ
  have hdeg : ((X 0+X 1+X 2)*l).IsHomogeneous (1+n) := by
    rw [← hl, Nat.add_comm]
    exact binaryPeriodLift_isHomogeneous (extractedBinaryPeriod_isHomogeneous hf hodd)
  have hd := isHomogeneous_quotient_add coordinate_sum_isHomogeneous coordinate_sum_ne_zero hdeg
  have hcl : C l = l := by
    apply cyclic_of_coordinate_sum_pow_mul 1
    simpa only [pow_one, ← hl] using binaryPeriodLift_cyclic (extractedBinaryPeriod n f)
  have hsl : S l = -l := by
    apply alternating_of_coordinate_sum_pow_mul 1
    simpa only [pow_one, ← hl] using binaryPeriodLift_alternating hq
  refine ⟨l, hl, hd, hcl, hsl, hj, ?_⟩
  rw [binaryFirstJetPrimitive_sub, binaryFirstJetPrimitive_binaryPeriodLift_quotient hq l hl]
  have hp := binaryPeriodPrimitive_pderiv (binaryFirstJetPrimitive_isHomogeneous hf hodd)
    (binaryFirstJetPrimitive_rotation_pderiv_of_todd_derivative hf hodd hc hs hJ)
  change binaryFirstJetPrimitive f - -pderiv 1
    (binaryPeriodPrimitive n (binaryFirstJetPrimitive f)) = 0
  rw [hp, neg_neg, sub_self]

end TernaryPoly
