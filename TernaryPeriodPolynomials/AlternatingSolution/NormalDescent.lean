module

public import TernaryPeriodPolynomials.AlternatingSolution.PeriodExtraction
public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.SquareDivisibility

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The actual alternating Todd expression is additive. -/
theorem alternatingTodd_add (f g : TernaryPolynomial) :
    alternatingTodd (f+g) = alternatingTodd f+alternatingTodd g := by
  simp only [alternatingTodd, alternatingFrame1, alternatingFrame2, substitute3,
    map_add, ternaryTodd]
  ring

/-- The actual alternating Todd expression respects subtraction. -/
theorem alternatingTodd_sub (f g : TernaryPolynomial) :
    alternatingTodd (f-g) = alternatingTodd f-alternatingTodd g := by
  have hframe : alternatingFrame2 (f-g) = alternatingFrame2 f-alternatingFrame2 g := by
    simp only [alternatingFrame2, alternatingFrame1, substitute3, map_sub]
    abel
  simp only [alternatingTodd, hframe, alternatingFrame1, substitute3, map_sub,
    ternaryTodd]
  ring

@[simp] theorem alternatingTodd_zero : alternatingTodd 0 = 0 := by
  simp [alternatingTodd, ternaryTodd, alternatingFrame1, alternatingFrame2, substitute3]

/-- The image of the coordinate sum in every frame is nonzero. -/
theorem frame_sum_ne_zero : (X 2-3*X 1 : TernaryPolynomial) ≠ 0 := by
  intro h
  have h' := congrArg (bind₁ (![0,0,1] : Fin 3 → TernaryPolynomial)) h
  simp at h'

/-- Division by coordinate-sum powers preserves the differential Todd kernel. -/
theorem todd_derivative_of_coordinate_sum_pow_mul {f : TernaryPolynomial} (r : ℕ)
    (hJ : pderiv 0 (alternatingTodd ((X 0+X 1+X 2)^r*f)) = 0) :
    pderiv 0 (alternatingTodd f) = 0 := by
  rw [alternatingTodd_W_pow_mul] at hJ
  have hd : pderiv (0 : Fin 3) ((X 2-3*X 1 : TernaryPolynomial)^r) = 0 := by
    rw [show (3 : TernaryPolynomial) = MvPolynomial.C (3 : ℚ) by rfl]
    simp
  rw [pderiv_mul, hd, zero_mul, zero_add] at hJ
  exact (mul_eq_zero.mp hJ).resolve_left (pow_ne_zero r frame_sum_ne_zero)

/-- A normal descent step removes a kernel lift and leaves a double-plane factor. -/
theorem alternating_normal_step {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    ∃ l g : TernaryPolynomial,
      f = l+(X 0+X 1+X 2)^2*g ∧
      binaryPeriodLift (extractedBinaryPeriod n f) = (X 0+X 1+X 2)*l ∧
      g.IsHomogeneous (n-2) ∧ C g = g ∧ S g = -g ∧
      pderiv 0 (alternatingTodd g) = 0 ∧
      (g ≠ 0 → 2 ≤ n) := by
  obtain ⟨l, hl, hld, hlc, hls, hlj, hlp⟩ := extractedBinaryPeriod_lift_data hf hodd hc hs hJ
  have hrc : C (f-l) = f-l := by rw [map_sub, hc, hlc]
  have hrs : S (f-l) = -(f-l) := by rw [map_sub, hs, hls]; abel
  have hrh := hf.sub hld
  obtain ⟨g, hg⟩ := coordinateSum_sq_dvd_of_binaryFirstJetPrimitive_eq_zero hrh hodd.pos hrc hlp
  have hWh : ((X 0+X 1+X 2 : TernaryPolynomial)^2).IsHomogeneous 2 := by
    simpa only [one_mul] using coordinate_sum_isHomogeneous.pow 2
  have hW0 := pow_ne_zero 2 coordinate_sum_ne_zero
  have hgh : ((X 0+X 1+X 2)^2*g).IsHomogeneous n := by rwa [← hg]
  have hgc : C g = g := cyclic_of_coordinate_sum_pow_mul 2 (by rwa [← hg])
  have hgs : S g = -g := alternating_of_coordinate_sum_pow_mul 2 (by rwa [← hg])
  have hgj : pderiv 0 (alternatingTodd g) = 0 := by
    apply todd_derivative_of_coordinate_sum_pow_mul 2
    rw [← hg, alternatingTodd_sub, hlj, sub_zero]
    exact hJ
  refine ⟨l,g,?_,hl,isHomogeneous_quotient hWh hW0 hgh,hgc,hgs,hgj,?_⟩
  · rw [← hg]; abel
  · intro hg0
    have ht := hgh.totalDegree (mul_ne_zero hW0 hg0)
    rw [totalDegree_mul_of_isDomain hW0 hg0, hWh.totalDegree hW0] at ht
    omega

/-- Strong induction through all normal layers, with no bound on the polynomial degree. -/
theorem alternating_normal_induction (P : TernaryPolynomial → Prop)
    (hzero : P 0)
    (hlift : ∀ (q : MvPolynomial (Fin 2) ℚ), BinaryPeriodRelations q →
      ∀ l : TernaryPolynomial, binaryPeriodLift q = (X 0+X 1+X 2)*l → P l)
    (hstep : ∀ l g : TernaryPolynomial, P l → P g → P (l+(X 0+X 1+X 2)^2*g))
    {n : ℕ} {f : TernaryPolynomial} (hf : f.IsHomogeneous n) (hodd : Odd n)
    (hc : C f = f) (hs : S f = -f) (hJ : pderiv 0 (alternatingTodd f) = 0) : P f := by
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    obtain ⟨l,g,hfg,hl,hgh,hgc,hgs,hgj,hge⟩ := alternating_normal_step hf hodd hc hs hJ
    rw [hfg]
    apply hstep l g
    · exact hlift _ (extractedBinaryPeriod_relations_of_todd_derivative hf hodd hc hs hJ) l hl
    · by_cases hg0 : g = 0
      · simpa only [hg0] using hzero
      · have hge := hge hg0
        apply ih (n-2) (by omega) hgh
        · exact Nat.Odd.sub_even hge hodd (by decide : Even (2 : ℕ))
        · exact hgc
        · exact hgs
        · exact hgj

/-- The whole Todd polynomial vanishes on every odd homogeneous alternating differential-kernel element. -/
theorem alternatingTodd_eq_zero_of_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) : alternatingTodd f = 0 := by
  apply alternating_normal_induction (fun p => alternatingTodd p = 0) alternatingTodd_zero
    ?_ ?_ hf hodd hc hs hJ
  · intro q hq l hl
    have h := alternatingTodd_binaryPeriodLift_eq_zero hq
    rw [hl, show (X 0+X 1+X 2)*l = (X 0+X 1+X 2)^1*l by simp,
      alternatingTodd_W_pow_mul, pow_one] at h
    exact (mul_eq_zero.mp h).resolve_left frame_sum_ne_zero
  · intro l g hl hg
    rw [alternatingTodd_add, alternatingTodd_W_pow_mul, hl, hg, mul_zero, add_zero]

/-- The exact norm hypotheses force the entire corrected Todd polynomial to vanish. -/
theorem alternatingTodd_eq_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) : alternatingTodd f = 0 :=
  alternatingTodd_eq_zero_of_derivative hf hodd hc hs (pderiv_zero_alternatingTodd hc hs hn)

end TernaryPoly
