module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingAction
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperDiscrete

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpaceRationalGluing SymmetricSpaceRationalAction
open SymmetricSpaceArithmeticProper

abbrev IntegralGL := Matrix.GeneralLinearGroup (Fin 3) ℤ

/-- The literal rational matrix relating an arithmetic translate of frame a to frame b. -/
def relative (a b : RationalGL) (g : IntegralGL) : RationalGL := b⁻¹*integralRational g*a

/-- Rational scalar extension of integral invertible matrices is injective. -/
theorem integralRational_injective : Function.Injective integralRational := by
  intro g h he
  apply Units.ext
  ext i j
  have e := congrArg (fun r : RationalGL => r.val i j) he
  change (g.val i j : ℚ)=(h.val i j : ℚ) at e
  exact_mod_cast e

theorem relative_injective (a b : RationalGL) : Function.Injective (relative a b) := by
  intro g h he
  apply integralRational_injective
  exact mul_left_cancel (mul_right_cancel he)

/-- Common-denominator proof specialized from the OrdinaryHeckeArithmetic API.
-/
theorem finite_denominator {ι : Type} [Fintype ι] (f : ι → ℚ) :
    ∃ d : ℕ,d≠0 ∧ ∀ i,∃ z : ℤ,(z : ℚ)=(d : ℚ)*f i := by
  classical
  let d := ∏ i,(f i).den
  refine ⟨d,Finset.prod_ne_zero_iff.mpr (fun i _ => (f i).den_ne_zero),?_⟩
  intro i
  obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem (fun i => (f i).den) (Finset.mem_univ i)
  refine ⟨(k : ℤ)*(f i).num,?_⟩
  change _=(∏ i,(f i).den : ℕ)*f i
  rw [hk,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
  rw [mul_right_comm,Rat.den_mul_eq_num,mul_comm]

/-- Every entry of every relative matrix has one denominator depending only on the two frames. -/
theorem relative_denominator (a b : RationalGL) :
    ∃ d : ℕ, d≠0 ∧ ∀ g : IntegralGL, ∀ i j, ∃ z : ℤ,
      (z : ℚ)=(d : ℚ)*(relative a b g).val i j := by
  obtain ⟨d,hd,h⟩ := finite_denominator
    (fun v : (Fin 3 × Fin 3) × (Fin 3 × Fin 3) => b⁻¹.val v.1.1 v.2.1*a.val v.2.2 v.1.2)
  choose z hz using h
  refine ⟨d,hd,?_⟩
  intro g i j
  refine ⟨∑ k,∑ l,z ((i,j),(k,l))*g.val k l,?_⟩
  simp only [Int.cast_sum,Int.cast_mul,hz]
  change (∑ k,∑ l,(d*(b⁻¹.val i k*a.val l j))*(g.val k l : ℚ))=
    d*((b⁻¹.val*(integralRational g).val*a.val) i j)
  simp only [Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (d : ℚ)*(b⁻¹.val i l*a.val k j)*(g.val l k : ℚ)=
    (d : ℚ)*(b⁻¹.val i l*(g.val l k : ℚ)*a.val k j)
  ring

/-- A fixed denominator gives a uniform positive lower bound for every nonzero entry. -/
theorem denominator_lower_bound (d : ℕ) (hd : d≠0) (q : ℚ)
    (hq : q≠0) (h : ∃ z : ℤ,(z : ℚ)=(d : ℚ)*q) : 1/(d : ℝ)≤|(q : ℝ)| := by
  obtain ⟨z,hz⟩ := h
  have hdQ : (d : ℚ)≠0 := by exact_mod_cast hd
  have hzQ : (z : ℚ)≠0 := by rw [hz]; exact mul_ne_zero hdQ hq
  have hz0 : z≠0 := by exact_mod_cast hzQ
  have hz1 : (1 : ℤ)≤|z| := by have := abs_pos.mpr hz0; omega
  have hzR : (z : ℝ)=(d : ℝ)*(q : ℝ) := by exact_mod_cast hz
  have hdR : 0<(d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hz1R : (1 : ℝ)≤|(z : ℝ)| := by exact_mod_cast hz1
  rw [hzR,abs_mul,abs_of_pos hdR] at hz1R
  exact (div_le_iff₀ hdR).mpr (by simpa [mul_comm] using hz1R)

/-- A bounded rational matrix family with one common denominator is finite. -/
theorem finite_rational_entry_bound (d : ℕ) (hd : d≠0) (R : ℝ) :
    {r : RationalGL | (∀ i j,∃ z : ℤ,(z : ℚ)=(d : ℚ)*r.val i j) ∧
      ∀ i j,|(r.val i j : ℝ)|≤R}.Finite := by
  let N : ℤ := ⌈(d : ℝ)*R⌉
  let S : Set ℚ := (fun z : ℤ => (z : ℚ)/(d : ℚ)) '' Set.Icc (-N) N
  have hS : S.Finite := (Set.finite_Icc (-N) N).image _
  have hM : {m : Matrix (Fin 3) (Fin 3) ℚ | ∀ i j,m i j∈S}.Finite :=
    Set.Finite.pi' (fun _ => Set.Finite.pi' (fun _ => hS))
  refine Set.Finite.of_injOn (f := fun r : RationalGL => r.val) ?_ Units.val_injective.injOn hM
  intro r hr i j
  obtain ⟨z,hz⟩ := hr.1 i j
  have hzR : (z : ℝ)=(d : ℝ)*(r.val i j : ℝ) := by exact_mod_cast hz
  have hb : |(z : ℝ)|≤(d : ℝ)*R := by
    rw [hzR,abs_mul,abs_of_nonneg (Nat.cast_nonneg d)]
    exact mul_le_mul_of_nonneg_left (hr.2 i j) (Nat.cast_nonneg d)
  have hb' := abs_le.mp (hb.trans (Int.le_ceil _))
  refine ⟨z,⟨?_,?_⟩,?_⟩
  · exact_mod_cast hb'.1
  · exact_mod_cast hb'.2
  · apply (div_eq_iff (by exact_mod_cast hd : (d : ℚ)≠0)).mpr
    simpa [mul_comm] using hz

/-- A real entry bound on actual relative arithmetic matrices implies finite transporters. -/
theorem finite_relative_entry_bound (a b : RationalGL) (R : ℝ) :
    {g : IntegralGL | ∀ i j,|((relative a b g).val i j : ℝ)|≤R}.Finite := by
  obtain ⟨d,hd,hden⟩ := relative_denominator a b
  refine Set.Finite.of_injOn (f := relative a b) ?_ (relative_injective a b).injOn
    (finite_rational_entry_bound d hd R)
  intro g hg
  exact ⟨hden g,hg⟩

end TernaryPoly.SymmetricSpaceGluedArithmetic
