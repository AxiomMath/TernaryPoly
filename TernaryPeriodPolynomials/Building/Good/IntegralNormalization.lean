module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.Data.Int.GCD

@[expose] public section

open scoped BigOperators
noncomputable section
namespace TernaryPoly.GoodIntegralNormalization

open ModThreeGoodAction

/-- The positive common divisor of all three integer coordinates. -/
def content (v : IntegralVector) : ℕ :=
  (v 0).natAbs.gcd ((v 1).natAbs.gcd (v 2).natAbs)

/-- An integer vector is primitive precisely when its coordinate gcd is one. -/
def Primitive (v : IntegralVector) : Prop := content v = 1

/-- Divide all coordinates by their common divisor. -/
def primitivePart (v : IntegralVector) : IntegralVector := fun i => v i / (content v : ℤ)

theorem content_dvd (v : IntegralVector) (i : Fin 3) : (content v : ℤ) ∣ v i := by
  apply Int.ofNat_dvd_left.mpr
  fin_cases i
  · exact Nat.gcd_dvd_left _ _
  · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)

theorem content_ne_zero {v : IntegralVector} (hv : ∑ i, (v i : ZMod 3) ≠ 0) :
    content v ≠ 0 := by
  intro h
  have hz (i : Fin 3) : v i = 0 := by
    have hi := content_dvd v i
    rw [h,Nat.cast_zero,zero_dvd_iff] at hi
    exact hi
  simp [hz] at hv

theorem mul_primitivePart (v : IntegralVector) (i : Fin 3) :
    (content v : ℤ) * primitivePart v i = v i := by
  exact Int.mul_ediv_cancel' (content_dvd v i)

theorem content_mul (d : ℕ) (v : IntegralVector) :
    content (fun i => (d : ℤ) * v i) = d * content v := by
  simp only [content,Int.natAbs_mul,Int.natAbs_natCast,Nat.gcd_mul_left]

theorem primitivePart_primitive {v : IntegralVector} (hv : content v ≠ 0) :
    Primitive (primitivePart v) := by
  have he : (fun i => (content v : ℤ) * primitivePart v i) = v :=
    funext (mul_primitivePart v)
  have h := content_mul (content v) (primitivePart v)
  rw [he] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hv) (by simpa only [mul_one] using h.symm)

theorem rationalVector_primitivePart (v : IntegralVector) :
    (content v : ℚ) • rationalVector (primitivePart v) = rationalVector v := by
  funext i
  change (content v : ℚ) * (primitivePart v i : ℚ) = (v i : ℚ)
  exact_mod_cast mul_primitivePart v i

theorem residue_primitivePart (v : IntegralVector) :
    (content v : ZMod 3) * (∑ i, (primitivePart v i : ZMod 3)) =
      ∑ i, (v i : ZMod 3) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun z : ℤ => (z : ZMod 3)) (mul_primitivePart v i)
  simpa only [Int.cast_mul,Int.cast_natCast] using h

/-- A good witness remains good after division, including at the prime three. -/
theorem primitivePart_good_residue {v : IntegralVector} (hv : ∑ i, (v i : ZMod 3) ≠ 0) :
    (content v : ZMod 3) ≠ 0 ∧ ∑ i, (primitivePart v i : ZMod 3) ≠ 0 := by
  have h : (content v : ZMod 3) * (∑ i, (primitivePart v i : ZMod 3)) ≠ 0 := by
    rwa [residue_primitivePart]
  constructor
  · intro hd
    exact h (by rw [hd,zero_mul])
  · intro hs
    exact h (by rw [hs,mul_zero])

theorem primitivePart_mem {L : RationalSubspace} {v : IntegralVector}
    (hv : rationalVector v ∈ L) (hgood : ∑ i, (v i : ZMod 3) ≠ 0) :
    rationalVector (primitivePart v) ∈ L := by
  have hd : (content v : ℚ) ≠ 0 := by exact_mod_cast content_ne_zero hgood
  apply (L.smul_mem_iff hd).mp
  rwa [rationalVector_primitivePart]

theorem Primitive.neg {v : IntegralVector} (hv : Primitive v) : Primitive (-v) := by
  simpa [Primitive,content] using hv

theorem rationalVector_neg (v : IntegralVector) : rationalVector (-v) = -rationalVector v := by
  ext i
  simp [rationalVector]

theorem residue_neg (v : IntegralVector) : (∑ i, ((-v) i : ZMod 3)) = -(∑ i, (v i : ZMod 3)) := by
  simp

theorem residue_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ -a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every good subspace contains a primitive witness with coordinate-sum residue one. -/
theorem exists_primitive_residue_one {L : RationalSubspace} (hL : Good L) :
    ∃ v : IntegralVector, Primitive v ∧ rationalVector v ∈ L ∧
      ∑ i, (v i : ZMod 3) = 1 := by
  obtain ⟨v,hv,hgood⟩ := hL
  have hp := primitivePart_primitive (content_ne_zero hgood)
  have hm := primitivePart_mem hv hgood
  rcases residue_one_or_neg_one _ (primitivePart_good_residue hgood).2 with hs | hs
  · exact ⟨primitivePart v,hp,hm,hs⟩
  · refine ⟨-primitivePart v,hp.neg,?_,?_⟩
    · rw [rationalVector_neg]
      exact L.neg_mem hm
    · rwa [residue_neg]

/-- A residue-one integral vector is nonzero. -/
theorem ne_zero_of_residue_one {v : IntegralVector} (hv : ∑ i, (v i : ZMod 3) = 1) :
    v ≠ 0 := by
  intro h
  simp [h] at hv

/-- A nonzero vector in a rational line spans that line. -/
theorem span_eq_of_mem_line {L : RationalSubspace} (hd : Module.finrank ℚ L = 1)
    {v : IntegralVector} (hv : rationalVector v ∈ L) (hs : ∑ i, (v i : ZMod 3) ≠ 0) :
    Submodule.span ℚ {rationalVector v} = L := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by intro w hw; rcases hw with rfl; exact hv)
  · rw [finrank_span_singleton (rationalVector_ne_zero hs),hd]

/-- Every good rational line has a primitive integral generator normalized modulo three. -/
theorem good_line_primitive_generator {L : RationalSubspace} (hd : Module.finrank ℚ L = 1)
    (hL : Good L) :
    ∃ v : IntegralVector, Primitive v ∧ v ≠ 0 ∧ rationalVector v ∈ L ∧
      Submodule.span ℚ {rationalVector v} = L ∧ ∑ i, (v i : ZMod 3) = 1 := by
  obtain ⟨v,hp,hm,hs⟩ := exists_primitive_residue_one hL
  refine ⟨v,hp,ne_zero_of_residue_one hs,hm,?_,hs⟩
  apply span_eq_of_mem_line hd hm
  rw [hs]
  exact one_ne_zero

end TernaryPoly.GoodIntegralNormalization
