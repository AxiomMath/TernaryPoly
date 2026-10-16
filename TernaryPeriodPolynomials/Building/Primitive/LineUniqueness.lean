module

public import TernaryPeriodPolynomials.Building.Good.IntegralNormalization
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators
noncomputable section
namespace TernaryPoly.PrimitiveLineUniqueness

open ModThreeGoodAction GoodIntegralNormalization

/-- Explicit integral Bézout coefficients for the gcd of three coordinates. -/
theorem content_bezout (v : IntegralVector) :
    ∃ b : IntegralVector, ∑ i, b i * v i = (content v : ℤ) := by
  let d : ℤ := Int.gcd (v 1) (v 2)
  let a := Int.gcdA (v 0) d
  let b := Int.gcdB (v 0) d
  let c := Int.gcdA (v 1) (v 2)
  let e := Int.gcdB (v 1) (v 2)
  refine ⟨![a,c*b,e*b],?_⟩
  calc
    ∑ i, (![a,c*b,e*b] : IntegralVector) i * v i =
        v 0 * a + (v 1 * c + v 2 * e) * b := by
      simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
      ring
    _ = v 0 * a + d * b := by rw [show v 1 * c + v 2 * e = d from (Int.gcd_eq_gcd_ab _ _).symm]
    _ = (Int.gcd (v 0) d : ℤ) := (Int.gcd_eq_gcd_ab _ _).symm
    _ = (content v : ℤ) := by simp [d,content,Int.gcd_def]

/-- Primitivity gives an integral linear functional taking the vector to one. -/
theorem primitive_bezout {v : IntegralVector} (hv : Primitive v) :
    ∃ b : IntegralVector, ∑ i, b i * v i = 1 := by
  obtain ⟨b,hb⟩ := content_bezout v
  change content v = 1 at hv
  exact ⟨b,by simpa only [hv,Nat.cast_one] using hb⟩

/-- If a rational multiple of a primitive vector is integral, its scalar is integral. -/
theorem scalar_integral_of_primitive {v w : IntegralVector} (hv : Primitive v) {q : ℚ}
    (hq : rationalVector w = q • rationalVector v) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨b,hb⟩ := primitive_bezout hv
  have he (i : Fin 3) : (w i : ℚ) = q * (v i : ℚ) := congrFun hq i
  have hbq : ∑ i, (b i : ℚ) * (v i : ℚ) = 1 := by exact_mod_cast hb
  refine ⟨∑ i, b i * w i,?_⟩
  calc
    ((∑ i, b i * w i : ℤ) : ℚ) = ∑ i, (b i : ℚ) * (w i : ℚ) := by simp
    _ = q * ∑ i, (b i : ℚ) * (v i : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [he]
      ring
    _ = q := by rw [hbq,mul_one]

/-- All integral points on a primitive rational line are integer multiples of its generator. -/
theorem integer_multiple_of_mem_span {v w : IntegralVector} (hv : Primitive v)
    (hw : rationalVector w ∈ Submodule.span ℚ {rationalVector v}) :
    ∃ n : ℤ, w = fun i => n * v i := by
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨n,hn⟩ := scalar_integral_of_primitive hv hq.symm
  refine ⟨n,?_⟩
  funext i
  have hi : q * (v i : ℚ) = (w i : ℚ) := congrFun hq i
  rw [← hn] at hi
  exact_mod_cast hi.symm

/-- Multiplication by any integer scales coordinate content by its absolute value. -/
theorem content_int_mul (n : ℤ) (v : IntegralVector) :
    content (fun i => n * v i) = n.natAbs * content v := by
  simp only [content,Int.natAbs_mul,Nat.gcd_mul_left]

/-- Primitive integral points on the same rational line differ only by a sign. -/
theorem primitive_eq_or_neg_of_mem_span {v w : IntegralVector} (hv : Primitive v)
    (hw : Primitive w) (hmem : rationalVector w ∈ Submodule.span ℚ {rationalVector v}) :
    w = v ∨ w = -v := by
  obtain ⟨n,hn⟩ := integer_multiple_of_mem_span hv hmem
  have habs : n.natAbs = 1 := by
    have h := content_int_mul n v
    rw [← hn,hv,hw,mul_one] at h
    exact h.symm
  rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr habs) with h | h
  · left
    simpa only [h,one_mul] using hn
  · right
    funext i
    simpa only [h,neg_one_mul,Pi.neg_apply] using congrFun hn i

/-- Equality of primitive rational spans determines the integer generators up to sign. -/
theorem primitive_eq_or_neg_of_span_eq {v w : IntegralVector} (hv : Primitive v)
    (hw : Primitive w)
    (hspan : Submodule.span ℚ {rationalVector v} = Submodule.span ℚ {rationalVector w}) :
    v = w ∨ v = -w := by
  apply primitive_eq_or_neg_of_mem_span hw hv
  rw [← hspan]
  exact Submodule.mem_span_singleton_self _

/-- Residue-one normalization removes the remaining sign ambiguity. -/
theorem primitive_eq_of_residue_one_of_span_eq {v w : IntegralVector}
    (hv : Primitive v) (hw : Primitive w)
    (hsv : ∑ i, (v i : ZMod 3) = 1) (hsw : ∑ i, (w i : ZMod 3) = 1)
    (hspan : Submodule.span ℚ {rationalVector v} = Submodule.span ℚ {rationalVector w}) :
    v = w := by
  rcases primitive_eq_or_neg_of_span_eq hv hw hspan with h | h
  · exact h
  · have hc : (1 : ZMod 3) = -1 := calc
      1 = ∑ i, (v i : ZMod 3) := hsv.symm
      _ = -(∑ i, (w i : ZMod 3)) := by rw [h,residue_neg]
      _ = -1 := by rw [hsw]
    exact (show (1 : ZMod 3) ≠ -1 by decide) hc |>.elim

/-- Primitive integral vectors with the unique good-line residue normalization. -/
abbrev NormalizedPrimitiveVector :=
  {v : IntegralVector // Primitive v ∧ ∑ i, (v i : ZMod 3) = 1}

abbrev GoodLine := {L : RationalSubspace // Module.finrank ℚ L = 1 ∧ Good L}

/-- The genuine rational line spanned by a normalized primitive integer vector. -/
def normalizedLine (v : NormalizedPrimitiveVector) : GoodLine :=
  ⟨Submodule.span ℚ {rationalVector v.val},
    finrank_span_singleton (rationalVector_ne_zero (by rw [v.property.2]; exact one_ne_zero)),
    ⟨v.val,Submodule.mem_span_singleton_self _,by rw [v.property.2]; exact one_ne_zero⟩⟩

theorem normalizedLine_injective : Function.Injective normalizedLine := by
  intro v w h
  apply Subtype.ext
  exact primitive_eq_of_residue_one_of_span_eq v.property.1 w.property.1
    v.property.2 w.property.2 (congrArg Subtype.val h)

theorem normalizedLine_surjective : Function.Surjective normalizedLine := by
  intro L
  obtain ⟨v,hp,_,_,hs,hr⟩ := good_line_primitive_generator L.property.1 L.property.2
  exact ⟨⟨v,hp,hr⟩,Subtype.ext hs⟩

/-- Good rational lines are in bijection with their unique normalized primitive integer vectors. -/
def normalizedPrimitiveEquiv : NormalizedPrimitiveVector ≃ GoodLine :=
  Equiv.ofBijective normalizedLine ⟨normalizedLine_injective,normalizedLine_surjective⟩

end TernaryPoly.PrimitiveLineUniqueness
