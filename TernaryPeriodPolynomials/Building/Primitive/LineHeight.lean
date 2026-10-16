module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Topology.Rational.LineBasis
public import TernaryPeriodPolynomials.Building.Primitive.LineUniqueness
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Int.DivMod

@[expose] public section

noncomputable section
namespace TernaryPoly.PrimitiveLineHeight
open ModThreeGoodAction GoodIntegralNormalization AugmentedFrameComplex
open RationalLineBasis PrimitiveLineUniqueness

/-- A chosen primitive integral generator of every actual rational line, including bad lines. -/
def primitiveGenerator (L : RationalLine) : IntegralVector :=
  (rationalLine_primitive_generator L).choose

theorem primitiveGenerator_primitive (L : RationalLine) : Primitive (primitiveGenerator L) :=
  (rationalLine_primitive_generator L).choose_spec.1

theorem primitiveGenerator_ne_zero (L : RationalLine) : rationalVector (primitiveGenerator L) ≠ 0 :=
  (rationalLine_primitive_generator L).choose_spec.2.1

theorem primitiveGenerator_span (L : RationalLine) :
    Submodule.span ℚ {rationalVector (primitiveGenerator L)} = L.val :=
  (rationalLine_primitive_generator L).choose_spec.2.2

/-- Primitive height for an arbitrary integral linear functional. -/
def height (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) : ℕ :=
  (F (primitiveGenerator L)).natAbs

/-- The height is independent of the chosen primitive generator. -/
theorem height_eq_natAbs (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine)
    {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) :
    height F L = (F v).natAbs := by
  rcases primitive_eq_or_neg_of_span_eq (primitiveGenerator_primitive L) hv
    ((primitiveGenerator_span L).trans hs.symm) with h | h
  · simp only [height,h]
  · simp only [height,h,map_neg,Int.natAbs_neg]

/-- Any two primitive generators of the same line give the same height. -/
theorem natAbs_eq_of_span_eq (F : IntegralVector →ₗ[ℤ] ℤ)
    {v w : IntegralVector} (hv : Primitive v) (hw : Primitive w)
    (hs : Submodule.span ℚ {rationalVector v} = Submodule.span ℚ {rationalVector w}) :
    (F v).natAbs = (F w).natAbs := by
  rcases primitive_eq_or_neg_of_span_eq hv hw hs with h | h
  · rw [h]
  · rw [h,map_neg,Int.natAbs_neg]

@[simp] theorem height_neg_functional (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    height (-F) L = height F L := by simp [height]

/-- Negating a generator preserves its actual rational span. -/
theorem span_neg (v : IntegralVector) :
    Submodule.span ℚ {rationalVector (-v)} = Submodule.span ℚ {rationalVector v} := by
  rw [rationalVector_neg,← neg_one_smul ℚ (rationalVector v)]
  exact Submodule.span_singleton_smul_eq (show IsUnit (-1 : ℚ) by norm_num) (rationalVector v)

/-- Choose the sign of the primitive generator so the functional is nonnegative. -/
def nonnegativeRepresentative (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) : IntegralVector :=
  if 0 ≤ F (primitiveGenerator L) then primitiveGenerator L else -primitiveGenerator L

theorem nonnegativeRepresentative_primitive (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    Primitive (nonnegativeRepresentative F L) := by
  unfold nonnegativeRepresentative
  split_ifs
  · exact primitiveGenerator_primitive L
  · exact (primitiveGenerator_primitive L).neg

theorem nonnegativeRepresentative_span (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    Submodule.span ℚ {rationalVector (nonnegativeRepresentative F L)} = L.val := by
  unfold nonnegativeRepresentative
  split_ifs
  · exact primitiveGenerator_span L
  · rw [span_neg,primitiveGenerator_span]

theorem nonnegativeRepresentative_ne_zero (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    rationalVector (nonnegativeRepresentative F L) ≠ 0 := by
  unfold nonnegativeRepresentative
  split_ifs
  · exact primitiveGenerator_ne_zero L
  · rw [rationalVector_neg]
    exact neg_ne_zero.mpr (primitiveGenerator_ne_zero L)

/-- The normalized generator reconstructs the original actual rational-line vertex. -/
theorem nonnegativeRepresentative_line (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    vectorLine (rationalVector (nonnegativeRepresentative F L))
      (nonnegativeRepresentative_ne_zero F L) = L :=
  Subtype.ext (nonnegativeRepresentative_span F L)

theorem nonnegativeRepresentative_nonneg (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    0 ≤ F (nonnegativeRepresentative F L) := by
  unfold nonnegativeRepresentative
  split_ifs with h
  · exact h
  · rw [map_neg]
    omega

theorem nonnegativeRepresentative_height (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    (F (nonnegativeRepresentative F L)).natAbs = height F L :=
  (height_eq_natAbs F L (nonnegativeRepresentative_primitive F L)
    (nonnegativeRepresentative_span F L)).symm

/-- The value of the normalized generator is literally the natural height, cast to integers. -/
theorem nonnegativeRepresentative_value (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine) :
    F (nonnegativeRepresentative F L) = (height F L : ℤ) := by
  rw [← nonnegativeRepresentative_height F L,Int.natCast_natAbs,
    abs_of_nonneg (nonnegativeRepresentative_nonneg F L)]

/-- Normalization changes an arbitrary primitive representative by at most its sign. -/
theorem nonnegativeRepresentative_eq_or_neg (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine)
    {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) :
    nonnegativeRepresentative F L = v ∨ nonnegativeRepresentative F L = -v :=
  primitive_eq_or_neg_of_span_eq (nonnegativeRepresentative_primitive F L) hv
    ((nonnegativeRepresentative_span F L).trans hs.symm)

/-- A primitive generator has height zero exactly when the functional vanishes on it. -/
theorem height_eq_zero_iff (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine)
    {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) :
    height F L = 0 ↔ F v = 0 := by
  rw [height_eq_natAbs F L hv hs,Int.natAbs_eq_zero]

/-- At positive height the nonnegative primitive generator is unique. -/
theorem eq_of_nonnegative_of_height_pos (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine)
    {v w : IntegralVector} (hv : Primitive v) (hw : Primitive w)
    (hsv : Submodule.span ℚ {rationalVector v} = L.val)
    (hsw : Submodule.span ℚ {rationalVector w} = L.val)
    (hv0 : 0 ≤ F v) (hw0 : 0 ≤ F w) (hp : 0 < height F L) : v = w := by
  rcases primitive_eq_or_neg_of_span_eq hv hw (hsv.trans hsw.symm) with h | h
  · exact h
  · have he : F v = 0 := by
      have hn : F v = -F w := by rw [h,map_neg]
      omega
    have hz := (height_eq_zero_iff F L hv hsv).mpr he
    omega

/-- A nonnegative primitive representative with positive height equals the chosen one. -/
theorem nonnegativeRepresentative_eq (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine)
    {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val)
    (hv0 : 0 ≤ F v) (hp : 0 < height F L) : nonnegativeRepresentative F L = v :=
  eq_of_nonnegative_of_height_pos F L (nonnegativeRepresentative_primitive F L) hv
    (nonnegativeRepresentative_span F L) hs (nonnegativeRepresentative_nonneg F L) hv0 hp

/-- At height zero both signs remain legitimate nonnegative primitive representatives. -/
theorem zero_height_sign_ambiguity (F : IntegralVector →ₗ[ℤ] ℤ) (L : RationalLine)
    {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) (hz : height F L = 0) :
    F v = 0 ∧ F (-v) = 0 ∧ Primitive (-v) ∧
      Submodule.span ℚ {rationalVector (-v)} = L.val := by
  have he := (height_eq_zero_iff F L hv hs).mp hz
  exact ⟨he,by rw [map_neg,he,neg_zero],hv.neg,(span_neg v).trans hs⟩

/-- The standard last-coordinate functional used in the rank-three height induction. -/
def lastCoordinate : IntegralVector →ₗ[ℤ] ℤ := LinearMap.proj 2

@[simp] theorem lastCoordinate_apply (v : IntegralVector) : lastCoordinate v = v 2 := rfl

/-- Last-coordinate height on every rational line. -/
def lastHeight (L : RationalLine) : ℕ := height lastCoordinate L

theorem lastHeight_eq_natAbs (L : RationalLine) {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) : lastHeight L = (v 2).natAbs :=
  height_eq_natAbs lastCoordinate L hv hs

theorem lastRepresentative_coordinate (L : RationalLine) :
    nonnegativeRepresentative lastCoordinate L 2 = (lastHeight L : ℤ) :=
  nonnegativeRepresentative_value lastCoordinate L

/-- The elementary remainder vector; no primitivity or frame claim is made by this definition. -/
def remainderVector (F : IntegralVector →ₗ[ℤ] ℤ) (w v : IntegralVector) : IntegralVector :=
  v - (F v / F w) • w

/-- The remainder vector has the exact expected functional value. -/
theorem remainderVector_value (F : IntegralVector →ₗ[ℤ] ℤ) (w v : IntegralVector) :
    F (remainderVector F w v) = F v % F w := by
  simp only [remainderVector,map_sub,map_smul,smul_eq_mul]
  have h := Int.emod_add_ediv_mul (F v) (F w)
  omega

/-- A representative already in the nonnegative lower interval is fixed by remainder reduction. -/
theorem remainderVector_eq_self (F : IntegralVector →ₗ[ℤ] ℤ) (w v : IntegralVector)
    (hv : 0 ≤ F v) (hw : F v < F w) : remainderVector F w v = v := by
  have hq : F v / F w = 0 := Int.ediv_eq_zero_of_lt hv hw
  simp [remainderVector,hq]

/-- A normalized primitive representative of lower height is fixed by the remainder operation. -/
theorem remainderVector_nonnegativeRepresentative (F : IntegralVector →ₗ[ℤ] ℤ)
    (w : IntegralVector) (L : RationalLine) (hL : (height F L : ℤ) < F w) :
    remainderVector F w (nonnegativeRepresentative F L) = nonnegativeRepresentative F L := by
  apply remainderVector_eq_self F w _ (nonnegativeRepresentative_nonneg F L)
  rwa [nonnegativeRepresentative_value]

end TernaryPoly.PrimitiveLineHeight
