module

public import TernaryPeriodPolynomials.Building.Good.IntegralNormalization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Tactic.Ring

@[expose] public section


noncomputable section
namespace TernaryPoly.PrimitiveBasisExtension

open ModThreeGoodAction GoodIntegralNormalization Matrix

abbrev IntegralMatrix := Matrix (Fin 3) (Fin 3) ℤ

/-- A concrete completion assembled from two binary Bézout identities. -/
def bezoutCompletion (x d t s a b c e : ℤ) : IntegralMatrix :=
  !![x, -b, 0; d*t, a*t, -e; d*s, a*s, c]

theorem bezoutCompletion_det (x d t s a b c e : ℤ)
    (h₁ : x*a+d*b = 1) (h₂ : t*c+s*e = 1) :
    (bezoutCompletion x d t s a b c e).det = 1 := by
  calc
    _ = (x*a+d*b)*(t*c+s*e) := by
      simp [bezoutCompletion,Matrix.det_fin_three]
      ring
    _ = 1 := by rw [h₁,h₂,mul_one]

/-- Every primitive integer vector is the first column of a determinant-one integer matrix. -/
theorem exists_matrix_first_column_det_one (v : IntegralVector) (hv : Primitive v) :
    ∃ M : IntegralMatrix, M.col 0 = v ∧ M.det = 1 := by
  change content v = 1 at hv
  by_cases hd : Int.gcd (v 1) (v 2) = 0
  · have hy : v 1 = 0 := Int.eq_zero_of_gcd_eq_zero_left hd
    have hz : v 2 = 0 := Int.eq_zero_of_gcd_eq_zero_right hd
    have hu : IsUnit (v 0) := by
      apply Int.isUnit_iff_natAbs_eq.mpr
      simpa [content,hy,hz] using hv
    let M : IntegralMatrix := !![v 0,0,0;0,v 0,0;0,0,1]
    refine ⟨M,?_,?_⟩
    · funext i
      fin_cases i <;> simp [M,Matrix.col,hy,hz]
    · simpa [M,Matrix.det_fin_three] using Int.isUnit_mul_self hu
  · obtain ⟨t,s,hcop,hy,hz⟩ := Int.exists_gcd_one (Nat.pos_of_ne_zero hd)
    let d : ℤ := Int.gcd (v 1) (v 2)
    have hg : Int.gcd (v 0) d = 1 := by
      simpa [d,Int.gcd_def,content] using hv
    let a := Int.gcdA (v 0) d
    let b := Int.gcdB (v 0) d
    let c := Int.gcdA t s
    let e := Int.gcdB t s
    have h₁ : v 0*a+d*b = 1 := by
      change v 0 * Int.gcdA (v 0) d + d * Int.gcdB (v 0) d = 1
      rw [← Int.gcd_eq_gcd_ab,hg]
      rfl
    have h₂ : t*c+s*e = 1 := by
      change t * Int.gcdA t s + s * Int.gcdB t s = 1
      rw [← Int.gcd_eq_gcd_ab,hcop]
      rfl
    refine ⟨bezoutCompletion (v 0) d t s a b c e,?_,bezoutCompletion_det _ _ _ _ _ _ _ _ h₁ h₂⟩
    funext i
    fin_cases i
    · rfl
    · change d * t = v 1
      simpa only [d,mul_comm] using hy.symm
    · change d * s = v 2
      simpa only [d,mul_comm] using hz.symm

/-- The completion is an actual unit in the integer matrix ring, with the specified first column. -/
theorem exists_integralGL_first_column (v : IntegralVector) (hv : Primitive v) :
    ∃ g : IntegralGL, g.val.col 0 = v ∧ g.val.det = 1 := by
  obtain ⟨M,hcol,hdet⟩ := exists_matrix_first_column_det_one v hv
  refine ⟨Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one),hcol,hdet⟩

/-- A chosen genuine integer general linear matrix extending the primitive vector. -/
def primitiveCompletion (v : IntegralVector) (hv : Primitive v) : IntegralGL :=
  (exists_integralGL_first_column v hv).choose

@[simp] theorem primitiveCompletion_first_column (v : IntegralVector) (hv : Primitive v) :
    (primitiveCompletion v hv).val.col 0 = v :=
  (exists_integralGL_first_column v hv).choose_spec.1

@[simp] theorem primitiveCompletion_det (v : IntegralVector) (hv : Primitive v) :
    (primitiveCompletion v hv).val.det = 1 :=
  (exists_integralGL_first_column v hv).choose_spec.2

end TernaryPoly.PrimitiveBasisExtension
