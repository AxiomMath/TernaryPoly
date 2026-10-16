module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.SupportRational
public import TernaryPeriodPolynomials.Polynomial.Divisibility
public import Mathlib.Algebra.Divisibility.Units

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SinglePoleCoordinate
open SinglePole PrimitiveLineHeight ModThreeGoodAction OrdinaryResidueSupport
attribute [local instance] Classical.propDecidable

abbrev Binary := MvPolynomial (Fin 2) ℚ
abbrev BinaryV (n : ℕ) := homogeneousSubmodule (Fin 2) ℚ n

/-- Ordered complementary variables: (b,c), (a,c), and (a,b). -/
def plane : Fin 3 → Fin 2 → Fin 3 := ![![1,2],![0,2],![0,1]]

/-- Literal substitution setting the selected coordinate equal to zero. -/
def restrictionVariables : Fin 3 → Fin 3 → Binary :=
  ![![0,X 0,X 1],![X 0,0,X 1],![X 0,X 1,0]]

def restrict (i : Fin 3) : Poly →ₐ[ℚ] Binary := bind₁ (restrictionVariables i)
def lift (i : Fin 3) : Binary →ₐ[ℚ] Poly := rename (plane i)

@[simp] theorem restrict_X_self (i : Fin 3) : restrict i (X i) = 0 := by
  simp only [restrict,bind₁_X_right]
  fin_cases i <;> rfl

@[simp] theorem restrict_lift (i : Fin 3) (q : Binary) : restrict i (lift i q) = q := by
  have h : (restrict i).comp (lift i) = AlgHom.id ℚ Binary := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,lift,rename_X,restrict,bind₁_X_right,AlgHom.id_apply]
    fin_cases i <;> fin_cases j <;> rfl
  exact AlgHom.congr_fun h q

/-- Lifting the literal restriction is the actual same-variable zero substitution. -/
theorem lift_restrict (i : Fin 3) (p : Poly) :
    lift i (restrict i p) = bind₁ (Function.update X i 0) p := by
  have h : (lift i).comp (restrict i) = bind₁ (Function.update X i 0) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply,restrict,bind₁_X_right]
    fin_cases i <;> fin_cases j <;>
      simp [lift,restrictionVariables,plane,Function.update]
  exact AlgHom.congr_fun h p

/-- The kernel of actual coordinate restriction is precisely divisibility by that variable. -/
theorem restrict_zero_iff (i : Fin 3) (p : Poly) : restrict i p = 0 ↔ X i ∣ p := by
  constructor
  · intro h
    have he : bind₁ (Function.update X i 0) p = 0 := by
      rw [← lift_restrict,h,map_zero]
    simpa only [sub_zero] using linear_factor_dvd_of_substitution_zero p i 0 he
  · rintro ⟨q,rfl⟩
    rw [map_mul,restrict_X_self,zero_mul]

theorem restrict_homogeneous (i : Fin 3) {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    (restrict i p).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hp
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [restrictionVariables,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    first | exact MvPolynomial.isHomogeneous_zero (σ := Fin 2) (R := ℚ) 1
          | exact isHomogeneous_X ℚ _

def homogeneousRestrict (n : ℕ) (i : Fin 3) : V n →ₗ[ℚ] BinaryV n where
  toFun p := ⟨restrict i p.val,restrict_homogeneous i p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext ((restrict i).toLinearMap.map_smul _ _)

def homogeneousLift (n : ℕ) (i : Fin 3) : BinaryV n →ₗ[ℚ] V n where
  toFun p := ⟨lift i p.val,p.property.rename_isHomogeneous⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext ((lift i).toLinearMap.map_smul _ _)

@[simp] theorem homogeneousRestrict_lift (n : ℕ) (i : Fin 3) (p : BinaryV n) :
    homogeneousRestrict n i (homogeneousLift n i p) = p :=
  Subtype.ext (restrict_lift i p.val)

/-- The scalar in the chosen primitive normal at a coordinate axis is retained explicitly. -/
def axisScale (i : Fin 3) : ℚ := rationalVector (primitiveGenerator (axis i)) i

theorem axis_generator_sign (i : Fin 3) :
    primitiveGenerator (axis i) = Pi.single i 1 ∨
      primitiveGenerator (axis i) = -Pi.single i 1 := by
  apply (normalOfRow_eq_iff (primitiveGenerator_primitive (axis i)) (axis_primitive i)).mp
  exact normalOfRow_generator (axis i)

theorem axisScale_eq_one_or_neg_one (i : Fin 3) : axisScale i = 1 ∨ axisScale i = -1 := by
  rcases axis_generator_sign i with h | h
  · left; simp [axisScale,h,rationalVector]
  · right; simp [axisScale,h,rationalVector]

theorem axisScale_ne_zero (i : Fin 3) : axisScale i ≠ 0 := by
  rcases axisScale_eq_one_or_neg_one i with h | h <;> simp [h]

/-- The chosen primitive denominator is a nonzero scalar times the literal coordinate variable. -/
theorem denominator_axis (i : Fin 3) : denominator (axis i) = MvPolynomial.C (axisScale i) * X i := by
  rcases axis_generator_sign i with h | h <;>
    simp [denominator,axisScale,h,form,rationalVector,Pi.single_apply]

theorem denominator_axis_dvd_iff (i : Fin 3) (p : Poly) : denominator (axis i) ∣ p ↔ X i ∣ p := by
  rw [denominator_axis]
  exact ((isUnit_iff_ne_zero.mpr (axisScale_ne_zero i)).map (MvPolynomial.C : ℚ →+* Poly)).mul_left_dvd

/-- The three coordinate-normal indices really are distinct. -/
theorem axis_injective : Function.Injective axis := by
  intro i j h
  by_contra hij
  rcases (normalOfRow_eq_iff (axis_primitive i) (axis_primitive j)).mp h with hrow | hrow
  · have he := congrFun hrow i
    simp [Pi.single_eq_of_ne hij] at he
  · have he := congrFun hrow i
    simp [Pi.single_eq_of_ne hij] at he

end TernaryPoly.SinglePoleCoordinate
