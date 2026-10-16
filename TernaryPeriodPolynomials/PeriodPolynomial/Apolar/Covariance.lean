module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.Span

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryHomogeneous
variable (K : Type*) [Field K]

/-- Actual substitution by an arbitrary two-by-two matrix, including singular matrices. -/
def transform (d : ℕ) (a b c e : K) : H K d →ₗ[K] H K d where
  toFun p := ⟨bind₁ ![C a*X 0+C b*X 1,C c*X 0+C e*X 1] p.val,by
    have hg (i : Fin 2) :
        ((![C a*X 0+C b*X 1,C c*X 0+C e*X 1] : Fin 2 → MvPolynomial (Fin 2) K) i).IsHomogeneous 1 := by
      fin_cases i
      · exact (isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)
      · exact (isHomogeneous_C_mul_X c 0).add (isHomogeneous_C_mul_X e 1)
    change (bind₁ _ p.val).IsHomogeneous d
    simpa only [one_mul,aeval_eq_bind₁] using p.property.aeval _ hg⟩
  map_add' p q := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r p := by apply Subtype.ext; exact map_smul _ _ _

/-- Matrix substitution on a pure power is the literal row-vector multiplication. -/
theorem transform_pure (d : ℕ) (a b c e u v : K) :
    transform K d a b c e (pure K d u v)=pure K d (u*a+v*c) (u*b+v*e) := by
  apply Subtype.ext
  change bind₁ _ ((C u*X 0+C v*X 1)^d)=_
  simp only [map_pow,map_add,map_mul,bind₁_C_right,bind₁_X_right,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,pure]
  congr 1
  ring

/-- The determinant covariance law for the actual apolar form in every degree. -/
theorem covariance [CharZero K] (d : ℕ) (a b c e : K) (p q : H K d) :
    form K d (transform K d a b c e p) (transform K d a b c e q)=
      (a*e-b*c)^d * form K d p q := by
  have hp : p ∈ Submodule.span K (Set.range (fun v : K×K => pure K d v.1 v.2)) := by
    rw [span_pure]; trivial
  have hq : q ∈ Submodule.span K (Set.range (fun v : K×K => pure K d v.1 v.2)) := by
    rw [span_pure]; trivial
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨⟨u,v⟩,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨⟨w,t⟩,rfl⟩ := hq
      rw [transform_pure,transform_pure,form_pure_pure,form_pure_pure,←mul_pow]
      congr 1
      ring
    | zero => simp only [map_zero,mul_zero]
    | add q r _ _ hq hr => simp only [map_add,hq,hr,mul_add]
    | smul r q _ hq => simp only [map_smul,smul_eq_mul,hq]; ring
  | zero => simp only [map_zero,LinearMap.zero_apply,mul_zero]
  | add p r _ _ hp hr => simp only [map_add,LinearMap.add_apply,hp,hr,mul_add]
  | smul r p _ hp => simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hp]; ring

end TernaryPoly.BinaryApolar
