module

public import TernaryPeriodPolynomials.Polynomial.Translation
public import TernaryPeriodPolynomials.Polynomial.TaylorHasse

@[expose] public section

open Polynomial
noncomputable section
namespace TernaryPoly.PolynomialTripleDifference

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

def difference (a : R) (p : Polynomial R) : Polynomial R := taylor a p-p

omit [IsDomain R] [CharZero R] in
theorem derivative_difference (a : R) (p : Polynomial R) :
    derivative (difference a p)=difference a (derivative p) := by
  simp only [difference,map_sub,derivative_taylor]

/-- A zero nonzero-step difference forces the derivative to vanish. -/
theorem derivative_eq_zero_of_difference {p : Polynomial R} {a : R}
    (ha : a≠0) (h : difference a p=0) : derivative p=0 := by
  have he : p.comp (X+C a)=p := by
    simpa only [difference,taylor_apply] using sub_eq_zero.mp h
  rw [polynomial_eq_constant_of_translation p a ha he,derivative_C]

/-- Three nonzero-step differences force the third derivative to vanish. -/
theorem third_derivative_eq_zero {p : Polynomial R} {a b c : R}
    (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (h : difference a (difference b (difference c p))=0) :
    derivative (derivative (derivative p))=0 := by
  have h1 := derivative_eq_zero_of_difference ha h
  simp only [derivative_difference] at h1
  have h2 := derivative_eq_zero_of_difference hb h1
  simp only [derivative_difference] at h2
  exact derivative_eq_zero_of_difference hc h2

/-- An odd polynomial with third derivative zero is killed by one nonzero root. -/
theorem eq_zero_of_third_derivative_odd_eval (p : Polynomial R) {a : R}
    (ha : a≠0) (hd : derivative (derivative (derivative p))=0)
    (ho : p.comp (-X)= -p) (hv : p.eval a=0) : p=0 := by
  have ho2 : (derivative (derivative p)).comp (-X)= -derivative (derivative p) := by
    have he := congrArg (fun q => derivative (derivative q)) ho
    simpa [derivative_comp] using he
  have hd2 : derivative (derivative p)=0 := by
    have he := eq_C_of_derivative_eq_zero hd
    rw [he,C_comp] at ho2
    rw [he]
    exact CharZero.eq_neg_self_iff.mp ho2
  have hdp := eq_C_of_derivative_eq_zero hd2
  have hz : p.eval 0=0 := by
    have he := congrArg (eval 0) ho
    simp only [eval_comp,eval_neg,eval_X,neg_zero] at he
    exact CharZero.eq_neg_self_iff.mp he
  let k := (derivative p).coeff 0
  have he : p=C k*X := by
    have hder : derivative (p-C k*X)=0 := by
      rw [map_sub,derivative_mul,derivative_C,derivative_X,zero_mul,zero_add,mul_one,hdp]
      simp [k]
    have hh := eq_C_of_derivative_eq_zero hder
    have hc : (p-C k*X).coeff 0=0 := by
      rw [coeff_zero_eq_eval_zero]
      simp [hz]
    rw [hc,map_zero] at hh
    exact sub_eq_zero.mp hh
  rw [he,eval_mul,eval_C,eval_X] at hv
  have hk : k=0 := (mul_eq_zero.mp hv).resolve_right ha
  rw [he,hk,map_zero,zero_mul]

end TernaryPoly.PolynomialTripleDifference
