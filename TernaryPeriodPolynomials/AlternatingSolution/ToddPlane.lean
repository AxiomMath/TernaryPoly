module

public import TernaryPeriodPolynomials.AlternatingSolution.PlaneFrames
public import TernaryPeriodPolynomials.AlternatingSolution.Todd
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Naturality
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Scaling
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Specialize the last variable to three times the middle one. -/
def normalPlane : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 0, X 1, 3*X 1]

/-- The same specialization on the univariate coefficient ring. -/
def normalPlaneCoeff : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ ![X 0, 3*X 0]

theorem finSuccEquiv_normalPlane (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (normalPlane f) =
      Polynomial.map normalPlaneCoeff.toRingHom (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [normalPlane, normalPlaneCoeff, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp]
    fin_cases i <;>
      simp [normalPlane, normalPlaneCoeff, map_ofNat, finSuccEquiv_X_zero,
        finSuccEquiv_ternary_X_one, finSuccEquiv_ternary_X_two]

theorem finSuccEquiv_shift_two_Y (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (alternatingShift (2*X 1) f) =
      Polynomial.taylor (-(2*X (0 : Fin 2))) (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [alternatingShift, finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.taylor_mul, hp]
    fin_cases i <;>
      simp [alternatingShift, map_ofNat, finSuccEquiv_X_zero, finSuccEquiv_ternary_X_one,
        finSuccEquiv_ternary_X_two, sub_eq_add_neg]

theorem finSuccEquiv_shift_one_Y (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (alternatingShift (X 1) f) =
      Polynomial.taylor (-X (0 : Fin 2)) (finSuccEquiv ℚ 2 f) :=
  finSuccEquiv_shift_Y f

/-- Plane specialization commutes with the finite Todd operator. -/
theorem finSuccEquiv_normalPlane_ternaryTodd (u : MvPolynomial (Fin 2) ℚ)
    (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (normalPlane (ternaryTodd u f)) =
      todd (normalPlaneCoeff u) (finSuccEquiv ℚ 2 (normalPlane f)) := by
  rw [finSuccEquiv_normalPlane, ternaryTodd, AlgEquiv.apply_symm_apply,
    map_todd, ← finSuccEquiv_normalPlane]

/-- The entire Todd expression vanishes on `Z=3Y` for every odd alternating polynomial. -/
theorem alternatingTodd_normalPlane {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) (hc : C f = f) (hs : S f = -f) :
    normalPlane (alternatingTodd f) = 0 := by
  apply (finSuccEquiv ℚ 2).injective
  simp only [alternatingTodd, map_sub, map_mul, map_zero]
  rw [show normalPlane (X (2 : Fin 3)) = 3*X 1 by simp [normalPlane],
    show normalPlane (X (1 : Fin 3)) = X 1 by simp [normalPlane]]
  rw [map_mul, map_ofNat, finSuccEquiv_ternary_X_one,
    finSuccEquiv_normalPlane_ternaryTodd, finSuccEquiv_normalPlane_ternaryTodd]
  have h1 := alternatingFrame1_plane hf hn
  have h2 := alternatingFrame2_plane hf hn hc hs
  change normalPlane (alternatingFrame1 f) = _ at h1
  change normalPlane (alternatingFrame2 f) = _ at h2
  rw [h1, h2]
  simp only [normalPlaneCoeff, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_neg, map_add]
  rw [finSuccEquiv_shift_one_Y, finSuccEquiv_shift_two_Y]
  have ht := todd_three_mul (X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ)
    (finSuccEquiv ℚ 2 (alternatingPlaneH f))
  simp only [map_add] at ht
  rw [ht]
  simp only [Polynomial.smul_eq_C_mul, map_ofNat]
  ring

end TernaryPoly
