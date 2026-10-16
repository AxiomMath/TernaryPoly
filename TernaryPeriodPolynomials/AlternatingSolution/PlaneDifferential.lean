module

public import TernaryPeriodPolynomials.AlternatingSolution.FirstDerivativeFrames
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Transport
public import TernaryPeriodPolynomials.Polynomial.Integral

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

/-- The ordinary boundary derivative is the difference of the second and third partials. -/
theorem pderiv_alternatingPlaneH (f : TernaryPolynomial) :
    pderiv 0 (alternatingPlaneH f) =
      alternatingPlaneH (pderiv 1 f) - alternatingPlaneH (pderiv 2 f) := by
  change pderiv 0 (bind₁ ![-X 1, X 0, X 1-X 0] f) =
    bind₁ ![-X 1, X 0, X 1-X 0] (pderiv 1 f) -
      bind₁ ![-X 1, X 0, X 1-X 0] (pderiv 2 f)
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    abel
  | mul_X p i hp =>
    fin_cases i <;> simp [map_mul, map_add, map_sub, hp] <;> ring

private theorem substitute3_identity (f : TernaryPolynomial) :
    substitute3 f (X 0) (X 1) (X 2) = f := by
  have ht : (![X 0, X 1, X 2] : Fin 3 → TernaryPolynomial) = X := by
    funext i
    fin_cases i <;> rfl
  simp [substitute3, ht]

private theorem pderiv_swap_last (i j : Fin 3)
    (hij : ∀ k : Fin 3, pderiv i ((![X 0, X 2, X 1] : Fin 3 → TernaryPolynomial) k) =
      if k = j then 1 else 0)
    {f : TernaryPolynomial} (hc : C f = f) (hs : S f = -f)
    (a b c : TernaryPolynomial) :
    substitute3 (pderiv j f) a c b = -substitute3 (pderiv i f) a b c := by
  have hr := substitute3_swap_last hc hs (X 0) (X 1) (X 2)
  rw [substitute3_identity] at hr
  have hd := congrArg (pderiv i) hr
  rw [show pderiv i (substitute3 f (X 0) (X 2) (X 1)) =
      substitute3 (pderiv j f) (X 0) (X 2) (X 1) from
    pderiv_bind₁_coordinate _ i j hij f, map_neg] at hd
  have h := congrArg (fun g => substitute3 g a b c) hd
  rw [substitute3_substitute3] at h
  simpa [substitute3] using h

private theorem planeH_reflect_expand (f : TernaryPolynomial) :
    bind₁ ![X 1-X 0, X 1, X 2] (alternatingPlaneH f) =
      substitute3 f (-X 1) (X 1-X 0) (X 0) := by
  change substitute3 (substitute3 f (-X 1) (X 0) (X 1-X 0))
    (X 1-X 0) (X 1) (X 2) = _
  rw [substitute3_substitute3]
  simp [substitute3]

/-- Reflection about the boundary midpoint corresponds to univariate composition. -/
theorem finSuccEquiv_reflect_Y (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (bind₁ ![X 1-X 0, X 1, X 2] f) =
      (finSuccEquiv ℚ 2 f).comp (Polynomial.C (X (0 : Fin 2)) - Polynomial.X) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.mul_comp, hp]
    fin_cases i <;>
      simp [finSuccEquiv_X_zero, finSuccEquiv_ternary_X_one, finSuccEquiv_ternary_X_two]

private theorem planeH_reflect {f : TernaryPolynomial} (hc : C f = f) (hs : S f = -f) :
    bind₁ ![X 1-X 0, X 1, X 2] (alternatingPlaneH f) = -alternatingPlaneH f := by
  rw [planeH_reflect_expand]
  exact substitute3_swap_last hc hs (-X 1) (X 0) (X 1-X 0)

private theorem planeH_first_partial_reflect {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) :
    bind₁ ![X 1-X 0, X 1, X 2] (alternatingPlaneH (pderiv 0 f)) =
      -alternatingPlaneH (pderiv 0 f) := by
  rw [planeH_reflect_expand]
  apply pderiv_swap_last 0 0 _ hc hs (-X 1) (X 0) (X 1-X 0)
  intro k
  fin_cases k <;> simp

private theorem planeH_second_partial_reflect {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) :
    bind₁ ![X 1-X 0, X 1, X 2] (alternatingPlaneH (pderiv 1 f)) =
      -alternatingPlaneH (pderiv 2 f) := by
  rw [planeH_reflect_expand]
  apply pderiv_swap_last 2 1 _ hc hs (-X 1) (X 0) (X 1-X 0)
  intro k
  fin_cases k <;> simp

private theorem planeH_add (f g : TernaryPolynomial) :
    alternatingPlaneH (f+g) = alternatingPlaneH f + alternatingPlaneH g := by
  simp [alternatingPlaneH, substitute3]

/-- The transported boundary derivative is the second boundary partial minus the third. -/
theorem alternatingPlaneH_derivative (f : TernaryPolynomial) :
    Polynomial.derivative (finSuccEquiv ℚ 2 (alternatingPlaneH f)) =
      finSuccEquiv ℚ 2 (alternatingPlaneH (pderiv 1 f)) -
        finSuccEquiv ℚ 2 (alternatingPlaneD1 f) := by
  rw [← finSuccEquiv_pderiv_zero, pderiv_alternatingPlaneH, map_sub]
  rfl

/-- Alternating symmetry supplies the reflection equation for the boundary derivative. -/
theorem alternatingPlaneH_derivative_reflection {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) :
    Polynomial.derivative (finSuccEquiv ℚ 2 (alternatingPlaneH f)) =
      finSuccEquiv ℚ 2 (alternatingPlaneH (pderiv 0 f+pderiv 1 f)) +
        (finSuccEquiv ℚ 2 (alternatingPlaneH (pderiv 0 f+pderiv 1 f))).comp
          (Polynomial.C (X (0 : Fin 2)) - Polynomial.X) := by
  have href : bind₁ ![X 1-X 0, X 1, X 2]
      (alternatingPlaneH (pderiv 0 f+pderiv 1 f)) =
      -alternatingPlaneH (pderiv 0 f) - alternatingPlaneH (pderiv 2 f) := by
    rw [planeH_add, map_add, planeH_first_partial_reflect hc hs,
      planeH_second_partial_reflect hc hs]
    abel
  rw [alternatingPlaneH_derivative, ← finSuccEquiv_reflect_Y, href]
  simp only [planeH_add, map_add, map_sub, map_neg, alternatingPlaneD1]
  abel

/-- The boundary values at zero and at the coefficient variable are opposite. -/
theorem alternatingPlaneH_eval_endpoints {f : TernaryPolynomial}
    (hc : C f = f) (hs : S f = -f) :
    (finSuccEquiv ℚ 2 (alternatingPlaneH f)).eval (X (0 : Fin 2)) =
      -(finSuccEquiv ℚ 2 (alternatingPlaneH f)).eval 0 := by
  have hr := congrArg (finSuccEquiv ℚ 2) (planeH_reflect hc hs)
  rw [finSuccEquiv_reflect_Y, map_neg] at hr
  have he := congrArg (Polynomial.eval 0) hr
  simpa [Polynomial.eval_comp] using he

/-- The canonical negative integral has the differential equation required by the first jet. -/
theorem alternatingPlane_integral_derivative (f : TernaryPolynomial) :
    Polynomial.derivative
        (-polyIntegral (finSuccEquiv ℚ 2 (alternatingPlaneH (pderiv 0 f+pderiv 1 f)))) +
      Polynomial.derivative (finSuccEquiv ℚ 2 (alternatingPlaneH f)) =
      -(finSuccEquiv ℚ 2 (alternatingPlaneA1 f) +
        finSuccEquiv ℚ 2 (alternatingPlaneD1 f)) := by
  rw [map_neg, derivative_polyIntegral, alternatingPlaneH_derivative]
  simp only [planeH_add, map_add, alternatingPlaneA1, alternatingPlaneD1]
  abel

end TernaryPoly
