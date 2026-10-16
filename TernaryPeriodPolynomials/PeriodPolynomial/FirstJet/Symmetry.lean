module

public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Basic
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodPrimitive
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import TernaryPeriodPolynomials.Polynomial.Parity

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

local notation "BP" => MvPolynomial (Fin 2) ℚ

private theorem bind2_comp (p a b c d : BP) :
    bind₁ ![a,b] (bind₁ ![c,d] p) =
      bind₁ ![bind₁ ![a,b] c, bind₁ ![a,b] d] p := by
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem binary_homogeneous_neg {p : BP} {n : ℕ} (hp : p.IsHomogeneous n) :
    bind₁ ![-X 0, -X 1] p = ((-1 : ℚ)^n) • p := by
  have h := homogeneous_bind_smul hp (-1 : ℚ)
  have hv : (fun i : Fin 2 => (-1 : ℚ) • (X i : BP)) = ![-X 0, -X 1] := by
    funext i
    fin_cases i <;> simp
  rwa [hv] at h

/-- The boundary substitution preserves the homogeneous degree. -/
theorem binaryBoundary_isHomogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (binaryBoundary f).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hf
  intro i
  fin_cases i
  · exact (isHomogeneous_X ℚ (1 : Fin 2)).neg
  · exact isHomogeneous_X ℚ (0 : Fin 2)
  · exact (isHomogeneous_X ℚ (1 : Fin 2)).sub (isHomogeneous_X ℚ (0 : Fin 2))

private theorem binaryBoundary_neg_swap {f : TernaryPolynomial} (hs : S f = -f) :
    bind₁ ![-X 1, -X 0] (binaryBoundary f) = -binaryBoundary f := by
  have he : bind₁ ![-X 1, -X 0] (binaryBoundary f) = binaryBoundary (S f) := by
    simp only [binaryBoundary, S, bind₁_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
    ring
  rw [he, hs]
  simp [binaryBoundary]

private theorem binaryBoundary_swap_parity {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hs : S f = -f) :
    ((-1 : ℚ)^n) • bind₁ ![X 1, X 0] (binaryBoundary f) = -binaryBoundary f := by
  have h := congrArg (bind₁ (![X 1, X 0] : Fin 2 → BP))
    (binary_homogeneous_neg (binaryBoundary_isHomogeneous hf))
  rw [bind2_comp, map_smul] at h
  simp only [map_neg, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [binaryBoundary_neg_swap hs] at h
  exact h.symm

/-- Odd alternating ternary polynomials have symmetric binary boundary. -/
theorem binaryBoundary_swap {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : S f = -f) :
    bind₁ ![X 1, X 0] (binaryBoundary f) = binaryBoundary f := by
  have h := binaryBoundary_swap_parity hf hs
  simpa only [hodd.neg_one_pow, neg_one_smul, neg_inj] using h

private theorem swap_partial_sum {f : TernaryPolynomial} (hs : S f = -f) :
    S (pderiv 0 f+pderiv 1 f) = -(pderiv 0 f+pderiv 1 f) := by
  have h0 : pderiv 0 (S f) = S (pderiv 1 f) := by
    apply pderiv_bind₁_coordinate _ 0 1 _ f
    intro k
    fin_cases k <;> simp
  have h1 : pderiv 1 (S f) = S (pderiv 0 f) := by
    apply pderiv_bind₁_coordinate _ 1 0 _ f
    intro k
    fin_cases k <;> simp
  rw [hs, map_neg] at h0 h1
  rw [map_add, ← h0, ← h1]
  abel

/-- The sum of the first boundary partials is alternating under swapping binary variables. -/
theorem binaryBoundary_partial_sum_swap {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : S f = -f) :
    bind₁ ![X 1, X 0] (binaryBoundary (pderiv 0 f+pderiv 1 f)) =
      -binaryBoundary (pderiv 0 f+pderiv 1 f) := by
  have he : Even (n-1) := Nat.Odd.sub_odd hodd (by decide : Odd (1 : ℕ))
  have h := binaryBoundary_swap_parity ((hf.pderiv (i := 0)).add (hf.pderiv (i := 1))) (swap_partial_sum hs)
  simpa only [he.neg_one_pow, one_smul] using h

/-- The normalized primitive differentiates to minus the first boundary partial sum. -/
theorem binaryFirstJetPrimitive_pderiv (f : TernaryPolynomial) :
    pderiv 0 (binaryFirstJetPrimitive f) = -binaryBoundary (pderiv 0 f+pderiv 1 f) := by
  simp [binaryFirstJetPrimitive]

/-- The normalized first-jet primitive has the original homogeneous degree. -/
theorem binaryFirstJetPrimitive_isHomogeneous {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) :
    (binaryFirstJetPrimitive f).IsHomogeneous n := by
  have hn : 1 ≤ n := hodd.pos
  have h := (isHomogeneous_binaryIntegral
    (binaryBoundary_isHomogeneous ((hf.pderiv (i := 0)).add (hf.pderiv (i := 1))))).neg
  simpa only [binaryFirstJetPrimitive, Nat.sub_add_cancel hn] using h

/-- Normalization makes the actual primitive vanish on its first axis. -/
theorem binaryFirstJetPrimitive_axis_first (f : TernaryPolynomial) :
    bind₁ (![0, X 1] : Fin 2 → BP) (binaryFirstJetPrimitive f) = 0 := by
  simp [binaryFirstJetPrimitive]

private theorem finSuccEquiv_binary_neg_first (p : BP) :
    finSuccEquiv ℚ 1 (bind₁ ![-X 0, X 1] p) =
      (finSuccEquiv ℚ 1 p).comp (-Polynomial.X) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, Polynomial.add_comp, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.mul_comp, hp]
    fin_cases i <;>
      simp [finSuccEquiv_X_zero, finSuccEquiv_binary_X_one]

/-- The actual primitive is even in its first variable. -/
theorem binaryFirstJetPrimitive_even_first_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    bind₁ ![-X 0, X 1] (binaryFirstJetPrimitive f) = binaryFirstJetPrimitive f := by
  have h := congrArg (Polynomial.map dropThirdCoeff.toRingHom)
    (alternatingFirstJetPrimitive_even_of_todd_derivative hf hodd hc hs hJ)
  simp only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
    ← binaryFirstJetPrimitive_transport] at h
  apply (finSuccEquiv ℚ 1).injective
  rw [finSuccEquiv_binary_neg_first]
  exact h

/-- The norm form of even parity in the first variable. -/
theorem binaryFirstJetPrimitive_even_first {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    bind₁ ![-X 0, X 1] (binaryFirstJetPrimitive f) = binaryFirstJetPrimitive f :=
  binaryFirstJetPrimitive_even_first_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

/-- Odd total degree and even first parity give oddness in the second variable. -/
theorem binaryFirstJetPrimitive_odd_second_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    bind₁ ![X 0, -X 1] (binaryFirstJetPrimitive f) = -binaryFirstJetPrimitive f := by
  have h := congrArg (bind₁ (![X 0, -X 1] : Fin 2 → BP))
    (binaryFirstJetPrimitive_even_first_of_todd_derivative hf hodd hc hs hJ)
  rw [bind2_comp] at h
  simp only [map_neg, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [binary_homogeneous_neg (binaryFirstJetPrimitive_isHomogeneous hf hodd),
    hodd.neg_one_pow, neg_one_smul] at h
  exact h.symm

/-- The norm form of odd parity in the second variable. -/
theorem binaryFirstJetPrimitive_odd_second {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    bind₁ ![X 0, -X 1] (binaryFirstJetPrimitive f) = -binaryFirstJetPrimitive f :=
  binaryFirstJetPrimitive_odd_second_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

private theorem pderiv_binary_neg_first (p : BP) :
    pderiv 0 (bind₁ (![-X 0, X 1] : Fin 2 → BP) p) =
      -bind₁ ![-X 0, X 1] (pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq, neg_add]
  | mul_X p i hp =>
    fin_cases i <;> simp [map_mul, map_add, hp]

/-- The derivative of the actual primitive is invariant under quarter rotation. -/
theorem binaryFirstJetPrimitive_rotation_pderiv_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) :
    binaryRotation (pderiv 0 (binaryFirstJetPrimitive f)) =
      pderiv 0 (binaryFirstJetPrimitive f) := by
  have hx := congrArg (pderiv (0 : Fin 2))
    (binaryFirstJetPrimitive_even_first_of_todd_derivative hf hodd hc hs hJ)
  rw [pderiv_binary_neg_first] at hx
  have hswap : bind₁ ![X 1, X 0] (pderiv 0 (binaryFirstJetPrimitive f)) =
      -pderiv 0 (binaryFirstJetPrimitive f) := by
    rw [binaryFirstJetPrimitive_pderiv, map_neg,
      binaryBoundary_partial_sum_swap hf hodd hs]
  have h := congrArg (bind₁ (![-X 0, X 1] : Fin 2 → BP)) hswap
  rw [bind2_comp, map_neg] at h
  simp only [bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h.trans hx

/-- The norm form of rotation invariance of the first partial. -/
theorem binaryFirstJetPrimitive_rotation_pderiv {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    binaryRotation (pderiv 0 (binaryFirstJetPrimitive f)) =
      pderiv 0 (binaryFirstJetPrimitive f) :=
  binaryFirstJetPrimitive_rotation_pderiv_of_todd_derivative hf hodd hc hs
    (pderiv_zero_alternatingTodd hc hs hn)

end TernaryPoly
