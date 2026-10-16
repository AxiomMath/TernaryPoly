module

public import TernaryPeriodPolynomials.PeriodPolynomial.FirstJet.Symmetry
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodEquation
public import TernaryPeriodPolynomials.PeriodPolynomial.Lift.JetRecovery

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly
namespace SymmetricPeriodExtraction

local notation "BP" => MvPolynomial (Fin 2) ℚ

 theorem bind_comp (p a b c d : BP) :
    bind₁ ![a,b] (bind₁ ![c,d] p) =
      bind₁ ![bind₁ ![a,b] c, bind₁ ![a,b] d] p := by
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

 theorem homogeneous_neg {p : BP} {n : ℕ} (hp : p.IsHomogeneous n) :
    bind₁ ![-X 0,-X 1] p = ((-1 : ℚ)^n) • p := by
  have h := homogeneous_bind_smul hp (-1 : ℚ)
  have hv : (fun i : Fin 2 => (-1 : ℚ) • (X i : BP)) = ![-X 0,-X 1] := by
    funext i
    fin_cases i <;> simp
  rwa [hv] at h

 theorem boundary_neg_swap {f : TernaryPolynomial} (hs : S f = f) :
    bind₁ ![-X 1,-X 0] (binaryBoundary f) = binaryBoundary f := by
  have he : bind₁ ![-X 1,-X 0] (binaryBoundary f) = binaryBoundary (S f) := by
    simp only [binaryBoundary, S, bind₁_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
    ring
  rw [he, hs]

 theorem boundary_swap_parity {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hs : S f = f) :
    ((-1 : ℚ)^n) • bind₁ ![X 1,X 0] (binaryBoundary f) = binaryBoundary f := by
  have h := congrArg (bind₁ (![X 1,X 0] : Fin 2 → BP))
    (homogeneous_neg (binaryBoundary_isHomogeneous hf))
  rw [bind_comp, map_smul] at h
  simp only [map_neg, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [boundary_neg_swap hs] at h
  exact h.symm

 theorem boundary_swap {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : S f = f) :
    bind₁ ![X 1,X 0] (binaryBoundary f) = -binaryBoundary f := by
  have h := boundary_swap_parity hf hs
  simpa only [hodd.neg_one_pow, neg_one_smul, neg_eq_iff_eq_neg] using h

 theorem partial_sum_swap {f : TernaryPolynomial} (hs : S f = f) :
    S (pderiv 0 f+pderiv 1 f) = pderiv 0 f+pderiv 1 f := by
  have h0 : pderiv 0 (S f) = S (pderiv 1 f) := by
    apply pderiv_bind₁_coordinate _ 0 1 _ f
    intro k
    fin_cases k <;> simp
  have h1 : pderiv 1 (S f) = S (pderiv 0 f) := by
    apply pderiv_bind₁_coordinate _ 1 0 _ f
    intro k
    fin_cases k <;> simp
  rw [hs] at h0 h1
  rw [map_add, ← h0, ← h1]
  abel

 theorem boundary_partial_sum_swap {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : S f = f) :
    bind₁ ![X 1,X 0] (binaryBoundary (pderiv 0 f+pderiv 1 f)) =
      binaryBoundary (pderiv 0 f+pderiv 1 f) := by
  have he : Even (n-1) := Nat.Odd.sub_odd hodd (by decide : Odd (1 : ℕ))
  have h := boundary_swap_parity ((hf.pderiv (i := 0)).add (hf.pderiv (i := 1)))
    (partial_sum_swap hs)
  simpa only [he.neg_one_pow, one_smul] using h

private theorem boundary_deriv (f : TernaryPolynomial) :
    pderiv 0 (binaryBoundary f) = binaryBoundary (pderiv 1 f-pderiv 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [binaryBoundary]
  | add f g hf hg =>
    simp only [binaryBoundary, map_sub] at hf hg
    simp only [binaryBoundary, map_add, map_sub, hf, hg]
    ring
  | mul_X f i hf =>
    simp only [binaryBoundary, map_sub] at hf
    fin_cases i <;> simp [binaryBoundary, map_mul, map_add, hf] <;> ring

private def swapLast : TernaryPolynomial →ₐ[ℚ] TernaryPolynomial :=
  bind₁ ![X 0,X 2,X 1]

private theorem swapLast_fixed {f : TernaryPolynomial} (hc : C f=f) (hs : S f=f) :
    swapLast f=f := by
  have he : swapLast f=S (C f) := by
    simp only [swapLast, S, C, bind₁_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
  rw [he,hc,hs]

private theorem swapLast_partials {f : TernaryPolynomial} (hc : C f=f) (hs : S f=f) :
    swapLast (pderiv 0 f+pderiv 1 f)=pderiv 0 f+pderiv 2 f := by
  have h0 : pderiv 0 (swapLast f)=swapLast (pderiv 0 f) := by
    apply pderiv_bind₁_coordinate _ 0 0 _ f
    intro k
    fin_cases k <;> simp
  have h2 : pderiv 2 (swapLast f)=swapLast (pderiv 1 f) := by
    apply pderiv_bind₁_coordinate _ 2 1 _ f
    intro k
    fin_cases k <;> simp
  rw [swapLast_fixed hc hs] at h0 h2
  rw [map_add, ← h0, ← h2]

 theorem boundary_deriv_reflection {f : TernaryPolynomial} (hc : C f=f) (hs : S f=f) :
    pderiv 0 (binaryBoundary f) = binaryBoundary (pderiv 0 f+pderiv 1 f) -
      bind₁ ![X 1-X 0,X 1] (binaryBoundary (pderiv 0 f+pderiv 1 f)) := by
  have he (g : TernaryPolynomial) :
      bind₁ ![X 1-X 0,X 1] (binaryBoundary g)=binaryBoundary (swapLast g) := by
    simp only [binaryBoundary, swapLast, bind₁_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
  rw [boundary_deriv, he, swapLast_partials hc hs]
  simp only [binaryBoundary, map_add, map_sub]
  ring

 theorem boundary_partial_sum_even_first {f : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f) -
      binaryFirstJetPrimitive f = binaryBoundary f) :
    bind₁ ![-X 0,X 1] (binaryBoundary (pderiv 0 f+pderiv 1 f)) =
      binaryBoundary (pderiv 0 f+pderiv 1 f) := by
  let H : BP := binaryBoundary (pderiv 0 f+pderiv 1 f)
  have hd := congrArg (pderiv (0 : Fin 2)) hdiff
  rw [map_sub, binary_pderiv_substitution] at hd
  simp only [map_sub, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    sub_zero, mul_one, mul_zero, add_zero, binaryFirstJetPrimitive_pderiv, map_neg] at hd
  rw [boundary_deriv_reflection hc hs] at hd
  have he : (bind₁ ![X 1-X 0,X 1] H : BP)=bind₁ ![X 0-X 1,X 1] H := by
    change -bind₁ ![X 0-X 1,X 1] H - -H=H-bind₁ ![X 1-X 0,X 1] H at hd
    linear_combination (norm := abel) hd
  have ht := congrArg (bind₁ (![X 0+X 1,X 1] : Fin 2 → BP)) he
  rw [bind_comp, bind_comp] at ht
  have hv : (![X 0,X 1] : Fin 2 → BP)=X := by
    funext i
    fin_cases i <;> rfl
  simpa [hv,H] using ht

 theorem primitive_odd_first {f : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f) -
      binaryFirstJetPrimitive f = binaryBoundary f) :
    bind₁ ![-X 0,X 1] (binaryFirstJetPrimitive f) = -binaryFirstJetPrimitive f := by
  let p := binaryFirstJetPrimitive f
  have haxis : bind₁ (![0,X 1] : Fin 2 → BP) (bind₁ ![-X 0,X 1] p) = 0 := by
    rw [bind_comp]
    simpa [p] using binaryFirstJetPrimitive_axis_first f
  have hd : pderiv 0 (bind₁ ![-X 0,X 1] p) = -pderiv 0 p := by
    rw [binary_pderiv_substitution]
    simp [p, binaryFirstJetPrimitive_pderiv, boundary_partial_sum_even_first hc hs hdiff]
  rw [← binaryIntegral_pderiv_of_axis _ haxis, hd, map_neg,
    binaryIntegral_pderiv_of_axis _ (binaryFirstJetPrimitive_axis_first f)]

 theorem primitive_even_second {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f) -
      binaryFirstJetPrimitive f = binaryBoundary f) :
    bind₁ ![X 0,-X 1] (binaryFirstJetPrimitive f) = binaryFirstJetPrimitive f := by
  have h := congrArg (bind₁ (![X 0,-X 1] : Fin 2 → BP)) (primitive_odd_first hc hs hdiff)
  rw [bind_comp, map_neg] at h
  simp only [map_neg, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [homogeneous_neg (binaryFirstJetPrimitive_isHomogeneous hf hodd),
    hodd.neg_one_pow, neg_one_smul, neg_inj] at h
  exact h.symm

 theorem primitive_rotation_deriv {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f=f) (hs : S f=f)
    (hdiff : bind₁ ![X 0-X 1,X 1] (binaryFirstJetPrimitive f) -
      binaryFirstJetPrimitive f = binaryBoundary f) :
    binaryRotation (pderiv 0 (binaryFirstJetPrimitive f)) =
      pderiv 0 (binaryFirstJetPrimitive f) := by
  have h := congrArg (bind₁ (![-X 0,X 1] : Fin 2 → BP))
    (boundary_partial_sum_swap hf hodd hs)
  rw [bind_comp, boundary_partial_sum_even_first hc hs hdiff] at h
  simp only [bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simpa only [binaryRotation, binaryFirstJetPrimitive_pderiv, map_neg] using congrArg Neg.neg h

end SymmetricPeriodExtraction
end TernaryPoly
