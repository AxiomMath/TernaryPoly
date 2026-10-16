module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Multiplicity
public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymmetricCoordinates
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm
open CharTwoProjector (sub Symmetric)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem sub_comp (f a b c x y z : Poly) :
    sub (sub f a b c) x y z = sub f (sub a x y z) (sub b x y z) (sub c x y z) := by
  simp only [sub, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem sub_add (f g a b c : Poly) :
    sub (f+g) a b c = sub f a b c + sub g a b c := map_add (bind₁ ![a,b,c]) f g

private theorem sub_zero_poly (a b c : Poly) : sub 0 a b c = 0 := map_zero (bind₁ ![a,b,c])

private theorem sub_X_zero (a b c : Poly) : sub (X 0) a b c = a := by simp [sub]
private theorem sub_X_one (a b c : Poly) : sub (X 1) a b c = b := by simp [sub]
private theorem sub_X_two (a b c : Poly) : sub (X 2) a b c = c := by simp [sub]

/-- The exact ternary chain rule, over the actual characteristic-two polynomial ring. -/
theorem pderiv_sub (f a b c : Poly) (i : Fin 3) :
    pderiv i (sub f a b c) =
      sub (pderiv 0 f) a b c * pderiv i a +
        sub (pderiv 1 f) a b c * pderiv i b +
        sub (pderiv 2 f) a b c * pderiv i c := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [sub]
  | add f g hf hg => simp [sub_add, hf, hg]; ring
  | mul_X f j hf =>
    simp only [sub] at hf ⊢
    fin_cases j <;> simp [map_mul, map_add, hf] <;> ring

/-- A squared diagonal factor kills the first derivative on that diagonal. -/
theorem diagonal_pderiv_zero_of_square {f : Poly} (hf : (X 0+X 1 : Poly)^2 ∣ f)
    (u v : Poly) : sub (pderiv 0 f) u u v = 0 := by
  obtain ⟨g, rfl⟩ := hf
  rw [pow_two, pderiv_mul, pderiv_mul]
  simp [sub, CharTwo.add_self_eq_zero]

/-- Differentiating the norm around the diagonal kills the first boundary partial. -/
theorem boundary_pderiv_zero_of_diagonal_square {f : Poly} (hs : Symmetric f)
    (hn : norm f = 0) (hf : (X 0+X 1 : Poly)^2 ∣ f) :
    sub (pderiv 0 f) (X 0) 0 (X 2) = 0 := by
  have h := CharTwoProjector.sub_norm_zero hn (X 0+X 1) (X 1) (X 2)
  have hu : (X 0+X 1+X 1 : Poly) = X 0 := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hu, CharTwoProjector.sub_swap hs (X 0+X 1) (X 0) (X 2)] at h
  have hd := congrArg (pderiv (0 : Fin 3)) h
  simp [pderiv_sub] at hd
  have he := congrArg (fun g => sub g 0 (X 0) (X 2)) hd
  simp only [sub_add, sub_zero_poly, sub_comp, sub_X_zero, sub_X_one, sub_X_two,
    zero_add] at he
  rw [diagonal_pderiv_zero_of_square hf] at he
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) he

/-- Restriction to the middle coordinate plane. -/
def middleBoundary (f : Poly) : Poly := sub f (X 0) 0 (X 2)

private theorem middleBoundary_homogeneous {f : Poly} {n : ℕ} (hf : f.IsHomogeneous n) :
    (middleBoundary f).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hf
  intro i
  fin_cases i
  · exact isHomogeneous_X (ZMod 2) 0
  · exact isHomogeneous_zero (Fin 3) (ZMod 2) 1
  · exact isHomogeneous_X (ZMod 2) 2

private theorem middleBoundary_swap {f : Poly} (hs : Symmetric f) :
    sub (middleBoundary f) (X 2) (X 1) (X 0) = middleBoundary f := by
  rw [middleBoundary, sub_comp]
  simp only [sub_X_zero, sub_X_two, sub_zero_poly]
  exact (CharTwoProjector.sub_permutations hs (X 0) 0 (X 2)).2.2.2.2

/-- Odd homogeneous norm-kernel polynomials with a diagonal square vanish on the middle plane. -/
theorem middleBoundary_zero_of_odd_diagonal_square {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : Symmetric f)
    (hn : norm f = 0) (hsq : (X 0+X 1 : Poly)^2 ∣ f) : middleBoundary f = 0 := by
  have h0 : pderiv 0 (middleBoundary f) = 0 := by
    simpa [middleBoundary, pderiv_sub] using boundary_pderiv_zero_of_diagonal_square hs hn hsq
  have h1 : pderiv 1 (middleBoundary f) = 0 := by simp [middleBoundary, pderiv_sub]
  have h2 := congrArg (pderiv (2 : Fin 3)) (middleBoundary_swap hs)
  simp [pderiv_sub, h0, sub_zero_poly] at h2
  have he : ∑ i : Fin 3, X i * pderiv i (middleBoundary f) =
      (n : ZMod 2) • middleBoundary f := by
    simpa only [Nat.cast_smul_eq_nsmul] using (middleBoundary_homogeneous hf).sum_X_mul_pderiv
  rw [hodd.natCast_zmod_two, one_smul] at he
  simpa only [Fin.sum_univ_three, h0, h1, ← h2, mul_zero, add_zero] using he.symm

private theorem middleBoundary_sub_zero {f : Poly} (hf : middleBoundary f = 0) (u v : Poly) :
    sub f u 0 v = 0 := by
  have h := congrArg (fun g => sub g u 0 v) hf
  simpa only [middleBoundary, sub_comp, sub_X_zero, sub_X_two, sub_zero_poly] using h

/-- Symmetry propagates a zero middle plane to all three coordinate factors. -/
theorem c_dvd_of_middleBoundary_zero {f : Poly} (hs : Symmetric f) (hf : middleBoundary f = 0) :
    c ∣ f := by
  have hv0 : Function.update (X : Fin 3 → Poly) 0 0 = ![0,X 1,X 2] := by
    funext i; fin_cases i <;> simp
  have hv1 : Function.update (X : Fin 3 → Poly) 1 0 = ![X 0,0,X 2] := by
    funext i; fin_cases i <;> simp
  have hv2 : Function.update (X : Fin 3 → Poly) 2 0 = ![X 0,X 1,0] := by
    funext i; fin_cases i <;> simp
  have h0 : bind₁ (Function.update (X : Fin 3 → Poly) 0 0) f = 0 := by
    rw [hv0]
    change sub f 0 (X 1) (X 2) = 0
    rw [CharTwoProjector.sub_swap hs (X 1) 0 (X 2)]
    exact middleBoundary_sub_zero hf _ _
  have h1 : bind₁ (Function.update (X : Fin 3 → Poly) 1 0) f = 0 := by
    rw [hv1]
    exact hf
  have h2 : bind₁ (Function.update (X : Fin 3 → Poly) 2 0) f = 0 := by
    rw [hv2]
    change sub f (X 0) (X 1) 0 = 0
    rw [(CharTwoProjector.sub_permutations hs (X 0) 0 (X 1)).2.2.2.1]
    exact middleBoundary_sub_zero hf _ _
  have hd0 : (X 0 : Poly) ∣ f := by
    simpa only [sub_zero] using linear_factor_dvd_of_substitution_zero f 0 0 h0
  have hd1 : (X 0*X 1 : Poly) ∣ f := by
    simpa only [sub_zero] using mul_linear_factor_dvd_of_substitution_zero f (X 0) 1 0 hd0 h1
      (by simp)
  simpa only [c, sub_zero] using
    mul_linear_factor_dvd_of_substitution_zero f (X 0*X 1) 2 0 hd1 h2
      (by simp)

/-- Odd homogeneity and a diagonal square already force all three coordinate factors. -/
theorem c_dvd_of_odd_diagonal_square {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : Symmetric f)
    (hn : norm f = 0) (hsq : (X 0+X 1 : Poly)^2 ∣ f) : c ∣ f :=
  c_dvd_of_middleBoundary_zero hs (middleBoundary_zero_of_odd_diagonal_square hf hodd hs hn hsq)

/-- The odd-degree higher-multiplicity implication for the actual symmetric norm kernel. -/
theorem c_dvd_of_odd_cplus_square {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hs : Symmetric f)
    (hn : norm f = 0) (hsq : cplus^2 ∣ f) : c ∣ f := by
  have hd : (X 0+X 1 : Poly) ∣ cplus := by
    refine ⟨(X 0+X 2)*(X 1+X 2), ?_⟩
    rw [cplus_eq_product]
    ring
  exact c_dvd_of_odd_diagonal_square hf hodd hs hn ((pow_dvd_pow_of_dvd hd 2).trans hsq)

private theorem sub_mul (f g x y z : Poly) :
    sub (f*g) x y z = sub f x y z * sub g x y z := map_mul (bind₁ ![x,y,z]) f g

private theorem sub_identity (f : Poly) : sub f (X 0) (X 1) (X 2) = f := by
  have hv : (![X 0,X 1,X 2] : Fin 3 → Poly) = X := by
    funext i; fin_cases i <;> rfl
  simp only [sub, hv, bind₁_X_left, AlgHom.id_apply]

private theorem form01_ne_zero : (X 0+X 1 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

private theorem form02_ne_zero : (X 0+X 2 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,0,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

private theorem form12_ne_zero : (X 1+X 2 : Poly) ≠ 0 := by
  intro h
  have he := congrArg (eval (![0,1,0] : Fin 3 → ZMod 2)) h
  norm_num [Matrix.cons_val_two] at he

private theorem diagonal_factor_dvd {f : Poly} (hs : Symmetric f) (hn : norm f = 0) :
    (X 0+X 1 : Poly) ∣ f := by
  have hv : Function.update (X : Fin 3 → Poly) 0 (X 1) = ![X 1,X 1,X 2] := by
    funext i; fin_cases i <;> simp
  simpa only [sub_eq_add_neg, CharTwo.neg_eq] using
    linear_factor_dvd_of_substitution_zero f 0 (X 1)
      (by rw [hv]; exact norm_zero_diagonal hs hn (X 1) (X 2))

private theorem pderiv_diagonal_of_swap {k : Poly}
    (hk : sub k (X 1) (X 0) (X 2) = k) :
    pderiv 0 (sub k (X 0) (X 0) (X 2)) = 0 := by
  have hd := congrArg (pderiv (0 : Fin 3)) hk
  simp [pderiv_sub] at hd
  have h := congrArg (fun g => sub g (X 0) (X 0) (X 2)) hd
  simp only [sub_comp, sub_X_zero, sub_X_one, sub_X_two] at h
  simp [pderiv_sub, ← h, CharTwo.add_self_eq_zero]

/-- The first normal jet on the diagonal, with the middle output variable unused. -/
def diagonalJet (f : Poly) : Poly := sub (pderiv 1 f) (X 0) (X 0) (X 2)

/-- Symmetry of the quotient by the diagonal factor makes the jet constant in its first derivative. -/
theorem diagonalJet_pderiv_zero {f : Poly} (hs : Symmetric f) (hn : norm f = 0) :
    pderiv 0 (diagonalJet f) = 0 := by
  obtain ⟨k, hk⟩ := diagonal_factor_dvd hs hn
  have hswap : sub k (X 1) (X 0) (X 2) = k := by
    apply mul_left_cancel₀ form01_ne_zero
    have h := hs.swap
    rw [hk] at h
    simpa only [sub_mul, sub_add, sub_X_zero, sub_X_one, add_comm (X (1 : Fin 3)) (X 0)] using h
  have hj : diagonalJet f = sub k (X 0) (X 0) (X 2) := by
    rw [diagonalJet, hk, pderiv_mul]
    simp [sub, CharTwo.add_self_eq_zero]
  rw [hj]
  exact pderiv_diagonal_of_swap hswap

private theorem sub_pderiv_zero_of_square {L f : Poly} (hf : L^2 ∣ f)
    (x y z : Poly) (hL : sub L x y z = 0) (i : Fin 3) :
    sub (pderiv i f) x y z = 0 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_two, pderiv_mul, pderiv_mul]
  simp only [sub_add, sub_mul, hL, zero_mul, mul_zero, add_zero]

private theorem sub_a_triangle_zero (u v : Poly) : sub a (u+v) v u = 0 := by
  simp only [a, sub_add, sub_X_zero, sub_X_one, sub_X_two]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- A square of the coordinate sum forces shear invariance of the diagonal jet. -/
theorem diagonalJet_shear {f : Poly} (hs : Symmetric f) (hn : norm f = 0)
    (ha : a^2 ∣ f) : sub (diagonalJet f) (X 0) (X 1) (X 0+X 2) = diagonalJet f := by
  have h := CharTwoProjector.sub_norm_zero hn (X 0+X 2) (X 2) (X 0+X 1)
  have hu : (X 0+X 2+X 2 : Poly) = X 0 := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hu, ← CharTwoProjector.sub_cycle hs (X 2) (X 0) (X 0+X 1),
    ← (CharTwoProjector.sub_permutations hs (X 0) (X 0+X 2) (X 0+X 1)).2.2.2.1] at h
  have hd := congrArg (pderiv (1 : Fin 3)) h
  simp [pderiv_sub] at hd
  have he := congrArg (fun g => sub g (X 0) 0 (X 2)) hd
  simp only [sub_add, sub_zero_poly, sub_comp, sub_X_zero, sub_X_one, sub_X_two,
    add_zero] at he
  rw [sub_pderiv_zero_of_square ha (X 0+X 2) (X 2) (X 0)
    (sub_a_triangle_zero (X 0) (X 2)) 2, zero_add] at he
  simp only [diagonalJet, sub_comp, sub_X_zero, sub_X_two]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) he

private theorem diagonalJet_homogeneous {f : Poly} {n : ℕ} (hf : f.IsHomogeneous n) :
    (diagonalJet f).IsHomogeneous (n-1) := by
  apply isHomogeneous_bind₁_linear (hf.pderiv (i := 1))
  intro i
  fin_cases i <;> exact isHomogeneous_X (ZMod 2) _

/-- Shear invariance and odd jet degree kill the complete diagonal first jet. -/
theorem diagonalJet_zero_of_even_a_square {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) (heven : Even n) (hs : Symmetric f)
    (hn : norm f = 0) (ha : a^2 ∣ f) : diagonalJet f = 0 := by
  by_cases hf0 : f = 0
  · simp [hf0, diagonalJet, sub_zero_poly]
  have hnpos : 1 ≤ n := by
    obtain ⟨k, hk⟩ := diagonal_factor_dvd hs hn
    have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hf0 hk
    have ht := hf.totalDegree hf0
    rw [hk, totalDegree_mul_of_isDomain form01_ne_zero hk0,
      ((isHomogeneous_X (ZMod 2) (0 : Fin 3)).add
        (isHomogeneous_X (ZMod 2) (1 : Fin 3))).totalDegree form01_ne_zero] at ht
    omega
  have hodd : Odd (n-1) := Nat.Even.sub_odd hnpos heven (by decide : Odd (1 : ℕ))
  have h0 := diagonalJet_pderiv_zero hs hn
  have h1 : pderiv 1 (diagonalJet f) = 0 := by simp [diagonalJet, pderiv_sub]
  have hd := congrArg (pderiv (0 : Fin 3)) (diagonalJet_shear hs hn ha)
  simp [pderiv_sub, h0, sub_zero_poly] at hd
  have h2 := congrArg (fun g => sub g (X 0) (X 1) (X 0+X 2)) hd
  simp only [sub_comp, sub_add, sub_X_zero, sub_X_one, sub_X_two, sub_zero_poly] at h2
  have hu : (X 0+(X 0+X 2) : Poly) = X 2 := by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [hu, sub_identity] at h2
  have he : ∑ i : Fin 3, X i * pderiv i (diagonalJet f) =
      ((n-1 : ℕ) : ZMod 2) • diagonalJet f := by
    simpa only [Nat.cast_smul_eq_nsmul] using (diagonalJet_homogeneous hf).sum_X_mul_pderiv
  rw [hodd.natCast_zmod_two, one_smul] at he
  simpa only [Fin.sum_univ_three, h0, h1, h2, mul_zero, add_zero] using he.symm

/-- A symmetric polynomial vanishing on one diagonal contains all three diagonal factors. -/
theorem cplus_dvd_of_symmetric_diagonal_zero {f : Poly} (hs : Symmetric f)
    (hf : sub f (X 0) (X 0) (X 2) = 0) : cplus ∣ f := by
  have hdiag (u v : Poly) : sub f u u v = 0 := by
    have h := congrArg (fun g => sub g u 0 v) hf
    simpa only [sub_comp, sub_X_zero, sub_X_two, sub_zero_poly] using h
  have h01 : bind₁ (Function.update (X : Fin 3 → Poly) 0 (X 1)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 0 (X 1) = ![X 1,X 1,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact hdiag _ _
  have h02 : bind₁ (Function.update (X : Fin 3 → Poly) 0 (X 2)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 0 (X 2) = ![X 2,X 1,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    change sub f (X 2) (X 1) (X 2) = 0
    rw [CharTwoProjector.sub_cycle hs (X 2) (X 2) (X 1)]
    exact hdiag _ _
  have h12 : bind₁ (Function.update (X : Fin 3 → Poly) 1 (X 2)) f = 0 := by
    have hv : Function.update (X : Fin 3 → Poly) 1 (X 2) = ![X 0,X 2,X 2] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    change sub f (X 0) (X 2) (X 2) = 0
    rw [CharTwoProjector.sub_swap hs (X 2) (X 0) (X 2),
      CharTwoProjector.sub_cycle hs (X 2) (X 2) (X 0)]
    exact hdiag _ _
  have hd1 := linear_factor_dvd_of_substitution_zero f 0 (X 1) h01
  have hd2 := mul_linear_factor_dvd_of_substitution_zero f (X 0-X 1) 0 (X 2) hd1 h02
    (by simpa [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using form12_ne_zero)
  have hd3 := mul_linear_factor_dvd_of_substitution_zero f ((X 0-X 1)*(X 0-X 2)) 1 (X 2)
    hd2 h12 (by simpa [sub_eq_add_neg, CharTwo.neg_eq] using mul_ne_zero form02_ne_zero form02_ne_zero)
  simpa only [cplus_eq_product, sub_eq_add_neg, CharTwo.neg_eq] using hd3

private theorem cplus_ne_zero : cplus ≠ 0 := by
  rw [cplus_eq_product]
  exact mul_ne_zero (mul_ne_zero form01_ne_zero form02_ne_zero) form12_ne_zero

private theorem cplus_symmetric : Symmetric cplus := by
  apply CharTwoProjector.symmetric_of_isSymmetric
  intro σ
  obtain ⟨ha,hb,hc⟩ := rename_elementary σ
  simp [cplus, ha, hb, hc]

private theorem symmetric_of_cplus_mul {k : Poly} (hs : Symmetric (cplus*k)) :
    Symmetric k := by
  constructor
  · apply mul_left_cancel₀ cplus_ne_zero
    simpa only [sub_mul, cplus_symmetric.cyclic] using hs.cyclic
  · apply mul_left_cancel₀ cplus_ne_zero
    simpa only [sub_mul, cplus_symmetric.swap] using hs.swap

private theorem sub_cplus_diagonal : sub cplus (X 0) (X 0) (X 2) = 0 := by
  simp [cplus_eq_product, sub, CharTwo.add_self_eq_zero]

private theorem sub_pderiv_cplus_diagonal :
    sub (pderiv 1 cplus) (X 0) (X 0) (X 2) = (X 0+X 2)^2 := by
  simp [cplus_eq_product, sub, CharTwo.add_self_eq_zero, pow_two]

/-- In even degree, a square of the coordinate sum forces squares of every diagonal factor. -/
theorem cplus_square_dvd_of_even_a_square {f : Poly} {n : ℕ}
    (hf : f.IsHomogeneous n) (heven : Even n) (hs : Symmetric f)
    (hn : norm f = 0) (ha : a^2 ∣ f) : cplus^2 ∣ f := by
  obtain ⟨k,hk⟩ := cplus_dvd_of_symmetric_diagonal_zero hs
    (norm_zero_diagonal hs hn (X 0) (X 2))
  have hks : Symmetric k := symmetric_of_cplus_mul (hk ▸ hs)
  have hjet := diagonalJet_zero_of_even_a_square hf heven hs hn ha
  rw [diagonalJet, hk, pderiv_mul, sub_add, sub_mul, sub_mul,
    sub_cplus_diagonal, sub_pderiv_cplus_diagonal, zero_mul, add_zero] at hjet
  have hkdiag : sub k (X 0) (X 0) (X 2) = 0 :=
    (mul_eq_zero.mp hjet).resolve_left (pow_ne_zero 2 form02_ne_zero)
  obtain ⟨r,hr⟩ := cplus_dvd_of_symmetric_diagonal_zero hks hkdiag
  exact ⟨r, by rw [hk, hr, pow_two, mul_assoc]⟩

end TernaryPoly.CharTwoNorm
