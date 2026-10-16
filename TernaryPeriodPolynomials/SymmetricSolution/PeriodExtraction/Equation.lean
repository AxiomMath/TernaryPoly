module

public import TernaryPeriodPolynomials.SymmetricSolution.PeriodExtraction.Parity

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly
namespace SymmetricPeriodExtraction
local notation "BP" => MvPolynomial (Fin 2) ℚ

def bs (a b : BP) : BP →ₐ[ℚ] BP := bind₁ ![a,b]

 theorem bs_comp (a b c d p : BP) : bs a b (bs c d p)=bs (bs a b c) (bs a b d) p :=
  bind_comp p a b c d

 theorem bs_id (p : BP) : bs (X 0) (X 1) p=p := by
  have h : (![X 0,X 1] : Fin 2 → BP)=X := by funext i; fin_cases i <;> rfl
  simp [bs,h]

 theorem bs_odd_first {p : BP} (hx : bind₁ ![-X 0,X 1] p= -p) (a b : BP) :
    bs (-a) b p= -bs a b p := by
  have h := congrArg (bs a b) hx
  change bs a b (bs (-X 0) (X 1) p)=_ at h
  rw [bs_comp] at h
  simpa [bs] using h

 theorem bs_even_second {p : BP} (hy : bind₁ ![X 0,-X 1] p=p) (a b : BP) :
    bs a (-b) p=bs a b p := by
  have h := congrArg (bs a b) hy
  change bs a b (bs (X 0) (-X 1) p)=_ at h
  rw [bs_comp] at h
  simpa [bs] using h

 theorem primitive_substitute (n : ℕ) (p a b : BP) :
    bs a b (binaryPeriodPrimitive n p)=
      -(1 / ((n : ℚ)+1)) • (a*bs b (-a) p+b*bs a b p) := by
  simp only [bs,binaryPeriodPrimitive,binaryRotation,map_smul,map_add,map_mul,
    bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [bind_comp]
  simp

 theorem periodPrimitive_swap (n : ℕ) {p : BP} (hy : bind₁ ![X 0,-X 1] p=p) :
    bind₁ ![X 1,X 0] (binaryPeriodPrimitive n p)=binaryPeriodPrimitive n p := by
  change bs (X 1) (X 0) (binaryPeriodPrimitive n p)=_
  rw [primitive_substitute]
  have hq := primitive_substitute n p (X 0) (X 1)
  rw [bs_id] at hq
  rw [hq,bs_even_second hy,bs_even_second hy]
  congr 1
  ring

 theorem periodPrimitive_odd_first (n : ℕ) {p : BP}
    (hx : bind₁ ![-X 0,X 1] p= -p) (hy : bind₁ ![X 0,-X 1] p=p) :
    bind₁ ![-X 0,X 1] (binaryPeriodPrimitive n p)= -binaryPeriodPrimitive n p := by
  change bs (-X 0) (X 1) (binaryPeriodPrimitive n p)=_
  rw [primitive_substitute]
  have hq := primitive_substitute n p (X 0) (X 1)
  rw [bs_id] at hq
  rw [hq,neg_neg,bs_odd_first hx,bs_even_second hy,← smul_neg]
  congr 1
  ring

 theorem periodPrimitive_odd_second (n : ℕ) {p : BP}
    (hx : bind₁ ![-X 0,X 1] p= -p) (hy : bind₁ ![X 0,-X 1] p=p) :
    bind₁ ![X 0,-X 1] (binaryPeriodPrimitive n p)= -binaryPeriodPrimitive n p := by
  change bs (X 0) (-X 1) (binaryPeriodPrimitive n p)=_
  rw [primitive_substitute]
  have hq := primitive_substitute n p (X 0) (X 1)
  rw [bs_id] at hq
  rw [hq,bs_odd_first hx,bs_even_second hy (X 0) (X 1),← smul_neg]
  congr 1
  ring

private def diagonal (g : BP) : BP := pderiv 0 g+pderiv 1 g

private theorem diagonal_bs (g a b : BP) :
    diagonal (bs a b g)=bs a b (pderiv 0 g)*diagonal a+bs a b (pderiv 1 g)*diagonal b := by
  simp only [diagonal,bs]
  rw [binary_pderiv_substitution,binary_pderiv_substitution]
  ring

 theorem period_equation (p h q : BP)
    (hqswap : bind₁ ![X 1,X 0] q=q) (hpodd : bind₁ ![-X 0,X 1] p= -p)
    (hqder : pderiv 1 q= -p) (hhswap : bind₁ ![X 1,X 0] h= -h)
    (hdiff : bind₁ ![X 0-X 1,X 1] p-p=h)
    (hqdiag : bind₁ (![X 0,X 0] : Fin 2 → BP) q=0) :
    q-bind₁ ![X 0-X 1,X 1] q+bind₁ ![X 0,X 0-X 1] q=0 := by
  have hqx : pderiv 0 q= -bs (X 1) (X 0) p := by
    have ht := congrArg (pderiv (0 : Fin 2)) hqswap
    rw [binary_pderiv_substitution] at ht
    simpa [hqder,bs] using ht.symm
  have hleft : diagonal (bs (X 0-X 1) (X 1) q)=bs (X 0-X 1) (X 1) (pderiv 1 q) := by
    rw [diagonal_bs]
    simp [diagonal]
  have hright : diagonal (bs (X 0) (X 0-X 1) q)=bs (X 0) (X 0-X 1) (pderiv 0 q) := by
    rw [diagonal_bs]
    simp [diagonal]
  have hpodd' : bs (X 1-X 0) (X 0) p= -bs (X 0-X 1) (X 0) p := by
    rw [show (X 1-X 0 : BP)= -(X 0-X 1) by ring]
    exact bs_odd_first (p := p) hpodd _ _
  have hdiff' : bs (X 0-X 1) (X 0) p+bs (X 1) (X 0) p=h := by
    have ht := congrArg (bs (X 1) (X 0)) hdiff
    change bs (X 1) (X 0) (bs (X 0-X 1) (X 1) p-p)=_ at ht
    rw [map_sub,bs_comp,show bs (X 1) (X 0) h= -h from hhswap] at ht
    have ht' : bs (X 1-X 0) (X 0) p-bs (X 1) (X 0) p= -h := by simpa [bs] using ht
    rw [hpodd'] at ht'
    linear_combination -ht'
  apply binary_diagonal_derivative_rigidity
  · change diagonal (q-bs (X 0-X 1) (X 1) q+bs (X 0) (X 0-X 1) q)=0
    have hd : diagonal (q-bs (X 0-X 1) (X 1) q+bs (X 0) (X 0-X 1) q)=
        diagonal q-diagonal (bs (X 0-X 1) (X 1) q)+diagonal (bs (X 0) (X 0-X 1) q) := by
      simp only [diagonal,map_add,map_sub]
      abel
    rw [hd,hleft,hright]
    change (pderiv 0 q+pderiv 1 q)-bs (X 0-X 1) (X 1) (pderiv 1 q)+
      bs (X 0) (X 0-X 1) (pderiv 0 q)=0
    rw [hqx,hqder,map_neg,map_neg,bs_comp]
    have ht : bs (X 0) (X 0-X 1) (X 1)=X 0-X 1 := by simp [bs]
    have hu : bs (X 0) (X 0-X 1) (X 0)=X 0 := by simp [bs]
    rw [ht,hu]
    calc
      (-bs (X 1) (X 0) p+ -p)- -bs (X 0-X 1) (X 1) p+
          -bs (X 0-X 1) (X 0) p=
        (bs (X 0-X 1) (X 1) p-p)-(bs (X 0-X 1) (X 0) p+bs (X 1) (X 0) p) := by abel
      _ = h-h := by rw [show bs (X 0-X 1) (X 1) p-p=h from hdiff,hdiff']
      _ = 0 := sub_self h
  · change bs (X 0) 0 (q-bs (X 0-X 1) (X 1) q+bs (X 0) (X 0-X 1) q)=0
    rw [map_add,map_sub,bs_comp,bs_comp]
    have ht : bs (X 0) 0 (X 0-X 1)=X 0 := by simp [bs]
    have hu : bs (X 0) 0 (X 1)=0 := by simp [bs]
    have hv : bs (X 0) 0 (X 0)=X 0 := by simp [bs]
    rw [ht,hu,hv,show bs (X 0) (X 0) q=0 from hqdiag]
    simp

end SymmetricPeriodExtraction
end TernaryPoly
