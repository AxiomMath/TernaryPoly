module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.SeedFibers

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinarySeedNorms
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryPolynomialNorm OrdinarySeedFibers

private theorem substitute_add (g h a b c : TernaryPolynomial) :
    substitute3 (g+h) a b c=substitute3 g a b c+substitute3 h a b c := map_add _ _ _
private theorem substitute_sub (g h a b c : TernaryPolynomial) :
    substitute3 (g-h) a b c=substitute3 g a b c-substitute3 h a b c := map_sub _ _ _

/-- The first mixed seed identity in arbitrary polynomial coordinates. -/
theorem mixedQ_eval {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) :
    substitute3 Q a b (c+a)-substitute3 Q a b c=substitute3 f (a+c) (-c) b := by
  have he := congrArg (fun t => substitute3 t a b c) h.mixedQ
  change substitute3 (substitute3 Q (X 0) (X 1) (X 2+X 0)-Q) a b c =
    substitute3 (substitute3 f (X 0+X 2) (-X 2) (X 1)) a b c at he
  rw [substitute_sub,substitute3_substitute3,substitute3_substitute3] at he
  simpa [substitute3] using he

/-- The second mixed seed identity in arbitrary polynomial coordinates. -/
theorem mixedP_eval {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) :
    substitute3 P a (c+a) b-substitute3 P a c b=substitute3 Q (-c) (a+c) b := by
  have he := congrArg (fun t => substitute3 t a b c) h.mixedP
  change substitute3 (substitute3 P (X 0) (X 2+X 0) (X 1)-
    substitute3 P (X 0) (X 2) (X 1)) a b c =
    substitute3 (substitute3 Q (-X 2) (X 0+X 2) (X 1)) a b c at he
  rw [substitute_sub,substitute3_substitute3,substitute3_substitute3,
    substitute3_substitute3] at he
  simpa [substitute3] using he

/-- The P norm in arbitrary polynomial coordinates. -/
theorem p_norm_eval {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) :
    substitute3 P a b c+substitute3 P a (-c) (b-c)+
      substitute3 P a (c-b) (-b)=0 := by
  have he := congrArg (fun t => substitute3 t a b c) h.p_norm
  change substitute3 (P+substitute3 P (X 0) (-X 2) (X 1-X 2)+
    substitute3 P (X 0) (X 2-X 1) (-X 1)) a b c = substitute3 0 a b c at he
  simp only [substitute_add,substitute3_substitute3] at he
  simpa [substitute3] using he

private theorem Q_swap {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) : substitute3 Q a b c=substitute3 Q b a c := by
  have he := congrArg (fun t => substitute3 t a b c) h.q_swap
  change substitute3 (substitute3 Q (X 1) (X 0) (X 2)) a b c=substitute3 Q a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he.symm

private theorem A_substitute (g a b c : TernaryPolynomial) :
    A (substitute3 g a b c)=substitute3 g (A a) (A b) (A c) :=
  substitute3_substitute3 g a b c (-X 1) (X 0-X 1) (X 2)
private theorem A2_substitute (g a b c : TernaryPolynomial) :
    A2 (substitute3 g a b c)=substitute3 g (A2 a) (A2 b) (A2 c) :=
  substitute3_substitute3 g a b c (X 1-X 0) (-X 0) (X 2)

/-- All five literal norms follow from the two mixed equations and three seed norms. -/
theorem five_seed_norms {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (hf : N f=0) (hQ : N Q=0) (i : Fin 5) :
    fiberNorm (seedValue f P Q) (representative i)=0 := by
  fin_cases i
  · change substitute3 P (X 2) (X 0) (X 1)+
      A (substitute3 P (X 2) (X 0) (X 1))+
      A2 (substitute3 P (X 2) (X 0) (X 1))=0
    simp only [A_substitute,A2_substitute]
    simpa only [A,A2,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using p_norm_eval h (X 2) (X 0) (X 1)
  · change seedValue f P Q ![1,1,0]+A (seedValue f P Q ![1,1,0])+
      A2 (seedValue f P Q ![1,1,0])=0
    simpa only [seedValue_two,N_apply] using hQ
  · change seedValue f P Q ![1,1,1]+A (seedValue f P Q ![1,1,1])+
      A2 (seedValue f P Q ![1,1,1])=0
    simpa only [seedValue_three,N_apply] using hf
  · change substitute3 Q (X 0) (X 2) (X 1)+
      A (-substitute3 f (-X 0) (X 1) (X 2))+
      A2 (-substitute3 Q (-X 1) (X 2) (X 0))=0
    simp only [map_neg,A_substitute,A2_substitute]
    simp only [A, A2, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
    have he := mixedQ_eval h (X 0) (X 2) (X 1-X 0)
    have ha : X 1-X 0+X 0=(X 1 : TernaryPolynomial) := by ring
    have hb : X 0+(X 1-X 0)=(X 1 : TernaryPolynomial) := by ring
    have hc : -(X 1-X 0)=(X 0-X 1 : TernaryPolynomial) := by ring
    rw [ha,hb,hc] at he
    linear_combination he
  · change substitute3 P (X 0) (X 1) (X 2)+
      A (-substitute3 Q (-X 0) (X 1) (X 2))+
      A2 (-substitute3 P (-X 1) (X 0) (X 2))=0
    simp only [map_neg,A_substitute,A2_substitute]
    simp only [A, A2, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
    have he := mixedP_eval h (X 0) (X 2) (X 1-X 0)
    have ha : X 1-X 0+X 0=(X 1 : TernaryPolynomial) := by ring
    have hb : X 0+(X 1-X 0)=(X 1 : TernaryPolynomial) := by ring
    have hc : -(X 1-X 0)=(X 0-X 1 : TernaryPolynomial) := by ring
    rw [ha,hb,hc,Q_swap h (X 0-X 1) (X 1) (X 2)] at he
    linear_combination he

/-- The complete26-fiber polynomial norm system, with no degree bound. -/
theorem seedValue_all_norms {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (hf : N f=0) (hQ : N Q=0) :
    ∀ r : Covector,r≠0 → fiberNorm (seedValue f P Q) r=0 :=
  all_norms_of_five (seedValue f P Q) (seedValue_sign12 h) (seedValue_sign3 h)
    (five_seed_norms h hf hQ)

end TernaryPoly.OrdinarySeedNorms
