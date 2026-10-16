module

public import TernaryPeriodPolynomials.SymmetricSolution.ToddCertificate
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricFirstLiftEvaluation

private theorem substitute_sub (g h a b c : TernaryPolynomial) :
    substitute3 (g-h) a b c=substitute3 g a b c-substitute3 h a b c := map_sub _ _ _

theorem mixed_eval {f Q : TernaryPolynomial}
    (hm : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f)
    (a b c : TernaryPolynomial) :
    substitute3 Q a b (c+a)-substitute3 Q a b c=substitute3 f (a+c) (-c) b := by
  have he := congrArg (fun t => substitute3 t a b c) hm
  change substitute3 (substitute3 Q (X 0) (X 1) (X 2+X 0)-Q) a b c =
    substitute3 (substitute3 f (X 0+X 2) (-X 2) (X 1)) a b c at he
  rw [substitute_sub,substitute3_substitute3,substitute3_substitute3] at he
  simpa [substitute3] using he

theorem odd_eval {Q : TernaryPolynomial}
    (ho : bind₁ ![X 0,X 1,-X 2] Q= -Q) (a b c : TernaryPolynomial) :
    substitute3 Q a b (-c)= -substitute3 Q a b c := by
  have he := congrArg (fun t => substitute3 t a b c) ho
  change substitute3 (substitute3 Q (X 0) (X 1) (-X 2)) a b c=
    substitute3 (-Q) a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he

theorem zero_eval {Q : TernaryPolynomial}
    (ho : bind₁ ![X 0,X 1,-X 2] Q= -Q) (a b : TernaryPolynomial) :
    substitute3 Q a b 0=0 := by
  have he := odd_eval ho a b 0
  rw [neg_zero] at he
  exact CharZero.eq_neg_self_iff.mp he

theorem step_eval {f Q : TernaryPolynomial}
    (ho : bind₁ ![X 0,X 1,-X 2] Q= -Q)
    (hm : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f)
    (a b : TernaryPolynomial) : substitute3 Q a b a=substitute3 f a 0 b := by
  have he := mixed_eval hm a b 0
  simpa only [zero_add,add_zero,neg_zero,zero_eval ho,sub_zero] using he

/-- The remaining linear norm defect vanishes at its first step, without a degree hypothesis. -/
theorem norm_at_step {f Q : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f) (hf : N f=0) (hqs : S Q=Q)
    (ho : bind₁ ![X 0,X 1,-X 2] Q= -Q)
    (hm : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f)
    (a b : TernaryPolynomial) : substitute3 (N Q) a b a=0 := by
  have h1 := step_eval ho hm a b
  have h2 : substitute3 Q (-b) (a-b) a=
      substitute3 f (-b) 0 (a-b)-substitute3 f (a-b) (-a) (a-b) := by
    have he := mixed_eval hm (-b) (a-b) a
    rw [show a+ -b=a-b by ring,show -b+a=a-b by ring,
      symmetric_substitute3_swap hqs (a-b) (-b) (a-b),step_eval ho hm,
      symmetric_substitute3_reverse hc hs (-b) 0 (a-b)] at he
    linear_combination -he
  have h3 : substitute3 Q (b-a) (-a) a= -substitute3 f (b-a) 0 (-a) := by
    have he := odd_eval ho (b-a) (-a) a
    rw [symmetric_substitute3_swap hqs (-a) (b-a) (-a),step_eval ho hm,
      symmetric_substitute3_reverse hc hs (b-a) 0 (-a)] at he
    linear_combination he
  have n1 : substitute3 f a b 0+substitute3 f (-b) (a-b) 0+
      substitute3 f (b-a) (-a) 0=0 := by
    rw [← substitute3_norm,hf]
    exact map_zero (bind₁ ![a,b,0])
  have n2 : substitute3 f (b-a) 0 (-a)+substitute3 f 0 (b-a) (-a)+
      substitute3 f (a-b) (a-b) (-a)=0 := by
    have he : substitute3 (N f) (b-a) 0 (-a)=0 := by
      rw [hf]
      exact map_zero (bind₁ ![b-a,0,-a])
    rw [substitute3_norm] at he
    simpa only [neg_zero,sub_zero,zero_sub,neg_sub] using he
  rw [substitute3_norm,h1,h2,h3]
  simp only [symmetric_substitute3_swap hs,symmetric_substitute3_swap_last hc hs] at n1 n2 ⊢
  linear_combination n1-n2

end TernaryPoly.SymmetricFirstLiftEvaluation
