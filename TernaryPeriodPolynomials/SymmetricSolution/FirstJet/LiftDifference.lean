module

public import TernaryPeriodPolynomials.SymmetricSolution.TwelveNorm
public import TernaryPeriodPolynomials.SymmetricSolution.FirstJet.LiftEvaluation

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricFirstLiftDifference

/-- The mixed equation and twelve norms annihilate the exact triple difference of `N Q`. -/
theorem norm_six_term {f Q : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f) (hf : N f=0)
    (hm : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f)
    (a b c : TernaryPolynomial) :
    -substitute3 (N Q) a b (a-b+c)-substitute3 (N Q) a b (b+c)
    -substitute3 (N Q) a b (-a+c)+substitute3 (N Q) a b (a+c)
    +substitute3 (N Q) a b (-b+c)+substitute3 (N Q) a b (-a+b+c)=0 := by
  have hn := SymmetricTwelveNorm.twelve_norm_identity hc hs hf a b c
  have h1 : substitute3 Q (a) (b) (c) - substitute3 Q (a) (b) (-a+c) = substitute3 f (c) (a-c) (b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (a) (b) (-a+c)
    have hz : (-a+c)+(a)=(c) := by ring
    have hx : (a)+(-a+c)=(c) := by ring
    have hnz : -(-a+c)=(a-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h2 : substitute3 Q (a) (b) (a-b+c) - substitute3 Q (a) (b) (-b+c) = substitute3 f (a-b+c) (b-c) (b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (a) (b) (-b+c)
    have hz : (-b+c)+(a)=(a-b+c) := by ring
    have hx : (a)+(-b+c)=(a-b+c) := by ring
    have hnz : -(-b+c)=(b-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h3 : substitute3 Q (a) (b) (b+c) - substitute3 Q (a) (b) (-a+b+c) = substitute3 f (b+c) (a-b-c) (b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (a) (b) (-a+b+c)
    have hz : (-a+b+c)+(a)=(b+c) := by ring
    have hx : (a)+(-a+b+c)=(b+c) := by ring
    have hnz : -(-a+b+c)=(a-b-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h4 : substitute3 Q (a) (b) (a+c) - substitute3 Q (a) (b) (c) = substitute3 f (a+c) (-c) (b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (a) (b) (c)
    have hz : (c)+(a)=(a+c) := by ring
    have hx : (a)+(c)=(a+c) := by ring
    have hnz : -(c)=(-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h5 : substitute3 Q (-b) (a-b) (c) - substitute3 Q (-b) (a-b) (b+c) = substitute3 f (c) (-b-c) (a-b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-b) (a-b) (b+c)
    have hz : (b+c)+(-b)=(c) := by ring
    have hx : (-b)+(b+c)=(c) := by ring
    have hnz : -(b+c)=(-b-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h6 : substitute3 Q (-b) (a-b) (a-b+c) - substitute3 Q (-b) (a-b) (a+c) = substitute3 f (a-b+c) (-a-c) (a-b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-b) (a-b) (a+c)
    have hz : (a+c)+(-b)=(a-b+c) := by ring
    have hx : (-b)+(a+c)=(a-b+c) := by ring
    have hnz : -(a+c)=(-a-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h7 : substitute3 Q (-b) (a-b) (-a+c) - substitute3 Q (-b) (a-b) (-a+b+c) = substitute3 f (-a+c) (a-b-c) (a-b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-b) (a-b) (-a+b+c)
    have hz : (-a+b+c)+(-b)=(-a+c) := by ring
    have hx : (-b)+(-a+b+c)=(-a+c) := by ring
    have hnz : -(-a+b+c)=(a-b-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h8 : substitute3 Q (-b) (a-b) (-b+c) - substitute3 Q (-b) (a-b) (c) = substitute3 f (-b+c) (-c) (a-b) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-b) (a-b) (c)
    have hz : (c)+(-b)=(-b+c) := by ring
    have hx : (-b)+(c)=(-b+c) := by ring
    have hnz : -(c)=(-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h9 : substitute3 Q (-a+b) (-a) (c) - substitute3 Q (-a+b) (-a) (a-b+c) = substitute3 f (c) (-a+b-c) (-a) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-a+b) (-a) (a-b+c)
    have hz : (a-b+c)+(-a+b)=(c) := by ring
    have hx : (-a+b)+(a-b+c)=(c) := by ring
    have hnz : -(a-b+c)=(-a+b-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h10 : substitute3 Q (-a+b) (-a) (b+c) - substitute3 Q (-a+b) (-a) (a+c) = substitute3 f (b+c) (-a-c) (-a) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-a+b) (-a) (a+c)
    have hz : (a+c)+(-a+b)=(b+c) := by ring
    have hx : (-a+b)+(a+c)=(b+c) := by ring
    have hnz : -(a+c)=(-a-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h11 : substitute3 Q (-a+b) (-a) (-a+c) - substitute3 Q (-a+b) (-a) (-b+c) = substitute3 f (-a+c) (b-c) (-a) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-a+b) (-a) (-b+c)
    have hz : (-b+c)+(-a+b)=(-a+c) := by ring
    have hx : (-a+b)+(-b+c)=(-a+c) := by ring
    have hnz : -(-b+c)=(b-c) := by ring
    simpa only [hz,hx,hnz] using he
  have h12 : substitute3 Q (-a+b) (-a) (-a+b+c) - substitute3 Q (-a+b) (-a) (c) = substitute3 f (-a+b+c) (-c) (-a) := by
    have he := SymmetricFirstLiftEvaluation.mixed_eval hm (-a+b) (-a) (c)
    have hz : (c)+(-a+b)=(-a+b+c) := by ring
    have hx : (-a+b)+(c)=(-a+b+c) := by ring
    have hnz : -(c)=(-c) := by ring
    simpa only [hz,hx,hnz] using he
  simp only [substitute3_norm]
  rw [show b-a= -a+b by ring]
  linear_combination hn + h1 - h2 - h3 + h4 + h5 - h6 - h7 + h8 + h9 - h10 - h11 + h12

/-- Expanded iterated forward differences, with their literal untranslated arguments. -/
theorem norm_triple_difference {f Q : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f) (hf : N f=0)
    (hm : bind₁ ![X 0,X 1,X 2+X 0] Q-Q=bind₁ ![X 0+X 2,-X 2,X 1] f)
    (a b c : TernaryPolynomial) :
    substitute3 (N Q) a b (c+a+(-b)+(b-a))
    -substitute3 (N Q) a b (c+a+(-b))
    -substitute3 (N Q) a b (c+a+(b-a))
    +substitute3 (N Q) a b (c+a)
    -substitute3 (N Q) a b (c+(-b)+(b-a))
    +substitute3 (N Q) a b (c+(-b))
    +substitute3 (N Q) a b (c+(b-a))
    -substitute3 (N Q) a b c=0 := by
  have he := norm_six_term hc hs hf hm a b c
  rw [show c+a+(-b)+(b-a)=c by ring,
    show c+a+(-b)=a-b+c by ring,
    show c+a+(b-a)=b+c by ring,
    show c+a=a+c by ring,
    show c+(-b)+(b-a)= -a+c by ring,
    show c+(-b)= -b+c by ring,
    show c+(b-a)= -a+b+c by ring]
  linear_combination he

end TernaryPoly.SymmetricFirstLiftDifference
