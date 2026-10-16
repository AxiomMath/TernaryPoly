module

public import TernaryPeriodPolynomials.SymmetricSolution.ToddCertificate

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricTwelveNorm

/-- The exact twelve-term common-denominator difference certificate. -/
theorem twelve_norm_identity {f : TernaryPolynomial}
    (hc : C f=f) (hs : S f=f) (hn : N f=0) (a b c : TernaryPolynomial) :
    substitute3 f (c) (a-c) (b)
    - substitute3 f (a-b+c) (b-c) (b)
    - substitute3 f (b+c) (a-b-c) (b)
    + substitute3 f (a+c) (-c) (b)
    + substitute3 f (c) (-b-c) (a-b)
    - substitute3 f (a-b+c) (-a-c) (a-b)
    - substitute3 f (-a+c) (a-b-c) (a-b)
    + substitute3 f (-b+c) (-c) (a-b)
    + substitute3 f (c) (-a+b-c) (-a)
    - substitute3 f (b+c) (-a-c) (-a)
    - substitute3 f (-a+c) (b-c) (-a)
    + substitute3 f (-a+b+c) (-c) (-a) = 0 := by
  have n1 : substitute3 f (b) (a+c) (-c) +
      substitute3 f (-a-c) (-a+b-c) (-c) +
      substitute3 f (a-b+c) (-b) (-c) = 0 := by
    have he := congrArg (fun p => substitute3 p (b) (a+c) (-c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (b) (a+c) (-c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(a+c)) ((b)-(a+c)) (-c) = substitute3 f (-a-c) (-a+b-c) (-c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((a+c)-(b)) (-(b)) (-c) = substitute3 f (a-b+c) (-b) (-c) := by
      congr 1; ring
    rw [h2,h3] at he
    exact he
  have n2 : substitute3 f (b-c) (b) (a-b+c) +
      substitute3 f (-b) (-c) (a-b+c) +
      substitute3 f (c) (-b+c) (a-b+c) = 0 := by
    have he := congrArg (fun p => substitute3 p (b-c) (b) (a-b+c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (b-c) (b) (a-b+c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(b)) ((b-c)-(b)) (a-b+c) = substitute3 f (-b) (-c) (a-b+c) := by
      congr 1; ring
    have h3 : substitute3 f ((b)-(b-c)) (-(b-c)) (a-b+c) = substitute3 f (c) (-b+c) (a-b+c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n3 : substitute3 f (b) (b+c) (a-b-c) +
      substitute3 f (-b-c) (-c) (a-b-c) +
      substitute3 f (c) (-b) (a-b-c) = 0 := by
    have he := congrArg (fun p => substitute3 p (b) (b+c) (a-b-c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (b) (b+c) (a-b-c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(b+c)) ((b)-(b+c)) (a-b-c) = substitute3 f (-b-c) (-c) (a-b-c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((b+c)-(b)) (-(b)) (a-b-c) = substitute3 f (c) (-b) (a-b-c) := by
      congr 1; ring
    rw [h2,h3] at he
    exact he
  have n4 : substitute3 f (b) (a-c) (c) +
      substitute3 f (-a+c) (-a+b+c) (c) +
      substitute3 f (a-b-c) (-b) (c) = 0 := by
    have he := congrArg (fun p => substitute3 p (b) (a-c) (c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (b) (a-c) (c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(a-c)) ((b)-(a-c)) (c) = substitute3 f (-a+c) (-a+b+c) (c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((a-c)-(b)) (-(b)) (c) = substitute3 f (a-b-c) (-b) (c) := by
      congr 1; ring
    rw [h2,h3] at he
    exact he
  have n5 : substitute3 f (-b+c) (a-b) (-c) +
      substitute3 f (-a+b) (-a+c) (-c) +
      substitute3 f (a-c) (b-c) (-c) = 0 := by
    have he := congrArg (fun p => substitute3 p (-b+c) (a-b) (-c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (-b+c) (a-b) (-c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(a-b)) ((-b+c)-(a-b)) (-c) = substitute3 f (-a+b) (-a+c) (-c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((a-b)-(-b+c)) (-(-b+c)) (-c) = substitute3 f (a-c) (b-c) (-c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n6 : substitute3 f (a-b) (a-b+c) (-a-c) +
      substitute3 f (-a+b-c) (-c) (-a-c) +
      substitute3 f (c) (-a+b) (-a-c) = 0 := by
    have he := congrArg (fun p => substitute3 p (a-b) (a-b+c) (-a-c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (a-b) (a-b+c) (-a-c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(a-b+c)) ((a-b)-(a-b+c)) (-a-c) = substitute3 f (-a+b-c) (-c) (-a-c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((a-b+c)-(a-b)) (-(a-b)) (-a-c) = substitute3 f (c) (-a+b) (-a-c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n7 : substitute3 f (a-b-c) (a-b) (-a+c) +
      substitute3 f (-a+b) (-c) (-a+c) +
      substitute3 f (c) (-a+b+c) (-a+c) = 0 := by
    have he := congrArg (fun p => substitute3 p (a-b-c) (a-b) (-a+c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (a-b-c) (a-b) (-a+c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(a-b)) ((a-b-c)-(a-b)) (-a+c) = substitute3 f (-a+b) (-c) (-a+c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((a-b)-(a-b-c)) (-(a-b-c)) (-a+c) = substitute3 f (c) (-a+b+c) (-a+c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n8 : substitute3 f (-b-c) (a-b) (c) +
      substitute3 f (-a+b) (-a-c) (c) +
      substitute3 f (a+c) (b+c) (c) = 0 := by
    have he := congrArg (fun p => substitute3 p (-b-c) (a-b) (c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (-b-c) (a-b) (c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(a-b)) ((-b-c)-(a-b)) (c) = substitute3 f (-a+b) (-a-c) (c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((a-b)-(-b-c)) (-(-b-c)) (c) = substitute3 f (a+c) (b+c) (c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n9 : substitute3 f (-a) (-a+b+c) (-c) +
      substitute3 f (a-b-c) (-b-c) (-c) +
      substitute3 f (b+c) (a) (-c) = 0 := by
    have he := congrArg (fun p => substitute3 p (-a) (-a+b+c) (-c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (-a) (-a+b+c) (-c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(-a+b+c)) ((-a)-(-a+b+c)) (-c) = substitute3 f (a-b-c) (-b-c) (-c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((-a+b+c)-(-a)) (-(-a)) (-c) = substitute3 f (b+c) (a) (-c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n10 : substitute3 f (-a-c) (-a) (b+c) +
      substitute3 f (a) (-c) (b+c) +
      substitute3 f (c) (a+c) (b+c) = 0 := by
    have he := congrArg (fun p => substitute3 p (-a-c) (-a) (b+c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (-a-c) (-a) (b+c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(-a)) ((-a-c)-(-a)) (b+c) = substitute3 f (a) (-c) (b+c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((-a)-(-a-c)) (-(-a-c)) (b+c) = substitute3 f (c) (a+c) (b+c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n11 : substitute3 f (-a) (-a+c) (b-c) +
      substitute3 f (a-c) (-c) (b-c) +
      substitute3 f (c) (a) (b-c) = 0 := by
    have he := congrArg (fun p => substitute3 p (-a) (-a+c) (b-c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (-a) (-a+c) (b-c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(-a+c)) ((-a)-(-a+c)) (b-c) = substitute3 f (a-c) (-c) (b-c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((-a+c)-(-a)) (-(-a)) (b-c) = substitute3 f (c) (a) (b-c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  have n12 : substitute3 f (-a) (-a+b-c) (c) +
      substitute3 f (a-b+c) (-b+c) (c) +
      substitute3 f (b-c) (a) (c) = 0 := by
    have he := congrArg (fun p => substitute3 p (-a) (-a+b-c) (c)) hn
    rw [substitute3_norm] at he
    have hz : substitute3 0 (-a) (-a+b-c) (c) = 0 := by simp [substitute3]
    rw [hz] at he
    have h2 : substitute3 f (-(-a+b-c)) ((-a)-(-a+b-c)) (c) = substitute3 f (a-b+c) (-b+c) (c) := by
      congr 1 <;> ring
    have h3 : substitute3 f ((-a+b-c)-(-a)) (-(-a)) (c) = substitute3 f (b-c) (a) (c) := by
      congr 1 <;> ring
    rw [h2,h3] at he
    exact he
  simp only [symmetric_substitute3_swap hs,symmetric_substitute3_swap_last hc hs] at n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 ⊢
  linear_combination n1 - n2 - n3 + n4 + n5 - n6 - n7 + n8 + n9 - n10 - n11 + n12

end TernaryPoly.SymmetricTwelveNorm
