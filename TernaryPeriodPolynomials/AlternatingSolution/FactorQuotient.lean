module

public import TernaryPeriodPolynomials.Polynomial.Operators
public import TernaryPeriodPolynomials.Topology.HomogeneousQuotient
public import Mathlib.Tactic.Ring

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The nine linear factors forced by the alternating first-jet descent. -/
def binaryLiftNineFactor : TernaryPolynomial :=
  (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) *
    (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) * (X 0+X 1-X 2)

/-- A single rational evaluation certifies that the factor is nonzero. -/
theorem binaryLiftNineFactor_ne_zero : binaryLiftNineFactor ≠ 0 := by
  intro h
  have he := congrArg (eval (![1,3,9] : Fin 3 → ℚ)) h
  norm_num [binaryLiftNineFactor, Matrix.cons_val_two] at he

/-- The product of the nine homogeneous linear factors has degree nine. -/
theorem binaryLiftNineFactor_isHomogeneous : binaryLiftNineFactor.IsHomogeneous 9 := by
  have h0 := isHomogeneous_X ℚ (0 : Fin 3)
  have h1 := isHomogeneous_X ℚ (1 : Fin 3)
  have h2 := isHomogeneous_X ℚ (2 : Fin 3)
  exact ((((((((h0.sub h1).mul (h0.add h1)).mul (h0.sub h2)).mul (h0.add h2)).mul
    (h1.sub h2)).mul (h1.add h2)).mul ((h0.sub h1).sub h2)).mul
    ((h0.sub h1).add h2)).mul ((h0.add h1).sub h2)

/-- The nine-factor product is invariant under cyclic permutation. -/
theorem binaryLiftNineFactor_cyclic : C binaryLiftNineFactor = binaryLiftNineFactor := by
  simp [binaryLiftNineFactor, C]
  ring

/-- Swapping the first two variables changes the sign of the nine-factor product. -/
theorem binaryLiftNineFactor_swap : S binaryLiftNineFactor = -binaryLiftNineFactor := by
  simp [binaryLiftNineFactor, S]
  ring

/-- The nonzero factor cancels from cyclic invariance. -/
theorem cyclic_of_binaryLiftNineFactor_mul {H : TernaryPolynomial}
    (hc : C (binaryLiftNineFactor*H) = binaryLiftNineFactor*H) : C H = H := by
  apply mul_left_cancel₀ binaryLiftNineFactor_ne_zero
  simpa only [map_mul, binaryLiftNineFactor_cyclic] using hc

/-- Dividing an alternating polynomial by the alternating factor gives swap invariance. -/
theorem symmetric_of_binaryLiftNineFactor_mul {H : TernaryPolynomial}
    (hs : S (binaryLiftNineFactor*H) = -(binaryLiftNineFactor*H)) : S H = H := by
  apply mul_left_cancel₀ binaryLiftNineFactor_ne_zero
  apply neg_injective
  simpa only [map_mul, binaryLiftNineFactor_swap, neg_mul] using hs

/-- A nonzero quotient can occur only when the original degree is at least nine. -/
theorem binaryLiftNineFactor_quotient_degree_le {H : TernaryPolynomial} {n : ℕ}
    (hf : (binaryLiftNineFactor*H).IsHomogeneous n) (hH : H ≠ 0) : 9 ≤ n := by
  have he := hf.totalDegree (mul_ne_zero binaryLiftNineFactor_ne_zero hH)
  rw [totalDegree_mul_of_isDomain binaryLiftNineFactor_ne_zero hH,
    binaryLiftNineFactor_isHomogeneous.totalDegree binaryLiftNineFactor_ne_zero] at he
  omega

/-- Homogeneous alternating division by the nine-factor product gives a symmetric quotient. -/
theorem exists_symmetric_quotient_binaryLiftNineFactor {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hc : C f = f) (hs : S f = -f)
    (hd : binaryLiftNineFactor ∣ f) :
    ∃ H : TernaryPolynomial, f = binaryLiftNineFactor*H ∧
      H.IsHomogeneous (n-9) ∧ C H = H ∧ S H = H ∧ (H ≠ 0 → 9 ≤ n) := by
  obtain ⟨H, hH⟩ := hd
  have hp : (binaryLiftNineFactor*H).IsHomogeneous n := by rwa [← hH]
  refine ⟨H, hH, isHomogeneous_quotient binaryLiftNineFactor_isHomogeneous
    binaryLiftNineFactor_ne_zero hp, ?_, ?_, binaryLiftNineFactor_quotient_degree_le hp⟩
  · apply cyclic_of_binaryLiftNineFactor_mul
    rwa [← hH]
  · apply symmetric_of_binaryLiftNineFactor_mul
    rwa [← hH]

/-- Odd degree leaves an even-degree symmetric quotient after removing the nine factors. -/
theorem alternating_factor_symmetric_even_quotient {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hd : binaryLiftNineFactor ∣ f) :
    ∃ (m : ℕ) (H : TernaryPolynomial), f = binaryLiftNineFactor*H ∧
      H.IsHomogeneous (2*m) ∧ C H = H ∧ S H = H := by
  obtain ⟨H, hH, hdeg, hcyc, hswap, _⟩ :=
    exists_symmetric_quotient_binaryLiftNineFactor hf hc hs hd
  have he : Even (n-9) := Nat.Odd.sub_odd hodd (by decide : Odd (9 : ℕ))
  obtain ⟨m, hm⟩ := he
  refine ⟨m, H, hH, ?_, hcyc, hswap⟩
  simpa only [hm, two_mul] using hdeg

end TernaryPoly
