module

public import TernaryPeriodPolynomials.AlternatingSolution.Factor
public import TernaryPeriodPolynomials.Building.Primitive.Transfer
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import Mathlib.Algebra.CharP.Two

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- The literal nine-factor polynomial over the integers. -/
def integerNineFactor : MvPolynomial (Fin 3) ℤ :=
  (X 0-X 1) * (X 0+X 1) * (X 0-X 2) * (X 0+X 2) *
    (X 1-X 2) * (X 1+X 2) * (X 0-X 1-X 2) * (X 0-X 1+X 2) * (X 0+X 1-X 2)

theorem integerNineFactor_map_rat :
    map (Int.castRingHom ℚ) integerNineFactor = binaryLiftNineFactor := by
  simp [integerNineFactor, binaryLiftNineFactor]

/-- Reduction of the nine literal factors is the compressed characteristic-two factor. -/
theorem integerNineFactor_map_modTwo :
    map (Int.castRingHom (ZMod 2)) integerNineFactor =
      CharTwoNorm.a ^ 3 * CharTwoNorm.cplus ^ 2 := by
  simp [integerNineFactor, CharTwoNorm.a, CharTwoNorm.b, CharTwoNorm.c,
    CharTwoNorm.cplus, CharTwo.sub_eq_add]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod]

/-- Cyclic invariance of an integral multiple reflects through the injective rational map. -/
theorem integral_multiple_cyclic {H : TernaryPolynomial} (hc : C H = H)
    {s : ℚ} {p : MvPolynomial (Fin 3) ℤ}
    (hp : map (Int.castRingHom ℚ) p = s • H) :
    bind₁ ![X 1, X 2, X 0] p = p := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [PrimitiveTransfer.map_bind_vec3, hp]
  simp only [map_X]
  change C (s • H) = s • H
  rw [map_smul, hc]

/-- The literal integral norm becomes the exact characteristic-two norm after reduction. -/
theorem modTwo_norm_of_integer_relations {p : MvPolynomial (Fin 3) ℤ}
    (hp : PrimitiveTransfer.Relations p) :
    CharTwoNorm.norm (map (Int.castRingHom (ZMod 2)) p) = 0 := by
  have h := (hp.map (Int.castRingHom (ZMod 2))).2
  simpa only [CharTwoNorm.norm, CharTwoNorm.sub₁, CharTwoNorm.sub₂,
    CharTwo.neg_eq, CharTwo.sub_eq_add,
    add_comm (X 1 : CharTwoNorm.Poly) (X 0)] using h

/-- Normalize the symmetric quotient itself, retaining a nonzero mod-two multiplier.
The entire Todd equation and the integral norm are inherited from the actual rational solution. -/
theorem odd_alternating_integral_reduction {f : TernaryPolynomial} {n : ℕ}
    (hf0 : f ≠ 0) (hf : f.IsHomogeneous n) (hodd : Odd n)
    (hc : C f = f) (hs : S f = -f) (hn : N f = 0) :
    ∃ (m : ℕ) (s : ℚ) (p : MvPolynomial (Fin 3) ℤ),
      s ≠ 0 ∧
      map (Int.castRingHom ℚ) (integerNineFactor * p) = s • f ∧
      p.IsHomogeneous (2*m) ∧
      bind₁ ![X 1, X 2, X 0] p = p ∧
      bind₁ ![X 1, X 0, X 2] p = p ∧
      map (Int.castRingHom (ZMod 2)) p ≠ 0 ∧
      alternatingTodd (map (Int.castRingHom ℚ) (integerNineFactor * p)) = 0 ∧
      PrimitiveTransfer.Relations (integerNineFactor * p) ∧
      CharTwoNorm.norm ((CharTwoNorm.a ^ 3 * CharTwoNorm.cplus ^ 2) *
        map (Int.castRingHom (ZMod 2)) p) = 0 := by
  obtain ⟨_, m, H, hfactor, hdegree, hcyclic, hswap⟩ :=
    alternating_norm_factorization hf hodd hc hs hn
  have hH0 : H ≠ 0 := by
    intro hH
    apply hf0
    simpa only [hH, mul_zero] using hfactor
  obtain ⟨s, hs0, p, hp, hp2⟩ := exists_primitive_integral_multiple hH0
  have hmap : map (Int.castRingHom ℚ) (integerNineFactor * p) = s • f := by
    rw [map_mul, integerNineFactor_map_rat, hp, mul_smul_comm, ← hfactor]
  have hpdeg : p.IsHomogeneous (2*m) := by
    apply IsHomogeneous.of_map (f := Int.castRingHom ℚ) Int.cast_injective
    rw [hp]
    exact (homogeneousSubmodule (Fin 3) ℚ (2*m)).smul_mem s hdegree
  have hpc : bind₁ ![X 1, X 2, X 0] p = p := integral_multiple_cyclic hcyclic hp
  have hps : bind₁ ![X 1, X 0, X 2] p = p := by
    simpa only [one_smul] using
      PrimitiveTransfer.integral_multiple_swap 1 (by simpa using hswap) hp
  have hrel := (PrimitiveTransfer.integral_multiple_relations ⟨hc, hn⟩ hf hmap).2
  have hj : alternatingTodd (map (Int.castRingHom ℚ) (integerNineFactor * p)) = 0 := by
    rw [hmap]
    apply alternatingTodd_eq_zero ((homogeneousSubmodule (Fin 3) ℚ n).smul_mem s hf) hodd
    · rw [map_smul, hc]
    · rw [map_smul, hs, smul_neg]
    · rw [map_smul, hn, smul_zero]
  refine ⟨m, s, p, hs0, hmap, hpdeg, hpc, hps, hp2, hj, hrel, ?_⟩
  have hnorm := modTwo_norm_of_integer_relations hrel
  simpa only [map_mul, integerNineFactor_map_modTwo] using hnorm

end TernaryPoly
