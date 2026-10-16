module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeTwist

@[expose] public section


/-!
# The Hecke transfer in the Hom model: `T₃(p,1)|_res = p T₂(p) + p² I`

Paper: Appendix A.3 "The Hecke
transfer" and `eq:Hecke-formula`.  This file reuses the library's Hom
model Hecke correspondences (`OrdinaryHomHecke.rationalHecke`, `BinaryRationalHecke.rationalHecke`), the
library's lower-triangular representatives and block decomposition
(`OrdinaryHeckeCosets.primeRepresentative_matrix`, `OrdinaryBinaryHecke.prime_block`), and the fibre factor `AppendixBResidue.fibre_term_twist` (the representative `(λ 0; u C)` contributes `λ^{e+1}`
times the binary term of `C` with exponent `e`; for the paper's determinant exponent `+1 = -1 + 2`
this is `λ²`).  The new content is the regrouping of the transfer sum:

* `sum_primeLevi_weighted`: `∑_i λ_i^k f(C_i) = p ∑_j f(C^{bin}_j) + p^k f(I)` (the first two families lie
  `p`-fold above each binary coset and have `λ = 1`; the last has `λ = p`, `C = I`);
* `hecke_transfer_residue`: at the level of the underlying functionals, the residue coordinate on the plane
  cone of the exponent-`+1` transfer sum is `p ∑_j (binary term j) + p² (identity)`;
* `hecke_transfer_operator`: the same for the Hom-model operators `T₃ = rationalHecke (diag(p,1,1))` and
  `T₂ = rationalHecke (diag(p,1))`, exponent `+1` on both sides (the elements `F₁`, `F₂` of the
  exponent-`+1` Hom spaces with the same underlying functionals are `AppendixBResidue.twistHom` and
  `twistHomB`; `det = ±1` on the integral groups).

The relation to the library's exponent `-1` statement
`OrdinaryBinaryHeckeComparison.toBinaryHom_prime` is the uniform factor `p²` (`AppendixBResidue.hecke_twist`).

**Scope.** The lifted formula is proved for the determinant-`+1` Hom-model operators named above, and it
is valid for both of them. It is a statement in this exact Hom model. It is NOT identified with the
paper's normalization of the literal analytic Hecke operator: that needs the actual `H₃`-to-Hom
comparison, the transpose and coefficient transport, and the identification of the fixed standard
analytic `T_p`, none of which is proved here. The file therefore neither closes the literal analytic
Hecke formula nor shows a paper error.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.OrdinaryHeckeCosets TernaryPoly.SinglePole TernaryPoly.OrdinaryFullAction
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPoly.OrdinaryResidueSymbol TernaryPoly.OrdinaryResidueParabolic

/-- Weighted regrouping of the sum over the `p² + p + 1` representatives by their binary blocks. -/
theorem sum_primeLevi_weighted {E : Type*} [AddCommGroup E] [Module ℚ E]
    (p : ℕ) [Fact p.Prime] (k : ℕ) (f : BinaryModularSymbol.GL2 → E) :
    (∑ i : OrdinaryHeckeCosets.PrimeIndex p,
        ((OrdinaryBinaryHecke.primeNormalUnit p i : ℚˣ) : ℚ) ^ k • f (OrdinaryBinaryHecke.primeLevi p i)) =
      (p : ℚ) • (∑ j : BinaryRationalHeckePrime.PrimeIndex p,
        f (BinaryRationalHeckePrime.primeRepresentative p j)) + (p : ℚ) ^ k • f 1 := by
  simp [OrdinaryHeckeCosets.PrimeIndex, BinaryRationalHeckePrime.PrimeIndex,
    OrdinaryBinaryHecke.primeLevi, OrdinaryBinaryHecke.primeNormalUnit,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Nat.cast_smul_eq_nsmul, smul_add, add_assoc]

open OrdinaryResidueSymbol OrdinaryResidueParabolic in
/-- **The Hecke transfer in the Hom model (function level).**  With the determinant exponent `+1`
of the paper (`-1 + 2`), the `p² + p + 1` terms of the `diag(1,1,p)` correspondence restrict, in
the residue coordinate on the plane cone, to `p` times the sum of the binary terms plus `p²` times the
identity: `T₃(p,1)|_res = p T₂(p) + p² I`. -/
theorem hecke_transfer_residue (n p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (c : BinaryModularSymbol.St) :
    zeroCoordinate n
        ((∑ i : OrdinaryHeckeCosets.PrimeIndex p,
          OrdinaryHomHecke.linearAction (residueAction n (-1 + 2))
            (OrdinaryHeckeCosets.primeRepresentative p i) F.val) (OrdinaryPlaneEdge.binaryCone c)) =
      (p : ℚ) • (∑ j : BinaryRationalHeckePrime.PrimeIndex p,
        BinaryModularSymbol.homAction
          (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2))
          (BinaryRationalHeckePrime.primeRepresentative p j) (toBinaryHom n F).val c) +
        (p : ℚ) ^ 2 • (BinaryModularSymbol.homAction
          (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)) 1
            (toBinaryHom n F).val c) := by
  rw [LinearMap.sum_apply, map_sum]
  have h := fun i : OrdinaryHeckeCosets.PrimeIndex p =>
    fibre_term_twist n 2 F (OrdinaryHeckeCosets.primeRepresentative p i)
      (OrdinaryBinaryHecke.primeNormalUnit p i) (OrdinaryBinaryHecke.primeShear p i)
      (OrdinaryBinaryHecke.primeLevi p i) (OrdinaryBinaryHecke.prime_block p i) c
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  have := sum_primeLevi_weighted p 2 (fun C => BinaryModularSymbol.homAction
      (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)) C
        (toBinaryHom n F).val c)
  simpa [zpow_ofNat] using this

open RankTwoAugmentedFrames in
theorem binary_integral_det_sq (g : IntegralGL) :
    (((BinaryModularSymbol.integral g).val.det : ℚ)) ^ 2 = 1 := by
  have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit
  have h : (BinaryModularSymbol.integral g).val.det = (g.val.det : ℚ) := by
    change (g.val.map (Int.castRingHom ℚ)).det = _
    exact (RingHom.map_det (Int.castRingHom ℚ) g.val).symm
  rw [h]
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num

open RankTwoAugmentedFrames in
/-- The binary Hom space for the exponent `e` is the binary Hom space for the exponent `e + 2`
(`det = ±1` on `GL₂(ℤ)`). -/
def twistHomB (d : ℕ) (e : ℤ) (f : BinaryModularSymbol.Hom (BinaryModularSymbolCoefficients.homogeneousAction d e)) :
    BinaryModularSymbol.Hom (BinaryModularSymbolCoefficients.homogeneousAction d (e + 2)) :=
  ⟨f.val, by
    intro g c
    rw [homogeneousAction_twist, f.property g c]
    have h2 : (((BinaryModularSymbol.integral g).val.det : ℚ)) ^ (2 : ℤ) = 1 := by
      simpa using binary_integral_det_sq g
    rw [h2, one_smul]⟩

/-- **`T₃(p,1)|_res = p T₂(p) + p² I` for the library's Hom-model Hecke correspondences, in the
paper's normalization (determinant exponent `+1 = -1 + 2` in both the ternary and the binary
coefficient systems).**  `T₃` is `OrdinaryHomHecke.rationalHecke` of `diag(p,1,1)` on
`Hom_G(St, R_n ⊗ det)`, `T₂` is `BinaryRationalHecke.rationalHecke` of `diag(p,1)` on
`Hom_{GL₂(ℤ)}(St₂, Sym^{n+1} ⊗ det)`, and the residue coordinate on the plane cone is
`OrdinaryResidueSymbol.toBinaryHom`.  Here `F₁` and `F₂` are the elements of the exponent-`+1` Hom
spaces with the same underlying functionals as `F` and its residue coordinate (they exist:
`AppendixBResidue.twistHom`, `twistHomB`).  (For exponent `-1` the library has
`OrdinaryBinaryHeckeComparison.toBinaryHom_prime`; the two differ by the uniform scalar `p²`,
`AppendixBResidue.hecke_twist`.) -/
theorem hecke_transfer_operator (n p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (F₁ : OrdinaryFullCoefficient.ResidueHom n (-1 + 2))
    (F₂ : BinaryModularSymbol.Hom
      (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)))
    (h₁ : F₁.val = F.val) (h₂ : F₂.val = (toBinaryHom n F).val) (c : BinaryModularSymbol.St) :
    zeroCoordinate n
        ((OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
          (residueAction n (-1 + 2)) F₁).val (OrdinaryPlaneEdge.binaryCone c)) =
      (p : ℚ) • (BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
          (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)) F₂).val c +
        (p : ℚ) ^ 2 • (toBinaryHom n F).val c := by
  have e1 := OrdinaryBinaryHecke.ternary_rationalHecke_prime p (residueAction n (-1 + 2)) F₁
  have e2 := BinaryRationalHeckePrime.rationalHecke_prime p
    (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)) F₂
  have e3 : BinaryModularSymbol.homAction
      (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)) 1
        (toBinaryHom n F).val c = (toBinaryHom n F).val c := by
    simp
  have h := hecke_transfer_residue n p F c
  rw [e3] at h
  rw [e1, e2, h₁, h₂]
  simp only [LinearMap.sum_apply] at h ⊢
  exact h

theorem mem_lift_ternary (n : ℕ) (e : ℤ) (F : OrdinaryFullCoefficient.ResidueHom n e) :
    F.val ∈ OrdinaryFullCoefficient.ResidueHom n (e + 2) := by
  rw [residueHom_twist_eq]; exact F.property

theorem mem_lift_binary (d : ℕ) (e : ℤ)
    (f : BinaryModularSymbol.Hom (BinaryModularSymbolCoefficients.homogeneousAction d e)) :
    f.val ∈ BinaryModularSymbol.Hom (BinaryModularSymbolCoefficients.homogeneousAction d (e + 2)) := by
  intro g c
  rw [homogeneousAction_twist, f.property g c]
  have h2 : (((BinaryModularSymbol.integral g).val.det : ℚ)) ^ (2 : ℤ) = 1 := by
    simpa using binary_integral_det_sq g
  rw [h2, one_smul]

/-- **`T₃(p,1)|_res = p T₂(p) + p² I` in the Hom model, with the exponent-`+1` lifts constructed.**
The lifts of `F` and of its residue coordinate to the exponent-`+1` Hom spaces are the same functionals
(`mem_lift_ternary`, `mem_lift_binary`: `det = ±1` on the integral groups). -/
theorem hecke_transfer_lifted (n p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (c : BinaryModularSymbol.St) :
    zeroCoordinate n
        ((OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
          (residueAction n (-1 + 2))
          (⟨F.val, mem_lift_ternary n (-1) F⟩ : OrdinaryFullCoefficient.ResidueHom n (-1 + 2))).val
          (OrdinaryPlaneEdge.binaryCone c)) =
      (p : ℚ) • (BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
          (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2))
          (⟨(toBinaryHom n F).val, mem_lift_binary (n + 1) (-1) (toBinaryHom n F)⟩ :
            BinaryModularSymbol.Hom
              (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + 2)))).val c +
        (p : ℚ) ^ 2 • (toBinaryHom n F).val c :=
  hecke_transfer_operator n p F _ _ rfl rfl c

end TernaryPeriodPolynomials.Argument.FiberModel
