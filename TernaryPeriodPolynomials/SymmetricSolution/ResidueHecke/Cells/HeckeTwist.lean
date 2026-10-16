module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeResidue
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BinaryHeckeTerm
public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Basic
public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodRationalComparison

@[expose] public section


/-!
# Lemma B.1: the determinant twist of the Hecke computation

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.3,
"The Hecke transfer" and `eq:Hecke-formula`.

The library's residue module `Residues n` carries a family of rational actions
`residueAction n e` (`e` the exponent of the determinant twist).  Two integral-group Hom spaces
with exponents differing by two coincide (`det = ±1` on `GL₃(ℤ)`), but the rational Hecke
operators do not.  This file computes the dependence on `e`:

* `residueAction_twist`: `residueAction n (e + k) g = det(g)^k • residueAction n e g`;
* `fibre_term_twist`: the fibre contribution on the plane cone of a representative
  `g = (λ 0; u C)` is `λ^{e+1} • (binary term of C with exponent e)`.  For `e = 1` this is the
  paper's factor `λ²` (with `det C` absorbed in the binary exponent);
* `hecke_twist`: the prime Hecke operator for the exponent `e + 2` is `p²` times the one for `e`
  (every coset representative of `diag(1,1,p)` has determinant `p`);
* `resH_hecke_cusp`: in the exponent `-1` normalization, if the residue coordinate of `F` is the
  period of a cusp form `f` of weight `d + 2`, `d = n + 1`, then
  `p^d · res_H(T₃(p,1) F) = periodMap (T_p f) + p^d · periodMap f`, with `T_p` the analytic Hecke
  operator.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.SinglePole TernaryPoly.OrdinaryFullAction
open TernaryPoly.PolynomialGLAction (determinantCharacter)

theorem singlePoleAction_twist (n : ℕ) (e k : ℤ) (g : GL3) (x : singlePole n) :
    singlePoleAction n (e + k) g x = determinantCharacter k g • singlePoleAction n e g x := by
  apply Subtype.ext
  simp only [singlePoleAction_val, fractionAction_apply, Submodule.coe_smul, smul_smul]
  congr 1
  simp only [determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [zpow_add₀ (Units.ne_zero _), mul_comm]

theorem residueAction_twist (n : ℕ) (e k : ℤ) (g : GL3) (r : Residues n) :
    residueAction n (e + k) g r = determinantCharacter k g • residueAction n e g r := by
  obtain ⟨x, rfl⟩ := residue_surjective n r
  rw [residue_equivariant, residue_equivariant, singlePoleAction_twist, map_smul]

theorem determinantCharacter_apply (k : ℤ) (g : GL3) :
    determinantCharacter k g = ((g.val.det : ℚ)) ^ k := by
  simp [determinantCharacter, Matrix.GeneralLinearGroup.val_det_apply]

theorem det_integral_sq (g : ModThreeGoodAction.IntegralGL) : determinantCharacter 2 (integral g) = 1 := by
  rw [determinantCharacter_apply]
  have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit
  have h : (integral g).val.det = (g.val.det : ℚ) := by
    change (g.val.map (Int.castRingHom ℚ)).det = _
    exact (RingHom.map_det (Int.castRingHom ℚ) g.val).symm
  rw [h]
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num

/-- The integral-group Hom spaces for exponents differing by two coincide. -/
theorem residueHom_twist_eq (n : ℕ) (e : ℤ) :
    OrdinaryFullCoefficient.ResidueHom n (e + 2) = OrdinaryFullCoefficient.ResidueHom n e := by
  ext f
  change (∀ g : ModThreeGoodAction.IntegralGL, ∀ c, f (cycleAction (integral g) c) = residueAction n (e + 2) (integral g) (f c)) ↔
    (∀ g : ModThreeGoodAction.IntegralGL, ∀ c, f (cycleAction (integral g) c) = residueAction n e (integral g) (f c))
  simp only [residueAction_twist, det_integral_sq, one_smul]

theorem det_primeRepresentative (p : ℕ) [Fact p.Prime] (i : OrdinaryHeckeCosets.PrimeIndex p) :
    determinantCharacter 2 (OrdinaryHeckeCosets.primeRepresentative p i) = (p : ℚ) ^ 2 := by
  rw [determinantCharacter_apply]
  rcases i with ⟨b, c⟩ | a | u <;>
    simp [OrdinaryHeckeCosets.primeRepresentative_matrix, Matrix.det_fin_three]

/-- The `ResidueHom n e` functional viewed in `ResidueHom n (e + 2)` (same integral equivariance). -/
def twistHom (n : ℕ) (e : ℤ) (F : OrdinaryFullCoefficient.ResidueHom n e) :
    OrdinaryFullCoefficient.ResidueHom n (e + 2) :=
  ⟨F.val, by rw [residueHom_twist_eq]; exact F.property⟩

/-- **Uniform `p²`.**  The prime Hecke operator with the determinant exponent raised by two is
`p²` times the original one (every representative of `diag(p,1,1)` has determinant `p`). -/
theorem hecke_twist (n : ℕ) (e : ℤ) (p : ℕ) [Fact p.Prime]
    (F : OrdinaryFullCoefficient.ResidueHom n e) :
    (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
        (residueAction n (e + 2)) (twistHom n e F)).val =
      (p : ℚ) ^ 2 • (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
        (residueAction n e) F).val := by
  rw [OrdinaryBinaryHecke.ternary_rationalHecke_prime, OrdinaryBinaryHecke.ternary_rationalHecke_prime,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply LinearMap.ext
  intro c
  simp only [OrdinaryHomHecke.linearAction_apply, LinearMap.smul_apply, twistHom]
  rw [residueAction_twist, det_primeRepresentative]

theorem homogeneousAction_twist (d : ℕ) (e k : ℤ) (C : BinaryModularSymbol.GL2)
    (q : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    BinaryModularSymbolCoefficients.homogeneousAction d (e + k) C q =
      ((C.val.det : ℚ) ^ k) • BinaryModularSymbolCoefficients.homogeneousAction d e C q := by
  apply Subtype.ext
  simp only [BinaryModularSymbolCoefficients.homogeneousAction_coe,
    BinaryModularSymbolCoefficients.action_apply, Submodule.coe_smul, smul_smul]
  congr 1
  simp only [BinaryModularSymbolCoefficients.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [zpow_add₀ (by simpa using C.det.ne_zero), mul_comm]

theorem det_block (lam : ℚˣ) (u : Fin 2 → ℚ) (C : OrdinaryResidueParabolic.GL2) :
    (OrdinaryResidueParabolic.blockMatrix lam u C).det = (lam : ℚ) * C.val.det := by
  rw [blockMatrix_eq]
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-- **The fibre factor `λ^{e+1}`.**  For the exponent `e = -1 + k`, the contribution of the
representative `g = (λ 0; u C)` to the residue coordinate on the plane cone is `λ^k` times the
binary term of `C` for the same exponent.  For `e = 1` (`k = 2`) this is the paper's `λ²`. -/
theorem fibre_term_twist (n : ℕ) (k : ℤ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : BinaryModularSymbol.GL2)
    (hg : g.val = OrdinaryResidueParabolic.blockMatrix lam u C) (c : BinaryModularSymbol.St) :
    OrdinaryResidueParabolic.zeroCoordinate n
        (OrdinaryHomHecke.linearAction (residueAction n (-1 + k)) g F.val
          (OrdinaryPlaneEdge.binaryCone c)) =
      (lam : ℚ) ^ k • BinaryModularSymbol.homAction
        (BinaryModularSymbolCoefficients.homogeneousAction (n + 1) (-1 + k)) C
        (OrdinaryResidueSymbol.toBinaryHom n F).val c := by
  have hdet : determinantCharacter k g = (lam : ℚ) ^ k * (C.val.det : ℚ) ^ k := by
    rw [determinantCharacter_apply, hg, det_block, mul_zpow]
  rw [OrdinaryHomHecke.linearAction_apply, residueAction_twist, map_smul, hdet,
    ← OrdinaryHomHecke.linearAction_apply, OrdinaryBinaryHecke.parabolic_term n F g lam u C hg c,
    BinaryModularSymbol.homAction_apply, BinaryModularSymbol.homAction_apply,
    homogeneousAction_twist, smul_smul]

theorem extend_add (d : ℕ) (q r : BinaryComplexPeriod.space ℚ d) :
    BinaryComplexPeriod.extend (algebraMap ℚ ℂ) d (q + r) =
      BinaryComplexPeriod.extend (algebraMap ℚ ℂ) d q +
        BinaryComplexPeriod.extend (algebraMap ℚ ℂ) d r :=
  Subtype.ext (map_add _ _ _)

theorem extend_nat_smul (d p : ℕ) (q : BinaryComplexPeriod.space ℚ d) :
    BinaryComplexPeriod.extend (algebraMap ℚ ℂ) d ((p : ℚ) • q) =
      (p : ℂ) • BinaryComplexPeriod.extend (algebraMap ℚ ℂ) d q := by
  apply Subtype.ext
  change MvPolynomial.map (algebraMap ℚ ℂ) ((p : ℚ) • q.val) = (p : ℂ) • MvPolynomial.map (algebraMap ℚ ℂ) q.val
  rw [Nat.cast_smul_eq_nsmul ℚ, Nat.cast_smul_eq_nsmul ℂ, map_nsmul]

/-- **The Hom-model Hecke shape on cusp periods.**  In the exponent `-1` normalization, if the
residue coordinate of `F` is the period `periodMap f` of a cusp form of weight `d + 2` (`d = n + 1`),
then the residue coordinate of `T₃(p,1)F` satisfies
`p^d · res_H(T₃ F) = periodMap (T_p f) + p^d · periodMap f`,
with `T_p` the analytic Hecke operator: the Hom-model operator is `T_p + p^d`, up to the scalar
`p^{-d}`, and not `p T_p + p²`. -/
theorem resH_hecke_cusp (n p : ℕ) [Fact p.Prime] (hd : Even (n + 1))
    (F : OrdinaryFullCoefficient.ResidueHom n (-1)) (f : BinaryCuspPeriod.Forms (n + 1))
    (h : BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n F) = BinaryCuspPeriod.periodMap (n + 1) hd f) :
    (p : ℂ) ^ (n + 1) • BinaryComplexPeriod.extend (algebraMap ℚ ℂ) (n + 1)
        (BinaryComplexPeriod.actualPeriodEquiv n
          (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
            (residueAction n (-1)) F)) =
      BinaryCuspPeriod.periodMap (n + 1) hd (BinaryCuspHeckeEndomorphism.T (n + 1) p f) +
        (p : ℂ) ^ (n + 1) • BinaryCuspPeriod.periodMap (n + 1) hd f := by
  have h1 := congrArg (BinaryComplexPeriod.rationalEquiv (n + 1)) (resH_hecke_prime n p F)
  have e1 : BinaryComplexPeriod.actualPeriodEquiv n
        (OrdinaryHomHecke.rationalHecke (OrdinaryHeckeCosets.primeDiagonal p)
          (residueAction n (-1)) F) =
      (p : ℚ) • BinaryComplexPeriod.rationalSymbolHecke (n + 1)
          (BinaryRationalHeckePrime.primeDiagonal p) (BinaryComplexPeriod.actualPeriodEquiv n F) +
        BinaryComplexPeriod.actualPeriodEquiv n F := by
    simpa [BinaryComplexPeriod.actualPeriodEquiv, BinaryComplexPeriod.rationalSymbolHecke,
      resH_eq_periodEquiv] using h1
  rw [e1, extend_add, extend_nat_smul, ← BinaryComplexPeriod.complexHecke_extend, h,
    BinaryCuspPeriod.periodMap_hecke hd f p, smul_add, smul_smul, pow_succ (p : ℂ) (n + 1)]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
