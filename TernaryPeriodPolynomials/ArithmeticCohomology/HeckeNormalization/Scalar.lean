module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.AnalyticHecke
public import TernaryPeriodPolynomials.ModularForm.PeriodDetection.Basic
public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResidueDetectionActual

@[expose] public section


/-!
# The exponent-`+1` Hom-model prime correspondence against the standard `T_p` on periods

Formalized by Claude Sonnet 5.5.

**Scope.**  Everything here is about the library's *Hom model*:
`BinaryRationalHecke.rationalHecke (primeDiagonal p) (homogeneousAction d e)` on
`Hom_{GL₂(ℤ)}(St₂, Sym^d ⊗ det^e)`, with `ρ_e(g) q = det(g)^e q(g⁻¹ ·)`, in the exponent `e = +1 = -1 + 2`
that `FiberModel.HeckeHom.hecke_transfer_operator` uses to reproduce the identity coefficient `p²` of
`eq:Hecke-formula`.  It is **not** identified with the paper's homology operator
`T₂(p)` (the one of the `heckeOp (binDatum p)`, built from the printed conventions `q ↦ det(C) q(C(b,c))`): that comparison is not addressed and nothing below is a statement about the paper's operator.

Paper: "It remains to check
that this binary correspondence has the standard analytic Hecke normalization on period polynomials. ... The
homological correspondence above is the standard Hecke operator on the period polynomial of `h`."

What is proved, for every level-one cusp form `f` of weight `d + 2` and every prime `p`, unconditionally
(no hypothesis of the form `κ(Sh F) = φ_f`):

* `homPlusRationalHecke`, `homPlusComplexHecke`: the exponent-`+1` Hom-model correspondence transported to the
  rational and complex period spaces (`homPlusRationalHecke_spec` identifies it with
  `rationalHecke (primeDiagonal p) (homogeneousAction d (-1+2))`);
* `homPlusComplexHecke_eq`: it is `p²` times the exponent-`-1` operator `complexHecke`;
* `periodMap_homPlus`: `p² • periodMap (T_p f) = p^{d+1} • homPlusComplexHecke p (periodMap f)`, i.e.
  `homPlus_periodMap_zpow`: `homPlusComplexHecke p ∘ periodMap = p^{1-d} • periodMap ∘ T_p`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.BinaryComplexPeriod
open TernaryPoly.BinaryModularSymbolCoefficients (homogeneousAction)
open TernaryPoly.BinaryCuspPeriod TernaryPoly.BinaryCuspPeriodDetection
open TernaryPeriodPolynomials.Argument.FiberModel

/-- The exponent-`+1` Hom-model prime correspondence in the rational period coordinates of
`BinaryComplexPeriod.space ℚ d`.  It is `p²` times the exponent-`-1` operator of the library
(`AnalyticHecke.binary_hecke_twist`: every representative of `diag(p,1)` has determinant `p`); that this is
the exponent-`+1` Hom-model correspondence `rationalHecke (primeDiagonal p) (homogeneousAction d (-1+2))`
is `homPlusRationalHecke_spec`. -/
def homPlusRationalHecke (d p : ℕ) [Fact p.Prime] : Module.End ℚ (space ℚ d) :=
  (p : ℚ) ^ 2 • rationalSymbolHecke d (BinaryRationalHeckePrime.primeDiagonal p)

/-- **`homPlusRationalHecke` is the exponent-`+1` Hom-model correspondence.**  For a period symbol `G`
(regarded in the exponent-`+1` Hom space, `mem_lift_binary`), the value at the reference edge of
`rationalHecke (diag(p,1)) (homogeneousAction d (-1 + 2)) G` is the period `homPlusRationalHecke d p` of the
period of `G`. -/
theorem homPlusRationalHecke_spec (d p : ℕ) [Fact p.Prime] (G : PeriodHom d) :
    ((homPlusRationalHecke d p (rationalEquiv d (periodEquiv d G)) : space ℚ d) :
        MvPolynomial (Fin 2) ℚ) =
      (((BinaryRationalHecke.rationalHecke (BinaryRationalHeckePrime.primeDiagonal p)
        (homogeneousAction d (-1 + 2)) ⟨G.val, mem_lift_binary d (-1) G⟩).val reference :
          BinaryModularSymbolCoefficients.HomogeneousPoly d) : MvPolynomial (Fin 2) ℚ) := by
  rw [AnalyticHecke.binary_hecke_twist d p (-1) G]
  simp [homPlusRationalHecke, rationalSymbolHecke, BinaryRationalHecke.periodHecke]
  rfl

/-- The exponent-`+1` Hom-model prime correspondence, complexified to the full complex period space. -/
def homPlusComplexHecke (d p : ℕ) [Fact p.Prime] : Module.End ℂ (space ℂ d) :=
  complexifyEnd d (homPlusRationalHecke d p)

/-- `homPlusComplexHecke p = p² · complexHecke p` (the library's exponent-`-1` operator). -/
theorem homPlusComplexHecke_eq (d p : ℕ) [Fact p.Prime] :
    homPlusComplexHecke d p =
      (p : ℂ) ^ 2 • complexHecke d (BinaryRationalHeckePrime.primeDiagonal p) := by
  apply end_ext_on_rational
  intro q
  have h1 : homPlusComplexHecke d p (extend (algebraMap ℚ ℂ) d q) =
      extend (algebraMap ℚ ℂ) d (homPlusRationalHecke d p q) :=
    complexifyEnd_extend d _ q
  rw [h1, homPlusRationalHecke, LinearMap.smul_apply, LinearMap.smul_apply,
    complexHecke_extend]
  have h2 := TernaryPeriodPolynomials.Argument.AppendixBResidue.extend_nat_smul d (p ^ 2)
    (rationalSymbolHecke d (BinaryRationalHeckePrime.primeDiagonal p) q)
  push_cast at h2
  exact h2

/-- **The exact scalar, unconditionally.**  For every level-one cusp form `f` of weight `d + 2` and
every prime `p`: `p² • periodMap (T_p f) = p^{d+1} • T₂(p) (periodMap f)`, with `T₂(p)` the
exponent-`+1` Hom-model correspondence and `T_p` the standard analytic Hecke operator. -/
theorem periodMap_homPlus {d : ℕ} (hd : Even d) (f : Forms d) (p : ℕ) [Fact p.Prime] :
    (p : ℂ) ^ 2 • periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) =
      (p : ℂ) ^ (d + 1) • homPlusComplexHecke d p (periodMap d hd f) := by
  rw [periodMap_hecke hd f p, homPlusComplexHecke_eq, LinearMap.smul_apply, smul_smul, smul_smul,
    mul_comm]

/-- `T₂(p) ∘ periodMap = p^{1-d} · periodMap ∘ T_p`: the exponent-`+1` Hom-model correspondence is the
standard Hecke operator multiplied by the explicit scalar `p^{1-d}`. -/
theorem homPlus_periodMap_zpow {d : ℕ} (hd : Even d) (f : Forms d) (p : ℕ) [Fact p.Prime] :
    homPlusComplexHecke d p (periodMap d hd f) =
      (p : ℂ) ^ ((1 : ℤ) - d) • periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h := congrArg (fun v => (p : ℂ) ^ (-((d : ℤ) + 1)) • v) (periodMap_homPlus hd f p)
  simp only [smul_smul] at h
  have h3 : (p : ℂ) ^ (-((d : ℤ) + 1)) * (p : ℂ) ^ (d + 1) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hp]
    push_cast
    simp
  have h4 : (p : ℂ) ^ (-((d : ℤ) + 1)) * (p : ℂ) ^ 2 = (p : ℂ) ^ ((1 : ℤ) - d) := by
    rw [← zpow_natCast, ← zpow_add₀ hp]
    congr 1
    push_cast
    ring
  rw [h3, h4, one_smul] at h
  exact h.symm

end TernaryPeriodPolynomials.Argument.HeckeNormalization
