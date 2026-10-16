module

public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.CocycleConstruction

@[expose] public section


/-!
# Corollary 1.4, Step 3: additivity and homogeneity of `periodCocycle` in `P`

`periodCocycle`'s value is `-P` at both generators `S` and `U = ST` (`periodCocycle_S`,
`periodCocycle_U`), so `cocycle_ext` (`ModularH1.lean`, a 1-cocycle of `SL₂(ℤ)` is determined by
its values on `S` and `U`) makes `periodCocycle` additive (`periodCocycle_add`) and homogeneous
(`periodCocycle_smul`) in `P`: both sides agree at `S` and at `U` because `-` and `•` on
`HomogeneousPoly n` distribute over themselves there, so the two generator-value equalities
collapse to `neg_add`/`smul_neg`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Corollary14

open Matrix Matrix.SpecialLinearGroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1
open GeneralEisenstein.Binary (HomogeneousPoly Poly)
open TernaryPoly.Paper (PeriodRelations)

variable {n : ℕ} (twist : ℤ)

/-- **Additivity of `periodCocycle` in `P`.** -/
theorem periodCocycle_add (hn : Even n) {P Q : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly)) (hQ : PeriodRelations (Q : Poly))
    (hPQ : PeriodRelations ((P + Q : HomogeneousPoly n) : Poly)) :
    periodCocycle twist hn hPQ = periodCocycle twist hn hP + periodCocycle twist hn hQ := by
  apply cocycle_ext (modularBinaryRep n twist)
  · show periodCocycle twist hn hPQ ModularGroup.S =
      (periodCocycle twist hn hP + periodCocycle twist hn hQ) ModularGroup.S
    have e1 : (periodCocycle twist hn hP + periodCocycle twist hn hQ) ModularGroup.S =
        periodCocycle twist hn hP ModularGroup.S + periodCocycle twist hn hQ ModularGroup.S := rfl
    rw [e1, periodCocycle_S, periodCocycle_S, periodCocycle_S]
    abel
  · show periodCocycle twist hn hPQ modularOrderSix =
      (periodCocycle twist hn hP + periodCocycle twist hn hQ) modularOrderSix
    have e1 : (periodCocycle twist hn hP + periodCocycle twist hn hQ) modularOrderSix =
        periodCocycle twist hn hP modularOrderSix + periodCocycle twist hn hQ modularOrderSix :=
      rfl
    rw [e1, periodCocycle_U, periodCocycle_U, periodCocycle_U]
    abel

/-- **Homogeneity of `periodCocycle` in `P`.** -/
theorem periodCocycle_smul (hn : Even n) (c : ℂ) {P : HomogeneousPoly n}
    (hP : PeriodRelations (P : Poly))
    (hcP : PeriodRelations ((c • P : HomogeneousPoly n) : Poly)) :
    periodCocycle twist hn hcP = c • periodCocycle twist hn hP := by
  apply cocycle_ext (modularBinaryRep n twist)
  · show periodCocycle twist hn hcP ModularGroup.S = (c • periodCocycle twist hn hP) ModularGroup.S
    have e1 : (c • periodCocycle twist hn hP) ModularGroup.S =
        c • (periodCocycle twist hn hP ModularGroup.S) := rfl
    rw [e1, periodCocycle_S, periodCocycle_S]
    exact (smul_neg c P).symm
  · show periodCocycle twist hn hcP modularOrderSix =
      (c • periodCocycle twist hn hP) modularOrderSix
    have e1 : (c • periodCocycle twist hn hP) modularOrderSix =
        c • (periodCocycle twist hn hP modularOrderSix) := rfl
    rw [e1, periodCocycle_U, periodCocycle_U]
    exact (smul_neg c P).symm

end TernaryPeriodPolynomials.Argument.Corollary14
