module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeHom
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Arithmetic.FiniteIndex
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeTwist

@[expose] public section


/-!
# L6b: `homT` against the Hom Hecke operator of `C1 = diag(1/p,1)`

Formalized by Claude Sonnet 5.5.

For `Φ = F ∘ piL` (`F : PeriodHom d`): `homT p s d Φ E0 = (2/p) • (rationalHecke (C1 p) ρ_{-1} F).val reference`
(`homT_eq`).  Pointwise (`term_eq`): each summand `ρ₀(y C1) Φ(s₁(y⁻¹E₀))` equals `(2/p) · (homAction ρ_{-1} (y C1) F)(reference)`
using `piL E0 = 2 reference`, `piL(s₁ x) = Ψ piL x`, `stD = detQ • action` and `det(y C1) = detQ y / p`.  The index set
`Γ/f(S)` is identified with the library's `RightCosets (intersection Gamma (C1 p))` by `y ↦ y⁻¹` (`cosetEquiv`,
`mem_range_iff`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology

theorem piL_E0 : piL E0 = (2 : ℚ) • reference := by
  change piT.hom (MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ)) = _
  rw [map_sub, piT_single, piT_single, edgeSym_swap, edgeSym_p0]
  module

theorem piL_smul (g : IntegralGL) (x : P1) : piL (P1.ρ g x) = stD g (piL x) :=
  Rep.hom_comm_apply piT g (x : PE)

variable (p : ℕ) [Fact p.Prime]

theorem det_C1 : ((C1 p).val.det : ℚ) = (p : ℚ)⁻¹ := by
  simp [C1, Matrix.det_fin_two]

/-- The summand of `homT`, in Hom form (L6b, pointwise). -/
theorem term_eq (s : DualLift p) (d : ℕ) (F : PeriodHom d) (Φ : P1 →ₗ[ℚ] (Dplain d))
    (hΦ : ∀ x, Φ x = F.val (piL x)) (y0 : IntegralGL) :
    (binMod d).ρ (binIota y0 * C1 p) (Φ (s.s1 (P1.ρ y0⁻¹ E0))) =
      ((2 : ℚ) / p) • (BinaryModularSymbol.homAction
        (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) (binIota y0 * C1 p) F.val reference) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  set β : GL2 := binIota y0 * C1 p with hβ
  have h1 : piL (s.s1 (P1.ρ y0⁻¹ E0)) =
      (2 * detQ y0) • action (β⁻¹) reference := by
    rw [s.symbol, piL_smul, piL_E0, map_smul, stD_apply, map_smul, map_smul, smul_smul, hβ, mul_inv_rev]
    have hd : detQ y0⁻¹ = detQ y0 := by
      rw [map_inv]; exact inv_eq_of_mul_eq_one_right (detQ_mul_self y0)
    rw [hd]
    unfold psi
    rw [map_mul action, Module.End.mul_apply, map_inv BinaryModularSymbol.integral y0]
  have hdet : (β.val.det : ℚ) = detQ y0 * (p : ℚ)⁻¹ := by
    rw [hβ, Units.val_mul, Matrix.det_mul, det_C1, ← det_integral_eq]
  have htw := TernaryPeriodPolynomials.Argument.AppendixBResidue.homogeneousAction_twist d 0 (-1) β
    (F.val (action β⁻¹ reference))
  rw [zero_add] at htw
  have hβ0 : BinaryModularSymbolCoefficients.homogeneousAction d 0 β (F.val (action β⁻¹ reference)) =
      (β.val.det : ℚ) • BinaryModularSymbolCoefficients.homogeneousAction d (-1) β
        (F.val (action β⁻¹ reference)) := by
    rw [htw, smul_smul, zpow_neg_one, mul_inv_cancel₀, one_smul]
    rw [hdet]
    exact mul_ne_zero (by
      intro h
      have := detQ_mul_self y0
      rw [h] at this; simp at this) (inv_ne_zero hp)
  change BinaryModularSymbolCoefficients.homogeneousAction d 0 β _ = _
  rw [hΦ, h1, map_smul, map_smul, hβ0, smul_smul, BinaryModularSymbol.homAction_apply, hdet]
  congr 1
  have := detQ_mul_self y0
  field_simp
  linear_combination this

section Cosets

open TernaryPoly.BinaryRationalHeckeArithmetic TernaryPoly.OrdinaryHeckeTransfer
open TernaryPoly.RationalCohomologyDescent

theorem mem_range_iff (k : IntegralGL) :
    k ∈ (binDatum p).f.range ↔ integralEquiv k ∈ intersection Gamma (C1 p) := by
  rw [mem_intersection]
  constructor
  · rintro ⟨s, rfl⟩
    have h := (binDatum p).hf s
    refine ⟨s.1, ?_⟩
    change binIota s.1 = (C1 p)⁻¹ * binIota ((binDatum p).f s) * (C1 p)
    rw [h]; group
  · rintro ⟨s', hs'⟩
    have hk : binIota k = C1 p * binIota s' * (C1 p)⁻¹ := by
      have : binIota s' = (C1 p)⁻¹ * binIota k * (C1 p) := hs'
      rw [this]; group
    have hmem : s' ∈ commSubgroup binIota (C1 p) := ⟨k, hk⟩
    refine ⟨⟨s', hmem⟩, ?_⟩
    apply binIota_injective
    rw [(binDatum p).hf ⟨s', hmem⟩, hk]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- `Γ/f(S) ≃ (Γ ∩ C1 Γ C1⁻¹)\Γ` by `y ↦ y⁻¹`. -/
def cosetEquiv : (IntegralGL ⧸ (binDatum p).f.range) ≃ RightCosets (intersection Gamma (C1 p)) :=
  Equiv.ofBijective
    (Quotient.map' (fun y : IntegralGL => (integralEquiv y)⁻¹) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      rw [QuotientGroup.rightRel_apply]
      have := (mem_range_iff p _).mp (Subgroup.inv_mem _ hab)
      simpa [map_mul] using this))
    ⟨fun a b => by
      refine Quotient.inductionOn₂' a b (fun a b hab => ?_)
      have hab' := Quotient.exact' hab
      rw [QuotientGroup.rightRel_apply] at hab'
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      have := (mem_range_iff p ((a⁻¹ * b)⁻¹)).mpr (by simpa [map_mul] using hab')
      simpa using Subgroup.inv_mem _ this,
     fun q => by
      refine Quotient.inductionOn' q (fun a => ?_)
      refine ⟨Quotient.mk'' ((integralEquiv.symm a)⁻¹), ?_⟩
      change Quotient.mk'' ((integralEquiv ((integralEquiv.symm a)⁻¹))⁻¹) = _
      simp⟩

open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeHom in
/-- **L6b.** `homT` in terms of the Hom Hecke operator of `C1 p` (exponent `-1`). -/
theorem homT_eq (s : DualLift p) (d : ℕ) (F : PeriodHom d) (Φ : P1 →ₗ[ℚ] (Dplain d))
    (hΦ : ∀ x, Φ x = F.val (piL x)) :
    homT p s d Φ E0 = ((2 : ℚ) / p) •
      ((BinaryRationalHecke.rationalHecke (C1 p)
        (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) F).val reference) := by
  let := intersection_finiteIndex (C1 p)
  unfold homT
  have hterm : ∀ y : IntegralGL ⧸ (binDatum p).f.range,
      (binMod d).ρ (binIota (Quotient.out y) * C1 p) (Φ (s.s1 (P1.ρ (Quotient.out y)⁻¹ E0))) =
        ((2 : ℚ) / p) • (BinaryModularSymbol.homAction
          (BinaryModularSymbolCoefficients.homogeneousAction d (-1))
          ((((cosetEquiv p y).out : Gamma) : GL2)⁻¹ * C1 p) F.val reference) := by
    intro y
    rw [term_eq p s d F Φ hΦ]
    have hq : cosetEquiv p y = Quotient.mk _ ((integralEquiv (Quotient.out y))⁻¹) := by
      conv_lhs => rw [← Quotient.out_eq' y]
      rfl
    have h2 := Quotient.exact ((Quotient.out_eq (cosetEquiv p y)).trans hq)
    have h3 : (integralEquiv (Quotient.out y))⁻¹ * ((cosetEquiv p y).out)⁻¹ ∈ intersection Gamma (C1 p) :=
      (QuotientGroup.rightRel_apply (s := intersection Gamma (C1 p))).mp h2
    have h4 : tau (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) (C1 p) F.val
        ((cosetEquiv p y).out) =
        tau (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) (C1 p) F.val
          ((integralEquiv (Quotient.out y))⁻¹) := by
      have hh : (cosetEquiv p y).out =
          ((integralEquiv (Quotient.out y))⁻¹ * ((cosetEquiv p y).out)⁻¹)⁻¹ * (integralEquiv (Quotient.out y))⁻¹ := by
        group
      rw [hh]
      exact tau_inv _ (C1 p) F ⟨_, inv_mem h3⟩ _
    have h5 : BinaryModularSymbol.homAction (BinaryModularSymbolCoefficients.homogeneousAction d (-1))
        (binIota (Quotient.out y) * C1 p) F.val =
        BinaryModularSymbol.homAction (BinaryModularSymbolCoefficients.homogeneousAction d (-1))
          ((((cosetEquiv p y).out : Gamma) : GL2)⁻¹ * C1 p) F.val := by
      have := congrArg (fun x => x) h4.symm
      simpa [tau] using this
    rw [h5]
  refine (finsum_congr hterm).trans ?_
  refine (finsum_comp_equiv (cosetEquiv p)
    (f := fun q : RightCosets (intersection Gamma (C1 p)) => ((2 : ℚ) / p) •
      (BinaryModularSymbol.homAction (BinaryModularSymbolCoefficients.homogeneousAction d (-1))
        ((q.out : Gamma).val⁻¹ * C1 p) F.val reference))).trans ?_
  rw [finsum_eq_sum_of_fintype, BinaryRationalHecke.rationalHecke_apply]
  simp only [LinearMap.sum_apply, Finset.smul_sum]

end Cosets

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
