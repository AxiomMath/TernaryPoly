module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Formula
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Representatives
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Arithmetic.FiniteIndex
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.AssemblyConventions
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.HeckeTwist

@[expose] public section


/-!
# L6c: the Hom Hecke operator of `C1 = diag(1/p,1)` against that of `diag(p,1)`

Formalized by Claude Sonnet 5.5.

`hecke_central_conj`: `rationalHecke (z γ g₂ γ') = ρ(z) rationalHecke g₂` for central `z` and `γ, γ' ∈ Γ`; applied to
`C1 p = zS * w * diag(p,1) * w` (`C1_decomp`), with `ρ_{-1}(zS) = p^(d+2)` (`rho_zS`) and the trivial action of scalar matrices
on `St` (`action_zS_inv`): `hecke_C1_neg : T[C1] F = p^(d+2) • T[diag(p,1)] F` for the exponent `-1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeHom

open TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.BinaryRationalHecke
open TernaryPoly.BinaryRationalHeckeArithmetic TernaryPoly.OrdinaryHeckeTransfer
open TernaryPoly.RationalCohomologyDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (ρ : Representation ℚ GL2 E)

theorem fixed_of_mem (F : Hom ρ) (γ : Gamma) : homAction ρ γ.val F.val = F.val :=
  (mem_hom_iff_fixed ρ F.val).mp F.property γ

/-- The summand of the Hecke sum. -/
def tau (g : GL2) (F : St →ₗ[ℚ] E) (x : Gamma) : St →ₗ[ℚ] E := homAction ρ (x.val⁻¹ * g) F

theorem tau_inv (g : GL2) (F : Hom ρ) (h : intersection Gamma g) (x : Gamma) :
    tau ρ g F.val ((h : Gamma) * x) = tau ρ g F.val x := by
  have hm : g⁻¹ * (((h : Gamma)⁻¹ : Gamma) : GL2) * g ∈ Gamma := by
    have := (mem_intersection Gamma g (h⁻¹)).mp (inv_mem h.2 |> fun t => t)
    simpa using this
  have key : (((h : Gamma) * x : Gamma) : GL2)⁻¹ * g = x.val⁻¹ * g * (g⁻¹ * (((h : Gamma)⁻¹ : Gamma) : GL2) * g) := by
    simp [mul_assoc]
  unfold tau
  rw [key, map_mul, Module.End.mul_apply]
  have := fixed_of_mem ρ F ⟨_, hm⟩
  rw [this]

theorem hecke_central_conj (g g2 z : GL2) (hz : ∀ a : GL2, z * a = a * z) (γ γ' : Gamma)
    (hg : g = z * γ.val * g2 * γ'.val) (F : Hom ρ) :
    (rationalHecke g ρ F).val = homAction ρ z (rationalHecke g2 ρ F).val := by
  let := intersection_finiteIndex g
  let := intersection_finiteIndex g2
  have hzc : ∀ X : GL2, z⁻¹ * X * z = X := by
    intro X
    have := hz X
    calc z⁻¹ * X * z = z⁻¹ * (X * z) := by rw [mul_assoc]
      _ = z⁻¹ * (z * X) := by rw [← hz X]
      _ = X := by rw [inv_mul_cancel_left]
  have hmem : ∀ k : Gamma, k ∈ intersection Gamma g2 ↔ γ * k * γ⁻¹ ∈ intersection Gamma g := by
    intro k
    rw [mem_intersection, mem_intersection]
    have e : g⁻¹ * ((γ * k * γ⁻¹ : Gamma) : GL2) * g = γ'.val⁻¹ * (g2⁻¹ * k.val * g2) * γ'.val := by
      calc g⁻¹ * ((γ * k * γ⁻¹ : Gamma) : GL2) * g
          = γ'.val⁻¹ * g2⁻¹ * γ.val⁻¹ * (z⁻¹ * (γ.val * k.val * γ.val⁻¹) * z) * γ.val * g2 * γ'.val := by
            rw [hg]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = γ'.val⁻¹ * g2⁻¹ * γ.val⁻¹ * (γ.val * k.val * γ.val⁻¹) * γ.val * g2 * γ'.val := by rw [hzc]
        _ = _ := by group
    rw [e]
    constructor
    · intro h
      exact Gamma.mul_mem (Gamma.mul_mem (Gamma.inv_mem γ'.2) h) γ'.2
    · intro h
      have := Gamma.mul_mem (Gamma.mul_mem γ'.2 h) (Gamma.inv_mem γ'.2)
      simpa [mul_assoc] using this
  let e : RightCosets (intersection Gamma g2) ≃ RightCosets (intersection Gamma g) :=
    Quotient.congr (Equiv.mulLeft γ) (fun a b => by
      rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
      change b * a⁻¹ ∈ _ ↔ (γ * b) * (γ * a)⁻¹ ∈ _
      rw [hmem (b * a⁻¹)]
      simp [mul_assoc])
  rw [rationalHecke_apply, rationalHecke_apply, map_sum]
  refine (Fintype.sum_equiv e (fun q' => homAction ρ z (homAction ρ (q'.out.val⁻¹ * g2) F.val))
    (fun q => homAction ρ (q.out.val⁻¹ * g) F.val) (fun q' => ?_)).symm
  have hq : e q' = Quotient.mk _ (γ * q'.out) := by
    conv_lhs => rw [← Quotient.out_eq q']
    rfl
  have h2 := Quotient.exact ((Quotient.out_eq (e q')).trans hq)
  have h3 : γ * q'.out * ((e q').out)⁻¹ ∈ intersection Gamma g := by
    have := (QuotientGroup.rightRel_apply (s := intersection Gamma g)).mp h2
    exact this
  have h4 : tau ρ g F.val (e q').out = tau ρ g F.val (γ * q'.out) := by
    have hh : (e q').out = (γ * q'.out * ((e q').out)⁻¹)⁻¹ * (γ * q'.out) := by group
    rw [hh]
    exact tau_inv ρ g F ⟨_, inv_mem h3⟩ (γ * q'.out)
  change homAction ρ z (homAction ρ (q'.out.val⁻¹ * g2) F.val) = tau ρ g F.val (e q').out
  rw [h4]
  unfold tau
  have e2 : ((γ * q'.out : Gamma) : GL2)⁻¹ * g = z * (q'.out.val⁻¹ * g2) * γ'.val := by
    rw [hg]; simp only [Subgroup.coe_mul]
    have hzq : q'.out.val⁻¹ * z = z * q'.out.val⁻¹ := (hz _).symm
    calc (γ.val * q'.out.val)⁻¹ * (z * γ.val * g2 * γ'.val)
        = q'.out.val⁻¹ * γ.val⁻¹ * (z * γ.val) * g2 * γ'.val := by group
      _ = q'.out.val⁻¹ * γ.val⁻¹ * (γ.val * z) * g2 * γ'.val := by rw [hz γ.val]
      _ = q'.out.val⁻¹ * z * g2 * γ'.val := by group
      _ = z * q'.out.val⁻¹ * g2 * γ'.val := by rw [hzq]
      _ = _ := by group
  rw [e2]
  simp only [map_mul, Module.End.mul_apply, fixed_of_mem ρ F γ']

open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.FareyTree
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryRationalHeckePrime in
theorem integral_wSwap_val :
    (BinaryModularSymbol.integral wSwap).val = !![(0 : ℚ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryModularSymbol.integral, Matrix.GeneralLinearGroup.map, wSwap, colGL_val_zero, colGL_val_one, e1, e2]

open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.FareyTree
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryRationalHeckePrime in
theorem C1_decomp (p : ℕ) [Fact p.Prime] :
    C1 p = zS p * BinaryModularSymbol.integral wSwap * primeDiagonal p * BinaryModularSymbol.integral wSwap := by
  have hp := p_ne_zero_rat p
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C1, zS, primeDiagonal, integral_wSwap_val, Matrix.mul_apply, Fin.sum_univ_two, hp]

open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.FareyTree
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryRationalHeckePrime in
/-- **L6c.** The Hom Hecke operator of `C1 = diag(1/p,1)` is `ρ(zS)` times that of `diag(p,1)`. -/
theorem hecke_C1 (p : ℕ) [Fact p.Prime] (F : Hom ρ) :
    (rationalHecke (C1 p) ρ F).val = homAction ρ (zS p) (rationalHecke (primeDiagonal p) ρ F).val :=
  hecke_central_conj ρ (C1 p) (primeDiagonal p) (zS p) (zS_central p) (integralEquiv wSwap)
    (integralEquiv wSwap) (by simpa using C1_decomp p) F

theorem lineAction_scalar (g : GL2) (c : ℚ) (hc : c ≠ 0) (h : ∀ v, vectorAction g v = c • v)
    (L : Line) : lineAction g L = L := by
  apply Subtype.ext
  change Submodule.map (vectorAction g).toLinearMap L.val = L.val
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, h]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact L.val.smul_mem c hy
  · intro hx
    exact ⟨c⁻¹ • x, L.val.smul_mem _ hx, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

theorem action_scalar (g : GL2) (c : ℚ) (hc : c ≠ 0) (h : ∀ v, vectorAction g v = c • v) (σ : St) :
    action g σ = σ := by
  apply Subtype.ext
  change divisorAction g σ.val = σ.val
  have hl : lineAction g = id := funext (lineAction_scalar g c hc h)
  change Finsupp.lmapDomain ℚ ℚ (lineAction g) σ.val = σ.val
  rw [hl]
  simp

open TernaryPeriodPolynomials.Argument.HeckeHomology in
theorem vectorAction_zS_inv (p : ℕ) [Fact p.Prime] (v : TernaryPoly.RankTwoAugmentedFrames.Space) :
    vectorAction (zS p)⁻¹ v = (p : ℚ) • v := by
  have hp := p_ne_zero_rat p
  ext i
  fin_cases i <;>
    simp [vectorAction, zS, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

open TernaryPeriodPolynomials.Argument.HeckeHomology in
theorem action_zS_inv (p : ℕ) [Fact p.Prime] (σ : St) : action (zS p)⁻¹ σ = σ :=
  action_scalar _ (p : ℚ) (p_ne_zero_rat p) (vectorAction_zS_inv p) σ

open TernaryPeriodPolynomials.Argument.HeckeHomology in
theorem rho_zS (p d : ℕ) [Fact p.Prime] (w : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    BinaryModularSymbolCoefficients.homogeneousAction d (-1) (zS p) w = (p : ℚ) ^ (d + 2) • w := by
  have hp := p_ne_zero_rat p
  have h := TernaryPeriodPolynomials.Argument.AppendixBResidue.homogeneousAction_twist d 0 (-1) (zS p) w
  rw [zero_add] at h
  rw [h]
  have h0 : BinaryModularSymbolCoefficients.homogeneousAction d 0 (zS p) w = (p : ℚ) ^ d • w :=
    binMod_zS p d w
  rw [h0]
  have hd : ((zS p).val.det : ℚ) = ((p : ℚ)⁻¹) * (p : ℚ)⁻¹ := by
    simp [zS, Matrix.det_fin_two]
  rw [hd, smul_smul]
  congr 1
  rw [zpow_neg_one, mul_inv, inv_inv]
  ring

open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPoly.BinaryRationalHeckePrime in
/-- **L6c, Hom form.** For the exponent `-1`: `T[C1] F = p^(d+2) T[diag(p,1)] F`. -/
theorem hecke_C1_neg (p d : ℕ) [Fact p.Prime]
    (F : Hom (BinaryModularSymbolCoefficients.homogeneousAction d (-1))) :
    (rationalHecke (C1 p) (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) F).val =
      (p : ℚ) ^ (d + 2) •
        (rationalHecke (primeDiagonal p) (BinaryModularSymbolCoefficients.homogeneousAction d (-1)) F).val := by
  rw [hecke_C1]
  apply LinearMap.ext
  intro c
  simp only [homAction_apply, action_zS_inv, rho_zS, LinearMap.smul_apply]

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeHom
