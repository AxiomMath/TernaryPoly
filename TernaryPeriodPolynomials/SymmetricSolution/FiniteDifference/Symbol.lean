module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusData
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeDescent

@[expose] public section

/-!
# Lemma B.1, period clause: the period symbol of a class in `H₁(GL₂(ℤ), M)`

Formalized by Claude Sonnet 5.5.  Paper: Lemma B.1 (`lem:literal-residue-comparison`), last paragraph of the proof: "the binary modular symbol from `0` to `i∞`
crosses the standard edge once. Pairing with an arbitrary dual binary coefficient identifies its edge coefficient with the odd part of
`∫_0^{i∞} h(z)(zc-b)^{n+1} dz`".

For every `ℚ`-representation `M` of `Γ = GL₂(ℤ)`:
* `SymHom M`: `Γ`-maps `σ : St → M` for the determinant-twisted action `stD`;
* `symEquiv M : PhiM M ≃ₗ SymHom M`: descent of `β`-killing `Γ`-maps `P1 → M` along the surjection `π : P1 → St`;
* `symbolEquiv M : H₁(Γ, M) ≃ₗ SymHom M` (the **period symbol** of a class): the Frobenius duality of `BridgeFrobenius` followed by descent.
  `symbolEquiv_edge`: `σ_x(edgeSym e)` is the `e`-coefficient of the Farey cycle of `x`; `symbolEquiv_reference`:
  `σ_x(reference) = edge₂ x` (the reference symbol `∞ → 0` is the symbol of the standard oriented edge `p₀`, `piL E₀ = 2 · reference`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.HeckeNormalization
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open scoped Classical MonoidAlgebra

section Symbol

variable (M : Rep ℚ IntegralGL)

/-- `Hom_Γ(St^δ, M)`: linear maps `σ : St → M` equivariant for the determinant-twisted action `stD`. -/
def SymHom : Submodule ℚ (St →ₗ[ℚ] M) where
  carrier := {σ | ∀ (g : IntegralGL) (c : St), σ (stD g c) = M.ρ g (σ c)}
  add_mem' := by
    intro a b ha hb g c
    rw [LinearMap.add_apply, ha g c, hb g c, LinearMap.add_apply, map_add]
  zero_mem' := by intro g c; simp
  smul_mem' := by
    intro r a ha g c
    rw [LinearMap.smul_apply, ha g c, LinearMap.smul_apply, map_smul]

theorem piL_equivariant (g : IntegralGL) (x : P1) : piL (P1.ρ g x) = stD g (piL x) :=
  Rep.hom_comm_apply piT g (x : PE)

theorem piL_betaL (t : P0) : piL (betaL t) = 0 := by
  induction t using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | single t r =>
    change piT.hom (bdryMap.hom (MonoidAlgebra.single t r)) = 0
    rw [bdryMap_single, map_smul, piT_bdryV, smul_zero]

theorem piL_E0 : piL E0 = (2 : ℚ) • reference := by
  change piT.hom (MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ)) = _
  rw [map_sub, piT_single, piT_single, edgeSym_swap, edgeSym_p0, one_smul, one_smul]
  module

theorem piL_Ee (e : OTE) : piL (Ee e) = (2 : ℚ) • edgeSym e := by
  change piT.hom (MonoidAlgebra.single e (1 : ℚ) - MonoidAlgebra.single e.swap (1 : ℚ)) = _
  rw [map_sub, piT_single, piT_single, edgeSym_swap, one_smul, one_smul]
  module

theorem piL_ker_le (Φ : PhiM M) : LinearMap.ker piL ≤ LinearMap.ker (Φ : P1 →ₗ[ℚ] M) := by
  intro x hx
  obtain ⟨t, rfl⟩ := ker_piL x hx
  exact Φ.2.2 t

/-- The descent of a `β`-killing `Γ`-map `Φ : P1 → M` along the surjection `π : P1 → St`. -/
def symDescend (Φ : PhiM M) : St →ₗ[ℚ] M :=
  ((LinearMap.ker piL).liftQ (Φ : P1 →ₗ[ℚ] M) (piL_ker_le M Φ)) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective piL piL_surjective).symm.toLinearMap

theorem symDescend_piL (Φ : PhiM M) (x : P1) : symDescend M Φ (piL x) = (Φ : P1 →ₗ[ℚ] M) x := by
  change ((LinearMap.ker piL).liftQ (Φ : P1 →ₗ[ℚ] M) (piL_ker_le M Φ))
    ((LinearMap.quotKerEquivOfSurjective piL piL_surjective).symm (piL x)) = _
  have : (LinearMap.quotKerEquivOfSurjective piL piL_surjective).symm (piL x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem symDescend_mem (Φ : PhiM M) : symDescend M Φ ∈ SymHom M := by
  intro g c
  obtain ⟨x, rfl⟩ := piL_surjective c
  rw [← piL_equivariant, symDescend_piL, symDescend_piL, Φ.2.1]

/-- `Hom_Γ(P1, M) ∩ {Φ β = 0} ≃ Hom_Γ(St^δ, M)`: descent along `π : P1 → St`. -/
def symEquiv : PhiM M ≃ₗ[ℚ] SymHom M where
  toFun Φ := ⟨symDescend M Φ, symDescend_mem M Φ⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := piL_surjective c
    change symDescend M (Φ + Ψ) (piL x) = symDescend M Φ (piL x) + symDescend M Ψ (piL x)
    rw [symDescend_piL, symDescend_piL, symDescend_piL]
    rfl
  map_smul' r Φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := piL_surjective c
    change symDescend M (r • Φ) (piL x) = r • symDescend M Φ (piL x)
    rw [symDescend_piL, symDescend_piL]
    rfl
  invFun σ := ⟨(σ : St →ₗ[ℚ] M) ∘ₗ piL, fun g x => by
      change σ.1 (piL (P1.ρ g x)) = M.ρ g (σ.1 (piL x))
      rw [piL_equivariant]; exact σ.2 g _, fun t => by
      change σ.1 (piL (betaL t)) = 0
      rw [piL_betaL, map_zero]⟩
  left_inv Φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact symDescend_piL M Φ x
  right_inv σ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := piL_surjective c
    exact symDescend_piL M ⟨(σ : St →ₗ[ℚ] M) ∘ₗ piL, _⟩ x

/-- **The period symbol of a class in `H₁(GL₂(ℤ), M)`**: the Frobenius duality `H₁(Γ, M) ≃ Hom_Γ(P1, M) ∩ {β-killing}`
followed by descent along the symbol map `π : P1 → St`.  The value of the symbol `σ_x` on the symbol `edgeSym e` of an
oriented dual edge is the coefficient at `e` of the Farey cycle of `x` (`symbolEquiv_edge`). -/
def symbolEquiv : groupHomology M 1 ≃ₗ[ℚ] SymHom M := (frobM M).trans (symEquiv M)

theorem symbolEquiv_piL (x : groupHomology M 1) (y : P1) :
    ((symbolEquiv M x : SymHom M) : St →ₗ[ℚ] M) (piL y) = ((frobM M x : PhiM M) : P1 →ₗ[ℚ] M) y :=
  symDescend_piL M (frobM M x) y

/-- **Normalization**: the period symbol of `x` on the reference symbol `∞ → 0` is the standard-edge coefficient. -/
theorem symbolEquiv_reference (x : groupHomology M 1) :
    ((symbolEquiv M x : SymHom M) : St →ₗ[ℚ] M) reference = edge2 M x := by
  have h := symbolEquiv_piL M x E0
  rw [piL_E0, map_smul, frobM_E0] at h
  have h2 : (2 : ℚ) • ((symbolEquiv M x : SymHom M) : St →ₗ[ℚ] M) reference = (2 : ℚ) • edge2 M x := h
  exact smul_right_injective M (two_ne_zero) h2

/-- The value of the period symbol on the symbol of an oriented dual edge `e` is the `e`-coefficient of the Farey cycle. -/
theorem symbolEquiv_edge (x : groupHomology M 1) (e : OTE) :
    ((symbolEquiv M x : SymHom M) : St →ₗ[ℚ] M) (edgeSym e) = ((h1Fun M x).1 : OTE → M) e := by
  have h := symbolEquiv_piL M x (Ee e)
  rw [piL_Ee, map_smul] at h
  change (2 : ℚ) • _ = phiOf M (h1Fun M x).1 (Ee e) at h
  rw [phiOf_Ee, (h1Fun M x).2.1 e, sub_neg_eq_add, ← two_smul ℚ] at h
  exact smul_right_injective M (two_ne_zero) h

end Symbol

end TernaryPeriodPolynomials.Argument.LemmaB1Period
