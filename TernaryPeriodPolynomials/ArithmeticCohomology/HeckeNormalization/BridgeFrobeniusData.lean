module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobenius
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeInterface

@[expose] public section


/-!
# L1 for `H₁(GL₂(ℤ), Sym^d)`: the `FrobData` of the Hecke bridge

Formalized by Claude Sonnet 5.5.  Discharges `BridgeInterface.L1 d`.

For every `ℚ`-representation `M` of `GL₂(ℤ)`: `frobM M : H₁(Γ, M) ≃ₗ PhiM M`, where `PhiM M` is the space of `Γ`-equivariant linear
maps `Φ : P1 → M` with `Φ ∘ β = 0` (`BridgeInterface.PhiSp` is `PhiM (Dplain d)`, `PhiSp_eq_PhiM`).  It is the composite of
`h1Fun : H₁(Γ, M) ≃ₗ H1Fun M` (`BridgeFrobenius`) with `phiEquiv : H1Fun M ≃ₗ PhiM M`, `F ↦ Φ_F = (∑ c_e [e] ↦ ∑ c_e F(e))`,
with inverse `Φ ↦ (e ↦ Φ(E_e)/2)`, `E_e = [e] - [e.swap]`.  `frobM_E0` : `(frobM y)(E₀) = 2 · edge2 y`, so `frobData d` is a
`BridgeInterface.FrobData d` with `κ = 2`, and `L1_holds d : BridgeInterface.L1 d`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open CategoryTheory Representation Rep TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open scoped Classical MonoidAlgebra

section PhiM

variable (M : Rep ℚ IntegralGL)

/-- `Hom_Γ(P1, M) ∩ {Φ ∘ β = 0}`: the general-`M` version of `BridgeInterface.PhiSp`. -/
def PhiM : Submodule ℚ (P1 →ₗ[ℚ] M) where
  carrier := {Φ | (∀ (γ : IntegralGL) (x : P1), Φ (P1.ρ γ x) = M.ρ γ (Φ x)) ∧ ∀ t : P0, Φ (betaL t) = 0}
  add_mem' := by
    rintro Φ Ψ ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun γ x => by rw [LinearMap.add_apply, h1 γ x, k1 γ x, LinearMap.add_apply, map_add],
      fun t => by rw [LinearMap.add_apply, h2 t, k2 t, add_zero]⟩
  zero_mem' := ⟨fun γ x => by simp, fun t => by simp⟩
  smul_mem' := by
    rintro c Φ ⟨h1, h2⟩
    exact ⟨fun γ x => by rw [LinearMap.smul_apply, h1 γ x, LinearMap.smul_apply, map_smul],
      fun t => by rw [LinearMap.smul_apply, h2 t, smul_zero]⟩

theorem PhiSp_eq_PhiM (d : ℕ) : PhiSp d = PhiM (Dplain d) := rfl

/-- The antisymmetric edge `E_e = [e] - [e.swap] ∈ P1`. -/
def Ee (e : OTE) : P1 := ⟨MonoidAlgebra.single e (1 : ℚ) - MonoidAlgebra.single e.swap (1 : ℚ), by
  rw [mem_antiSub, map_sub, swapMap_single, swapMap_single, OTE.swap_swap]; abel⟩

theorem E0_eq_Ee : E0 = Ee p0 := rfl

theorem Ee_swap (e : OTE) : Ee e.swap = -Ee e := by
  apply Subtype.ext
  change MonoidAlgebra.single e.swap (1 : ℚ) - MonoidAlgebra.single e.swap.swap (1 : ℚ) =
    -(MonoidAlgebra.single e (1 : ℚ) - MonoidAlgebra.single e.swap (1 : ℚ))
  rw [OTE.swap_swap]; abel

theorem Ee_smul (γ : IntegralGL) (e : OTE) : Ee (γ • e) = P1.ρ γ (Ee e) := by
  apply Subtype.ext
  change MonoidAlgebra.single (γ • e) (1 : ℚ) - MonoidAlgebra.single (γ • e).swap (1 : ℚ) =
    PE.ρ γ (MonoidAlgebra.single e (1 : ℚ) - MonoidAlgebra.single e.swap (1 : ℚ))
  rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, OTE.swap_smul]

theorem betaL_eq (t : Tri) : betaL (MonoidAlgebra.single t (1 : ℚ)) = -∑ q ∈ nbF t, Ee q := by
  apply Subtype.ext
  change bdryMap.hom (MonoidAlgebra.single t (1 : ℚ)) = ((-∑ q ∈ nbF t, Ee q : P1) : PE)
  rw [bdryMap_single, one_smul]
  unfold bdryV
  rw [Submodule.coe_neg, Submodule.coe_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  change _ = -(MonoidAlgebra.single q (1 : ℚ) - MonoidAlgebra.single q.swap (1 : ℚ))
  abel

theorem EqFun.equiv_apply (F : EqFun (Γ := IntegralGL) OTE M) :
    ∀ (g : IntegralGL) (x : OTE), (F : OTE → M) (g • x) = M.ρ g ((F : OTE → M) x) := F.2

/-- The `P1`-linear extension `Φ_F` of an equivariant function `F : OTE → M`: `Φ_F(c) = ∑_e c(e) F(e)`. -/
def phiOf (F : EqFun (Γ := IntegralGL) OTE M) : P1 →ₗ[ℚ] M :=
  (permLift M (F : OTE → M) (EqFun.equiv_apply M F)).hom.toLinearMap ∘ₗ antiSub.subtype

theorem phiOf_equivariant (F : EqFun (Γ := IntegralGL) OTE M) (γ : IntegralGL) (x : P1) :
    phiOf M F (P1.ρ γ x) = M.ρ γ (phiOf M F x) :=
  Rep.hom_comm_apply (permLift M (F : OTE → M) (EqFun.equiv_apply M F)) γ (x : PE)

theorem phiOf_Ee (F : EqFun (Γ := IntegralGL) OTE M) (e : OTE) :
    phiOf M F (Ee e) = (F : OTE → M) e - (F : OTE → M) e.swap := by
  change (permLift M (F : OTE → M) (EqFun.equiv_apply M F)).hom (MonoidAlgebra.single e (1 : ℚ) - MonoidAlgebra.single e.swap (1 : ℚ)) = _
  rw [map_sub, permLift_single, permLift_single, one_smul, one_smul]

theorem phiOf_E0 (F : EqFun (Γ := IntegralGL) OTE M) :
    phiOf M F E0 = (F : OTE → M) p0 - (F : OTE → M) p0.swap := phiOf_Ee M F p0

theorem phiOf_betaL (F : H1Fun M) (t : Tri) : phiOf M F.1 (betaL (MonoidAlgebra.single t (1 : ℚ))) = 0 := by
  rw [betaL_eq, map_neg, map_sum]
  have : ∀ q ∈ nbF t, phiOf M F.1 (Ee q) = (2 : ℚ) • (F.1 : OTE → M) q := by
    intro q _
    rw [phiOf_Ee, F.2.1 q, two_smul]
    abel
  rw [Finset.sum_congr rfl this, ← Finset.smul_sum, F.2.2 t, smul_zero, neg_zero]

theorem phiOf_mem (F : H1Fun M) : phiOf M F.1 ∈ PhiM M := by
  refine ⟨phiOf_equivariant M F.1, fun t => ?_⟩
  induction t using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | single t r =>
    have : (MonoidAlgebra.single t r : P0) = r • MonoidAlgebra.single t (1 : ℚ) := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, phiOf_betaL, smul_zero]

theorem retrP1_single (e : OTE) : retrP1.hom (MonoidAlgebra.single e (1 : ℚ)) = (1 / 2 : ℚ) • Ee e := by
  apply Subtype.ext
  change antiLin (MonoidAlgebra.single e (1 : ℚ)) = ((1 / 2 : ℚ) • Ee e : P1)
  rw [antiLin_apply, swapMap_single]
  rfl

theorem P1_hom_ext {Φ Ψ : P1 →ₗ[ℚ] M} (h : ∀ e : OTE, Φ (Ee e) = Ψ (Ee e)) : Φ = Ψ := by
  have key : Φ ∘ₗ retrP1.hom.toLinearMap = Ψ ∘ₗ retrP1.hom.toLinearMap := by
    refine MonoidAlgebra.lhom_ext' fun e => LinearMap.ext_ring ?_
    change Φ (retrP1.hom (MonoidAlgebra.single e (1 : ℚ))) = Ψ (retrP1.hom (MonoidAlgebra.single e (1 : ℚ)))
    rw [retrP1_single, map_smul, map_smul, h e]
  apply LinearMap.ext
  intro x
  have hx : retrP1.hom (inclP1.hom x) = x :=
    LinearMap.congr_fun (congrArg (fun f => f.hom.toLinearMap) inclP1_retrP1) x
  have := LinearMap.congr_fun key (inclP1.hom x)
  simp only [LinearMap.comp_apply] at this
  change Φ (retrP1.hom (inclP1.hom x)) = Ψ (retrP1.hom (inclP1.hom x)) at this
  rwa [hx] at this

/-- The equivariant function `e ↦ Φ(E_e) / 2` attached to `Φ ∈ PhiM`. -/
def funOf (Φ : PhiM M) : OTE → M := fun e => (1 / 2 : ℚ) • (Φ : P1 →ₗ[ℚ] M) (Ee e)

theorem funOf_equiv (Φ : PhiM M) : funOf M Φ ∈ EqFun (Γ := IntegralGL) OTE M := by
  intro γ e
  unfold funOf
  rw [Ee_smul, Φ.2.1 γ, map_smul]

theorem funOf_mem (Φ : PhiM M) : (⟨funOf M Φ, funOf_equiv M Φ⟩ : EqFun (Γ := IntegralGL) OTE M) ∈ H1Fun M := by
  refine ⟨fun e => ?_, fun t => ?_⟩
  · change (1 / 2 : ℚ) • (Φ : P1 →ₗ[ℚ] M) (Ee e.swap) = -((1 / 2 : ℚ) • (Φ : P1 →ₗ[ℚ] M) (Ee e))
    rw [Ee_swap, map_neg, smul_neg]
  · change ∑ q ∈ nbF t, (1 / 2 : ℚ) • (Φ : P1 →ₗ[ℚ] M) (Ee q) = 0
    rw [← Finset.smul_sum, ← map_sum]
    have h := Φ.2.2 (MonoidAlgebra.single t (1 : ℚ))
    rw [betaL_eq, map_neg, neg_eq_zero] at h
    rw [h, smul_zero]

theorem phiOf_funOf (Φ : PhiM M) :
    phiOf M ⟨funOf M Φ, funOf_equiv M Φ⟩ = (Φ : P1 →ₗ[ℚ] M) := by
  apply P1_hom_ext
  intro e
  rw [phiOf_Ee]
  change (1 / 2 : ℚ) • (Φ : P1 →ₗ[ℚ] M) (Ee e) - (1 / 2 : ℚ) • (Φ : P1 →ₗ[ℚ] M) (Ee e.swap) = _
  rw [Ee_swap, map_neg, smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num

theorem funOf_phiOf (F : H1Fun M) :
    funOf M ⟨phiOf M F.1, phiOf_mem M F⟩ = (F.1 : OTE → M) := by
  funext e
  unfold funOf
  change (1 / 2 : ℚ) • phiOf M F.1 (Ee e) = _
  rw [phiOf_Ee, F.2.1 e, sub_neg_eq_add, ← two_smul ℚ ((F.1 : OTE → M) e), smul_smul]
  norm_num

theorem phiOf_add (F G : EqFun (Γ := IntegralGL) OTE M) : phiOf M (F + G) = phiOf M F + phiOf M G := by
  apply P1_hom_ext
  intro e
  rw [LinearMap.add_apply, phiOf_Ee, phiOf_Ee, phiOf_Ee]
  change (F : OTE → M) e + (G : OTE → M) e - ((F : OTE → M) e.swap + (G : OTE → M) e.swap) = _
  abel

theorem phiOf_smul (c : ℚ) (F : EqFun (Γ := IntegralGL) OTE M) : phiOf M (c • F) = c • phiOf M F := by
  apply P1_hom_ext
  intro e
  rw [LinearMap.smul_apply, phiOf_Ee, phiOf_Ee]
  change c • (F : OTE → M) e - c • (F : OTE → M) e.swap = _
  rw [smul_sub]

/-- `H1Fun M ≃ PhiM M`: the period function `F` and the `P1`-linear form `Φ_F = ∑ c(e) F(e)`. -/
def phiEquiv : H1Fun M ≃ₗ[ℚ] PhiM M where
  toFun F := ⟨phiOf M F.1, phiOf_mem M F⟩
  map_add' F G := Subtype.ext (phiOf_add M F.1 G.1)
  map_smul' c F := Subtype.ext (phiOf_smul M c F.1)
  invFun Φ := ⟨⟨funOf M Φ, funOf_equiv M Φ⟩, funOf_mem M Φ⟩
  left_inv F := Subtype.ext (Subtype.ext (funOf_phiOf M F))
  right_inv Φ := Subtype.ext (phiOf_funOf M Φ)

theorem phiEquiv_apply (F : H1Fun M) : ((phiEquiv M F : PhiM M) : P1 →ₗ[ℚ] M) = phiOf M F.1 := rfl

/-- Frobenius duality `H₁(Γ, M) ≃ PhiM M` (L1), composed from `h1Fun` and `phiEquiv`. -/
def frobM : groupHomology M 1 ≃ₗ[ℚ] PhiM M := (h1Fun M).trans (phiEquiv M)

/-- `(frobM y)(E₀) = 2 · edge2 y`. -/
theorem frobM_E0 (y : groupHomology M 1) :
    ((frobM M y : PhiM M) : P1 →ₗ[ℚ] M) E0 = (2 : ℚ) • edge2 M y := by
  change phiOf M (h1Fun M y).1 E0 = _
  rw [phiOf_E0, (h1Fun M y).2.1 p0, sub_neg_eq_add, two_smul]
  rfl

/-- **L1** (`BridgeInterface.L1 d`): Frobenius duality for `H₁(GL₂(ℤ), Sym^d)` with the universal constant `κ = 2`. -/
def frobData (d : ℕ) : BridgeInterface.FrobData d where
  κ := 2
  κ_ne := by norm_num
  frob := (frobM (Dplain d)).trans (LinearEquiv.ofEq _ _ (PhiSp_eq_PhiM d).symm)
  eval := fun y => frobM_E0 (Dplain d) y

theorem L1_holds (d : ℕ) : BridgeInterface.L1 d := ⟨frobData d⟩

end PhiM

end TernaryPeriodPolynomials.Argument.HeckeNormalization
