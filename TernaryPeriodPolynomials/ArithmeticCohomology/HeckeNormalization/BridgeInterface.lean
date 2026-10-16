module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.Bridge
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaLevi

@[expose] public section


/-!
# Interface statements for the proof of `HomologyHomBridge p d (p^(d+1))` (B1)

Formalized by Claude Sonnet 5.5.

Only definitions and `Prop`-valued statements.  Division of labour:

* `L3 p`: the dual lift `DualLift p` exists (comparison theorem on `0 → P0 → P1 → St_δ → 0`).
* `L2 p`, `L2b p`: transposition `DualLift → LiftData` and `LiftData` over the identity `→ LiftRes` with `LiftOverId`.
* `L1 d`: Frobenius duality `FrobData d`.
* `L5 p d`: `edge`-coefficient formula `(TΦ)(E₀) = homT s Φ E₀`.
* `L4 p`: the transposed lift covers the identity.
* L6 and the assembly: `BridgeMain.lean`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology

/-- Standard pairing on `ℚ[Tri]`. -/
def pairT (u v : P0) : ℚ := (MonoidAlgebra.coeffLinearEquiv ℚ u).sum fun t a => a * (MonoidAlgebra.coeffLinearEquiv ℚ v) t

/-- Standard pairing on `ℚ[OTE]` (restricted to `P1`). -/
def pairE (u v : PE) : ℚ := (MonoidAlgebra.coeffLinearEquiv ℚ u).sum fun t a => a * (MonoidAlgebra.coeffLinearEquiv ℚ v) t

/-- `d1 : P1 → P0` as a linear map. -/
def d1L : P1 →ₗ[ℚ] P0 := d1.hom.toLinearMap

/-- `β : P0 → P1`, the transposed boundary. -/
def betaL : P0 →ₗ[ℚ] P1 :=
  LinearMap.codRestrict antiSub (bdryMap.hom.toLinearMap) bdryMap_mem_antiSub

/-- `π : P1 → St`. -/
def piL : P1 →ₗ[ℚ] St := piT.hom.toLinearMap ∘ₗ antiSub.subtype

/-- The standard antisymmetric edge `E₀ = [p₀] - [p₀.swap] ∈ P1`. -/
def E0 : P1 := ⟨MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ), by
  rw [mem_antiSub, map_sub, swapMap_single, swapMap_single, OTE.swap_swap]; abel⟩

variable (p : ℕ) [Fact p.Prime]

/-- The correspondence on cusps/symbols: the action of `g⁻¹ = diag(p,1)` on `St`. -/
def psi : St →ₗ[ℚ] St := action (C1 p)⁻¹

/-- **Data produced by L3** (the dual lift): `S`-equivariant, `f`-twisted maps on `P0`, `P1` with
`s(f(σ) x) = σ s(x)`, a chain map for `β`, covering `Ψ = g⁻¹·` on `St`. -/
structure DualLift where
  s0 : P0 →ₗ[ℚ] P0
  s1 : P1 →ₗ[ℚ] P1
  eq0 : ∀ (σ : (binDatum p).S) (x : P0), s0 (P0.ρ ((binDatum p).f σ) x) = P0.ρ σ.1 (s0 x)
  eq1 : ∀ (σ : (binDatum p).S) (x : P1), s1 (P1.ρ ((binDatum p).f σ) x) = P1.ρ σ.1 (s1 x)
  chain : ∀ t : P0, betaL (s0 t) = s1 (betaL t)
  symbol : ∀ x : P1, piL (s1 x) = psi p (piL x)

/-- **L3** (S1): the dual lift exists (comparison theorem: `Res_f P1` is `S`-projective by `binDatum_hproj`,
`piL` is onto, `ker piL = im betaL` by `FareyKernel`). -/
def L3 : Prop := Nonempty (DualLift p)

/-- A lift data: the chain map `lam : Res_S P• → Res_f P•` of `LiftRes`, in terms of linear maps. -/
structure LiftData where
  lam0 : P0 →ₗ[ℚ] P0
  lam1 : P1 →ₗ[ℚ] P1
  eq0 : ∀ (σ : (binDatum p).S) (x : P0), lam0 (P0.ρ σ.1 x) = P0.ρ ((binDatum p).f σ) (lam0 x)
  eq1 : ∀ (σ : (binDatum p).S) (x : P1), lam1 (P1.ρ σ.1 x) = P1.ρ ((binDatum p).f σ) (lam1 x)
  chain : ∀ x : P1, d1L (lam1 x) = lam0 (d1L x)

/-- `lam` is the adjoint of `s` for the standard pairings. -/
def LiftData.IsAdjoint {p : ℕ} [Fact p.Prime] (l : LiftData p) (s : DualLift p) : Prop :=
  (∀ u v : P0, pairT (l.lam0 u) v = pairT u (s.s0 v)) ∧
  (∀ u v : P1, pairE (l.lam1 u : PE) (v : PE) = pairE (u : PE) (s.s1 v : PE))

/-- Over the identity: `ε ∘ lam₀ = ε` (the `LiftOverId` condition in coordinates). -/
def LiftData.OverId {p : ℕ} [Fact p.Prime] (l : LiftData p) : Prop :=
  ∀ t : P0, epsMap.hom (l.lam0 t) = epsMap.hom t

/-- **L2** (S2): transposition. -/
def L2 : Prop := ∀ s : DualLift p, ∃ l : LiftData p, l.IsAdjoint s

/-- **L4** (S5, the crux): the transposed lift covers the identity. -/
def L4 : Prop := ∀ (s : DualLift p) (l : LiftData p), l.IsAdjoint s → l.OverId

/-- **L2b** (S2/S1): a `LiftData` over the identity is the same as a `LiftRes` of `farResolution` with
`LiftOverId` (the terms `farResolution.complex.X 0 = P0`, `X 1 = P1` are definitional). -/
def L2b : Prop := ∀ l : LiftData p, l.OverId →
  ∃ lam : LiftRes (binDatum p) farResolution, LiftOverId (binDatum p) farResolution lam ∧
    (∀ x : P0, (lam.f 0).hom x = l.lam0 x) ∧ (∀ x : P1, (lam.f 1).hom x = l.lam1 x)

/-- The `Φ`-space of `Γ`-maps `P1 → Sym^d` killing `β`. -/
def PhiSp (d : ℕ) : Submodule ℚ (P1 →ₗ[ℚ] (Dplain d)) where
  carrier := {Φ | (∀ (γ : IntegralGL) (x : P1), Φ (P1.ρ γ x) = (Dplain d).ρ γ (Φ x)) ∧
    ∀ t : P0, Φ (betaL t) = 0}
  add_mem' := by
    rintro Φ Ψ ⟨h1, h2⟩ ⟨k1, k2⟩
    exact ⟨fun γ x => by rw [LinearMap.add_apply, h1 γ x, k1 γ x, LinearMap.add_apply, map_add],
      fun t => by rw [LinearMap.add_apply, h2 t, k2 t, add_zero]⟩
  zero_mem' := ⟨fun γ x => by simp, fun t => by simp⟩
  smul_mem' := by
    rintro c Φ ⟨h1, h2⟩
    exact ⟨fun γ x => by rw [LinearMap.smul_apply, h1 γ x, LinearMap.smul_apply, map_smul],
      fun t => by rw [LinearMap.smul_apply, h2 t, smul_zero]⟩

/-- **L1** (S2): Frobenius duality for `H₁(GL₂(ℤ), Sym^d)`, with a universal nonzero constant `κ₁`. -/
structure FrobData (d : ℕ) where
  κ : ℚ
  κ_ne : κ ≠ 0
  frob : groupHomology (Dplain d) 1 ≃ₗ[ℚ] PhiSp d
  eval : ∀ y, ((frob y : PhiSp d) : P1 →ₗ[ℚ] (Dplain d)) E0 = κ • edge2 (Dplain d) y

def L1 (d : ℕ) : Prop := Nonempty (FrobData d)

/-- The Hom-form of the Hecke operator on `Φ` through the transposed lift (the formula of L5):
`(TΦ)(e) = Σ_{y ∈ Γ/f(S)} ρ(y g) Φ(s₁(y⁻¹ e))`, `g = C1 p`. -/
def homT (s : DualLift p) (d : ℕ) (Φ : P1 →ₗ[ℚ] (Dplain d)) (e : P1) : Dplain d :=
  ∑ᶠ y : IntegralGL ⧸ (binDatum p).f.range,
    (binMod d).ρ (binIota (Quotient.out y) * C1 p) (Φ (s.s1 (P1.ρ (Quotient.out y)⁻¹ e)))

/-- **L5**: the homology Hecke operator in Frobenius form, for a transposed lift over the identity. -/
def L5 (d : ℕ) : Prop := ∀ (F : FrobData d) (s : DualLift p) (l : LiftData p), l.IsAdjoint s → l.OverId →
  ∀ y : groupHomology (Dplain d) 1,
    ((F.frob ((heckeOp (binDatum p) (binMod d) 1).hom y) : PhiSp d) : P1 →ₗ[ℚ] (Dplain d)) E0 =
      homT p s d ((F.frob y : PhiSp d) : P1 →ₗ[ℚ] (Dplain d)) E0

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
