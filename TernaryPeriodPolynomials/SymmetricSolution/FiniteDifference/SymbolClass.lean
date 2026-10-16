module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Symbol
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Equiv
public import TernaryPeriodPolynomials.BoundaryComparison.BinaryDuality

@[expose] public section

/-!
# Lemma B.1, period clause: the binary duality `Hom_Γ(St^δ, M) ≃ H₁(GL₂(ℤ), M)` from the dual Farey data

Formalized by Claude Sonnet 5.5.

* `edgeFun σ`, `edgeFun_mem`: for `σ : St → M` equivariant for `stD`, the function `e ↦ σ(edgeSym e)` on oriented dual edges
  (`edgeSym e` the Farey modular symbol of the edge, `edgeSym (γ • p₀) = det γ • γ • reference`, `edgeSym p₀ = reference`) is a
  Farey cycle: equivariant, antisymmetric (`edgeSym_swap`) with zero outgoing sum at every triangle (the three edges of a triangle sum to
  zero in `St`, `edgeSym_sum_nbF`).
* `symbolClassM M : SymHom M → H₁(Γ, M)` (defined from this cycle only) is the inverse of the period symbol `symbolEquiv`
  (`symbolEquiv_symbolClassM`, `symbolClassM_eq_symm`), and `edge2_symbolClassM : edge₂ (class σ) = σ(reference)`.
* Hom-model form: `PeriodHom d = Hom_Γ(St, Sym^d)` (exponent `-1`) equals `Hom_Γ(St^δ, Sym^d)` for the plain action
  (`mem_periodHom_iff`); `symbolClass d : PeriodHom d → H₁(GL₂(ℤ), Sym^d)`, `symbolClass_bijective`, and
  `edge2_symbolClass : edge₂ (symbolClass Φ) = periodEquiv Φ`, i.e. the scalar is `c₂ = 1` with the orientation of the reference
  symbol `∞ → 0` equal to that of the standard dual edge `p₀ = (triPlus → triMinus)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.HeckeNormalization
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open scoped Classical MonoidAlgebra

section SymbolClass

variable (M : Rep ℚ IntegralGL)

/-- The dual-Farey data of a symbol map `σ : St^δ → M`: the function `e ↦ σ(edgeSym e)` on oriented dual edges, where
`edgeSym e` is the Farey modular symbol of the edge (`edgeSym (γ • p₀) = det γ • γ • reference`). -/
def edgeFun (σ : SymHom M) : EqFun (Γ := IntegralGL) OTE M :=
  ⟨fun e => (σ : St →ₗ[ℚ] M) (edgeSym e), fun γ e => by
    change (σ : St →ₗ[ℚ] M) (edgeSym (γ • e)) = M.ρ γ ((σ : St →ₗ[ℚ] M) (edgeSym e))
    rw [edgeSym_smul]
    exact σ.2 γ _⟩

/-- **The cycle condition**: `e ↦ σ(edgeSym e)` is antisymmetric (reversing an edge negates its symbol) and has zero
outgoing sum at every triangle (the three edges of a triangle sum to zero in `St`). -/
theorem edgeFun_mem (σ : SymHom M) : edgeFun M σ ∈ H1Fun M := by
  refine ⟨fun e => ?_, fun t => ?_⟩
  · change (σ : St →ₗ[ℚ] M) (edgeSym e.swap) = -(σ : St →ₗ[ℚ] M) (edgeSym e)
    rw [edgeSym_swap, map_neg]
  · obtain ⟨g, rfl⟩ := tri_htr t
    change ∑ q ∈ nbF (g • triPlus), (σ : St →ₗ[ℚ] M) (edgeSym q) = 0
    rw [← map_sum, edgeSym_sum_nbF, map_zero]

/-- `σ ↦ (e ↦ σ(edgeSym e))`, linear. -/
def edgeFunLin : SymHom M →ₗ[ℚ] H1Fun M where
  toFun σ := ⟨edgeFun M σ, edgeFun_mem M σ⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (funext fun _ => rfl))
  map_smul' _ _ := Subtype.ext (Subtype.ext (funext fun _ => rfl))

/-- **The class of a symbol map**, defined from the dual-Farey data only: the Farey cycle with coefficient `σ(edgeSym e)` on the
oriented dual edge `e`. -/
def symbolClassM : SymHom M →ₗ[ℚ] groupHomology M 1 := (h1Fun M).symm.toLinearMap ∘ₗ edgeFunLin M

theorem h1Fun_symbolClassM (σ : SymHom M) (e : OTE) :
    ((h1Fun M (symbolClassM M σ)).1 : OTE → M) e = (σ : St →ₗ[ℚ] M) (edgeSym e) := by
  have h : h1Fun M (symbolClassM M σ) = edgeFunLin M σ := (h1Fun M).apply_symm_apply _
  rw [h]
  rfl

theorem symbolEquiv_symbolClassM (σ : SymHom M) : symbolEquiv M (symbolClassM M σ) = σ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro c
  obtain ⟨y, rfl⟩ := piL_surjective c
  have hy : ((symbolEquiv M (symbolClassM M σ) : SymHom M) : St →ₗ[ℚ] M) (piL y) =
      ((frobM M (symbolClassM M σ) : PhiM M) : P1 →ₗ[ℚ] M) y := symbolEquiv_piL M _ y
  rw [hy]
  have key : ((frobM M (symbolClassM M σ) : PhiM M) : P1 →ₗ[ℚ] M) = (σ : St →ₗ[ℚ] M) ∘ₗ piL := by
    apply P1_hom_ext
    intro e
    change phiOf M (h1Fun M (symbolClassM M σ)).1 (Ee e) = _
    rw [phiOf_Ee, (h1Fun M _).2.1 e, h1Fun_symbolClassM, LinearMap.comp_apply, piL_Ee, map_smul, two_smul]
    abel
  rw [key]
  rfl

/-- The class of a symbol map is the inverse of the period symbol. -/
theorem symbolClassM_eq_symm : (symbolClassM M : SymHom M →ₗ[ℚ] groupHomology M 1) = (symbolEquiv M).symm.toLinearMap := by
  apply LinearMap.ext
  intro σ
  apply (symbolEquiv M).injective
  rw [symbolEquiv_symbolClassM]
  exact ((symbolEquiv M).apply_symm_apply σ).symm

/-- The standard-edge coefficient of the class of `σ` is `σ(reference)`. -/
theorem edge2_symbolClassM (σ : SymHom M) : edge2 M (symbolClassM M σ) = (σ : St →ₗ[ℚ] M) reference := by
  rw [← symbolEquiv_reference, symbolEquiv_symbolClassM]

end SymbolClass

section PeriodHomClass

open TernaryPoly.OrdinaryResiduePeriod

/-- `Hom_Γ(St, Sym^d)` for the exponent `-1` is `Hom_Γ(St^δ, Sym^d)` for the plain action. -/
theorem mem_periodHom_iff (d : ℕ) (Φ : St →ₗ[ℚ] Dplain d) :
    Φ ∈ PeriodHom d ↔ Φ ∈ SymHom (Dplain d) := by
  constructor
  · intro h g c
    rw [stD_apply, map_smul]
    have h1 := h g c
    rw [rho_neg_one] at h1
    rw [h1, smul_smul, detQ_mul_self, one_smul]
  · intro h g c
    have e : action (integral g) c = detQ g • stD g c := by
      rw [stD_apply, smul_smul, detQ_mul_self, one_smul]
    rw [e, map_smul, h g c, rho_neg_one]

/-- The identification of the two descriptions of `Hom_Γ(St^δ, Sym^d)`. -/
def periodHomEquivSym (d : ℕ) : PeriodHom d ≃ₗ[ℚ] SymHom (Dplain d) :=
  LinearEquiv.ofEq _ _ (Submodule.ext fun Φ => mem_periodHom_iff d Φ)

/-- **The binary duality** `Hom_Γ(St^δ, Sym^d) ≃ H₁(GL₂(ℤ), Sym^d)` in the Hom-model form `PeriodHom d`. -/
def symbolClassEquiv (d : ℕ) : PeriodHom d ≃ₗ[ℚ] groupHomology (Dplain d) 1 :=
  (periodHomEquivSym d).trans (symbolEquiv (Dplain d)).symm

/-- The class of a period Hom: the Farey cycle with coefficient `Φ(edgeSym e)` on the oriented dual edge `e`
(defined from the dual-Farey data only). -/
def symbolClass (d : ℕ) : PeriodHom d →ₗ[ℚ] groupHomology (Dplain d) 1 :=
  symbolClassM (Dplain d) ∘ₗ (periodHomEquivSym d).toLinearMap

theorem symbolClass_eq_equiv (d : ℕ) (Φ : PeriodHom d) : symbolClass d Φ = symbolClassEquiv d Φ := by
  change symbolClassM (Dplain d) (periodHomEquivSym d Φ) = _
  rw [symbolClassM_eq_symm]
  rfl

theorem symbolClass_bijective (d : ℕ) : Function.Bijective (symbolClass d) := by
  have : (symbolClass d : PeriodHom d → _) = symbolClassEquiv d := funext (symbolClass_eq_equiv d)
  rw [this]
  exact (symbolClassEquiv d).bijective

/-- The coefficient of the Farey cycle of `symbolClass Φ` on the oriented dual edge `e` is `Φ(edgeSym e)`. -/
theorem h1Fun_symbolClass (d : ℕ) (Φ : PeriodHom d) (e : OTE) :
    ((h1Fun (Dplain d) (symbolClass d Φ)).1 : OTE → Dplain d) e = Φ.val (edgeSym e) :=
  h1Fun_symbolClassM (Dplain d) (periodHomEquivSym d Φ) e

/-- **`edge₂ ∘ symbolClass = periodEquiv`**, with scalar `c₂ = 1`: the orientation of the standard dual edge `p₀` is the one of the
reference symbol `∞ → 0` (`edgeSym p₀ = reference`). -/
theorem edge2_symbolClass (d : ℕ) (Φ : PeriodHom d) :
    edge2 (Dplain d) (symbolClass d Φ) = (periodEquiv d Φ).val := by
  change edge2 (Dplain d) (symbolClassM (Dplain d) (periodHomEquivSym d Φ)) = _
  rw [edge2_symbolClassM]
  rfl

/-- The same, for the Mathlib-level export `periodEquivHomology'`. -/
theorem periodEquivHomology_symbolClass (d : ℕ) (Φ : PeriodHom d) :
    TernaryPeriodPolynomials.Argument.Statements.BinaryDuality.periodEquivHomology' d (symbolClass d Φ) =
      periodEquiv d Φ :=
  Subtype.ext (edge2_symbolClass d Φ)

end PeriodHomClass

end TernaryPeriodPolynomials.Argument.LemmaB1Period
