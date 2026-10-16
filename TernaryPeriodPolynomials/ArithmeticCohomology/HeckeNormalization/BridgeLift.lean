module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeInterface

@[expose] public section


/-!
# L3: the comparison-theorem lift of the symbol-level Hecke correspondence to the dual Farey tree

Formalized by Claude Sonnet 5.5.

* `exists_comparison` (abstract): for an exact sequence `0 → P0 --β--> P1 --π--> X → 0` of `Γ`-modules with `Res_φ P0`, `Res_φ P1`
  projective over `H`, every `H`-morphism `Ψ : Res_φ X → Res_ψ X` lifts to `s₁ : Res_φ P1 → Res_ψ P1`, `s₀ : Res_φ P0 → Res_ψ P0`
  with `π s₁ = Ψ π` and `s₁ β = β s₀` (projectivity for `s₁`; for `s₀` projectivity onto the image of `β`).
* Farey specialization: `betaF = β` (corestriction of `bdryMap`), `piF = π` (symbol map on the antisymmetric chains, onto and with kernel
  `im β` by `FareyKernel`), `PsiG p : Res_f St^δ → Res_S St^δ`, `σ ↦ C₁⁻¹ σ` (a morphism of `S`-modules because
  `f(s) = C₁ s C₁⁻¹` and `det f(s) = det s`), `farLift_exists`, and `L3_holds : BridgeInterface.L3 p`.
-/

open CategoryTheory Representation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

section Abstract

variable {Γ : Type} [Group Γ]

/-- The image of a morphism as a subrepresentation. -/
def imRep {P0 P1 : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) : Rep.{0} ℚ Γ :=
  Rep.of (P1.ρ.subrepresentation (LinearMap.range β.hom.toLinearMap) (fun g x hx => by
    obtain ⟨w, rfl⟩ := hx
    exact ⟨P0.ρ g w, Rep.hom_comm_apply β g w⟩))

/-- The inclusion of the image. -/
def imIncl {P0 P1 : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) : imRep β ⟶ P1 :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (imRep β).ρ) (σ := P1.ρ) (LinearMap.range β.hom.toLinearMap).subtype (fun _ _ => rfl))

/-- The corestriction of `β` to its image. -/
def imCorestr {P0 P1 : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) : P0 ⟶ imRep β :=
  Rep.ofHom ⟨LinearMap.codRestrict (LinearMap.range β.hom.toLinearMap) β.hom.toLinearMap
    (fun w => ⟨w, rfl⟩), fun g => by
      refine LinearMap.ext fun w => Subtype.ext ?_
      exact Rep.hom_comm_apply β g w⟩

theorem imCorestr_imIncl {P0 P1 : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) : imCorestr β ≫ imIncl β = β := rfl

theorem epi_imCorestr {P0 P1 : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) : Epi (imCorestr β) := by
  rw [Rep.epi_iff_surjective]
  intro x
  obtain ⟨w, hw⟩ := x.2
  exact ⟨w, Subtype.ext hw⟩

theorem mono_imIncl {P0 P1 : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) : Mono (imIncl β) := by
  rw [Rep.mono_iff_injective]
  exact Subtype.val_injective

variable {H : Type} [Group H] (φ ψ : H →* Γ)

/-- **Comparison theorem for the dual resolution (abstract form).**  Let `0 → P0 --β--> P1 --π--> X → 0` be an exact
sequence of `Γ`-representations with `Res_φ P0` and `Res_φ P1` projective over `H`, and `Ψ : Res_φ X → Res_ψ X` a morphism
of `H`-modules.  Then `Ψ` lifts to morphisms `s₁ : Res_φ P1 → Res_ψ P1`, `s₀ : Res_φ P0 → Res_ψ P0` of `H`-modules with
`π s₁ = Ψ π` (function order: `π_ψ ∘ s₁ = Ψ ∘ π_φ`) and `s₁ β = β s₀`. -/
theorem exists_comparison {P0 P1 X : Rep.{0} ℚ Γ} (β : P0 ⟶ P1) (π : P1 ⟶ X)
    (hπ : Function.Surjective π.hom) (hβπ : ∀ w, π.hom (β.hom w) = 0)
    (hex : ∀ x : P1, π.hom x = 0 → ∃ w, β.hom w = x)
    [Projective (Rep.res φ P1)] [Projective (Rep.res φ P0)]
    (Ψ : Rep.res φ X ⟶ Rep.res ψ X) :
    ∃ (s₁ : Rep.res φ P1 ⟶ Rep.res ψ P1) (s₀ : Rep.res φ P0 ⟶ Rep.res ψ P0),
      Rep.resMap φ π ≫ Ψ = s₁ ≫ Rep.resMap ψ π ∧ Rep.resMap φ β ≫ s₁ = s₀ ≫ Rep.resMap ψ β := by
  have hepi : Epi (Rep.resMap ψ π) := by
    rw [Rep.epi_iff_surjective]
    exact hπ
  obtain ⟨s₁, hs₁⟩ := Projective.factors (Rep.resMap φ π ≫ Ψ) (Rep.resMap ψ π)
  have hs₁' : ∀ x, π.hom (s₁.hom x) = Ψ.hom (π.hom x) := fun x => by
    have := congrArg (fun m => m.hom x) hs₁
    exact this
  -- the corestriction of `s₁ β` to the image of `β`
  let g' : Rep.res φ P0 ⟶ Rep.res ψ (imRep β) :=
    Rep.ofHom ⟨LinearMap.codRestrict (LinearMap.range β.hom.toLinearMap)
      (s₁.hom.toLinearMap ∘ₗ β.hom.toLinearMap) (fun w => by
        obtain ⟨v, hv⟩ := hex (s₁.hom (β.hom w)) (by
          rw [hs₁', hβπ, map_zero])
        exact ⟨v, hv⟩), fun h => by
      refine LinearMap.ext fun w => Subtype.ext ?_
      have h1 : s₁.hom (β.hom (P0.ρ (φ h) w)) = P1.ρ (ψ h) (s₁.hom (β.hom w)) := by
        rw [Rep.hom_comm_apply β (φ h) w]
        exact Rep.hom_comm_apply s₁ h _
      exact h1⟩
  have : Epi (Rep.resMap ψ (imCorestr β)) := by
    have := epi_imCorestr β
    rw [Rep.epi_iff_surjective] at this ⊢
    exact this
  obtain ⟨s₀, hs₀⟩ := Projective.factors g' (Rep.resMap ψ (imCorestr β))
  refine ⟨s₁, s₀, hs₁.symm, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  have h2 := congrArg (fun m => m.hom w) hs₀
  have h3 : (imIncl β).hom ((imCorestr β).hom (s₀.hom w)) = s₁.hom (β.hom w) := by
    have := congrArg (fun z => (imIncl β).hom z) h2
    exact this
  exact h3.symm

end Abstract


section Farey

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol

theorem piT_swapMap (c : PE) : piT.hom (swapMap.hom c) = - piT.hom c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, neg_add]
  | single q r =>
    rw [swapMap_single, piT_single, piT_single, edgeSym_swap, smul_neg]

/-- The dual boundary `β : P0 → P1` with values in the antisymmetric chains. -/
def betaF : P0 ⟶ P1 :=
  Rep.ofHom ⟨LinearMap.codRestrict antiSub bdryMap.hom.toLinearMap bdryMap_mem_antiSub, fun g => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact Rep.hom_comm_apply bdryMap g w⟩

theorem betaF_incl (w : P0) : ((betaF.hom w : P1) : PE) = bdryMap.hom w := rfl

/-- The symbol map on the antisymmetric edge chains. -/
def piF : P1 ⟶ StD := inclP1 ≫ piT

theorem piF_apply (x : P1) : piF.hom x = piT.hom (x : PE) := rfl

theorem piF_surjective : Function.Surjective piF.hom := by
  intro σ
  obtain ⟨c, hc⟩ := piT_surjective σ
  refine ⟨⟨antiLin c, antiLin_mem c⟩, ?_⟩
  rw [piF_apply]
  change piT.hom (antiLin c) = σ
  rw [antiLin_apply, map_smul, map_sub, piT_swapMap, hc]
  have : ((1 / 2 : ℚ) • (σ - -σ)) = σ := by module
  exact this

theorem piF_betaF (w : P0) : piF.hom (betaF.hom w) = 0 := by
  rw [piF_apply]
  change piT.hom (bdryMap.hom w) = 0
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | single t r => rw [bdryMap_single, map_smul, piT_bdryV, smul_zero]

theorem exact_betaF (x : P1) (hx : piF.hom x = 0) : ∃ w, betaF.hom w = x := by
  obtain ⟨w, hw⟩ := exists_bdry_preimage (x : PE) x.2 hx
  exact ⟨w, Subtype.ext hw⟩


variable (p : ℕ) [Fact p.Prime]

theorem detQ_binDatum_f (s : (binDatum p).S) : detQ ((binDatum p).f s) = detQ s.1 := by
  have hdvd := (mem_commSubgroup_C1 p s.1).mp s.2
  obtain ⟨b, hb⟩ := hdvd
  have hp := p_ne_zero_int (p := p)
  have hv := binDatum_f_val p s
  have e00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 0) hv
  have e01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 1) hv
  have e10 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 1 0) hv
  have e11 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 1 1) hv
  simp only [cjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  rw [detQ_eq, detQ_eq]
  change ((((binDatum p).f s).val 0 0 * ((binDatum p).f s).val 1 1 -
      ((binDatum p).f s).val 0 1 * ((binDatum p).f s).val 1 0 : ℤ) : ℚ) = _
  rw [e00, e01, e10, e11, hb, Int.mul_ediv_cancel_left _ hp]
  push_cast
  ring


/-- **The symbol-level correspondence** `σ ↦ C₁⁻¹ σ` on the Steinberg module, as a morphism of `S`-modules
`Res_f St^δ → Res_S St^δ`. -/
def PsiG : Rep.res (binDatum p).f StD ⟶ Rep.res (binDatum p).S.subtype StD :=
  Rep.ofHom ⟨action (C1 p)⁻¹, fun s => by
    refine LinearMap.ext fun σ => ?_
    change action (C1 p)⁻¹ (stD ((binDatum p).f s) σ) = stD s.1 (action (C1 p)⁻¹ σ)
    have hf := (binDatum p).hf s
    rw [stD_apply, stD_apply, map_smul, detQ_binDatum_f]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    change (C1 p)⁻¹ * binIota ((binDatum p).f s) = binIota s.1 * (C1 p)⁻¹
    rw [hf]
    group⟩

theorem PsiG_apply (σ : St) : (PsiG p).hom σ = action (C1 p)⁻¹ σ := rfl


/-- **L3 (comparison theorem).**  The symbol-level correspondence `Ψ = C₁⁻¹ ·` on the Steinberg module lifts to the dual Farey
tree resolution `0 → P0 → P1 → St^δ → 0` by `S`-equivariant maps `s₁ : Res_f P1 → Res_S P1`, `s₀ : Res_f P0 → Res_S P0`
(`π s₁ = Ψ π`, `s₁ β = β s₀`). -/
theorem farLift_exists :
    ∃ (s₁ : Rep.res (binDatum p).f P1 ⟶ Rep.res (binDatum p).S.subtype P1)
      (s₀ : Rep.res (binDatum p).f P0 ⟶ Rep.res (binDatum p).S.subtype P0),
      Rep.resMap (binDatum p).f piF ≫ PsiG p = s₁ ≫ Rep.resMap (binDatum p).S.subtype piF ∧
      Rep.resMap (binDatum p).f betaF ≫ s₁ = s₀ ≫ Rep.resMap (binDatum p).S.subtype betaF := by
  have : Projective (Rep.res (binDatum p).f P1) := binDatum_hproj p 1
  have : Projective (Rep.res (binDatum p).f P0) := binDatum_hproj p 0
  exact exists_comparison (binDatum p).f (binDatum p).S.subtype betaF piF piF_surjective piF_betaF
    exact_betaF (PsiG p)


section DualLiftData

open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

/-- **L3** (`BridgeInterface.L3`): the dual lift exists. -/
theorem L3_holds : L3 p := by
  obtain ⟨s₁, s₀, h1, h0⟩ := farLift_exists p
  refine ⟨⟨s₀.hom.toLinearMap, s₁.hom.toLinearMap, fun σ x => ?_, fun σ x => ?_, fun t => ?_, fun x => ?_⟩⟩
  · exact Rep.hom_comm_apply s₀ σ x
  · exact Rep.hom_comm_apply s₁ σ x
  · have := congrArg (fun m => m.hom t) h0
    exact this.symm
  · have := congrArg (fun m => m.hom x) h1
    exact this.symm

end DualLiftData

end Farey

end TernaryPeriodPolynomials.Argument.HeckeNormalization
