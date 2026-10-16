module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Cohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Cusp

@[expose] public section


/-!
# The Kronecker pairing between Mathlib's group cohomology and homology, through the two bridges

Formalized by Claude Sonnet 5.5.

Mathlib has no pairing `H^n(Λ, ℂ) × H_n(Λ, ℂ) → ℂ`.  Here it is defined from the two class maps
`cohClass` (invariant cocycles → `groupCohomology`) and `bridgeClass` (cycles modulo null chains →
`groupHomology`), both surjective: `kron Λ j : H^{j+1}(Λ, ℂ) →ₗ Dual H_{j+1}(Λ, ℂ)` is the unique
bilinear form with `kron (cohClass F) (bridgeClass c) = ∑ c(x) F(x)` (`kron_class`).  It is well defined because an
invariant function pairs to zero with null chains and boundaries are killed by cocycles (`pairModel_bdry`,
`pairModel_coboundary`).  `kron_res_cor` is the adjunction between Mathlib's restriction of cohomology and
corestriction of homology for `Λ' ≤ Λ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation MonoidalCategory Rep
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains eval_null)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (BdryChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains leftTranslate)
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)

section Descent

variable {A B C : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

/-- Descent of a linear map along a surjection whose kernel it kills. -/
def descend (f : A →ₗ[ℂ] B) (hf : Function.Surjective f) (g : A →ₗ[ℂ] C)
    (h : ∀ a, f a = 0 → g a = 0) : B →ₗ[ℂ] C :=
  (Submodule.liftQ (LinearMap.ker f) g (fun a ha => h a ha)) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective f hf).symm.toLinearMap

theorem descend_apply (f : A →ₗ[ℂ] B) (hf : Function.Surjective f) (g : A →ₗ[ℂ] C)
    (h : ∀ a, f a = 0 → g a = 0) (a : A) : descend f hf g h (f a) = g a := by
  unfold descend
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have : (LinearMap.quotKerEquivOfSurjective f hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this]
  rfl

end Descent

variable {G : Type} [Group G]

theorem lc_boundary (Λ : Subgroup G) (j : ℕ) (F : Inv Λ j) (b : Chains G (j + 1)) :
    Finsupp.linearCombination ℂ F.1 (homogeneousBoundary (j + 1) b) =
      Finsupp.linearCombination ℂ (dInv Λ j F).1 b := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single x r =>
    rw [show (Finsupp.single x r : Chains G (j + 1)) = r • Finsupp.single x (1 : ℂ) by simp,
      map_smul, map_smul, map_smul]
    rw [Finsupp.linearCombination_single, one_smul, dInv_apply]

section Pairing

variable (Λ : Subgroup G) (j : ℕ)

/-- The Kronecker pairing of an invariant cocycle with a cycle modulo null chains, on representatives. -/
def pairModel : cohCycles Λ j →ₗ[ℂ] Zhom Λ j →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun F c => Finsupp.linearCombination ℂ F.1.1 c.1)
    (fun F F' c => by
      simp [Finsupp.linearCombination_apply, Finsupp.sum, mul_add, Finset.sum_add_distrib])
    (fun a F c => by
      simp [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, mul_left_comm])
    (fun F c c' => by simp)
    (fun a F c => by simp)

theorem pairModel_apply (F : cohCycles Λ j) (c : Zhom Λ j) :
    pairModel Λ j F c = Finsupp.linearCombination ℂ F.1.1 c.1 := rfl

theorem lc_null (F : Inv Λ j) {c : Chains G j} (hc : c ∈ NullChains Λ j) :
    Finsupp.linearCombination ℂ F.1 c = 0 :=
  eval_null F.1 (fun γ x => F.2 γ.1 γ.2 x) hc

theorem pairModel_bdry (F : cohCycles Λ j) (c : Zhom Λ j)
    (hc : (c : Chains G (j + 1)) ∈ BdryChains Λ (j + 1)) : pairModel Λ j F c = 0 := by
  obtain ⟨n, hn, b, ⟨d, rfl⟩, hnb⟩ := Submodule.mem_sup.mp hc
  rw [pairModel_apply, ← hnb, map_add, lc_null Λ (j + 1) F.1 hn, zero_add,
    lc_boundary, (mem_cohCycles Λ j F.1).mp F.2]
  simp

theorem pairModel_coboundary (F : cohCycles Λ j) (hF : F.1 ∈ LinearMap.range (dInv Λ j))
    (c : Zhom Λ j) : pairModel Λ j F c = 0 := by
  obtain ⟨E, hE⟩ := hF
  rw [pairModel_apply, ← hE, ← lc_boundary]
  exact lc_null Λ j E ((mem_Zhom Λ j c.1).mp c.2)

end Pairing

section Kronecker

variable (Λ : Subgroup G) (j : ℕ)

/-- Mathlib group homology in degree `j + 1` with trivial coefficients. -/
abbrev HomL : Type := groupHomology (Rep.res Λ.subtype (triv (G := G))) (j + 1)

/-- Mathlib group cohomology in degree `j + 1` with trivial coefficients. -/
abbrev CohL : Type := groupCohomology (Rep.trivial ℂ Λ ℂ) (j + 1)

/-- The functionals on cycles that kill `ker bridgeClass`. -/
theorem pairModel_kills_ker (F : cohCycles Λ j) (c : Zhom Λ j) (hc : bridgeClass Λ j c = 0) :
    pairModel Λ j F c = 0 :=
  pairModel_bdry Λ j F c ((bridgeClass_eq_zero_iff Λ j c).mp hc)

/-- The pairing of a cohomology class with cycles modulo null chains (on representatives). -/
def kronModel : CohL Λ j →ₗ[ℂ] Module.Dual ℂ (Zhom Λ j) :=
  descend (A := cohCycles Λ j) (B := CohL Λ j) (C := Module.Dual ℂ (Zhom Λ j)) (cohClass Λ j)
    (cohClass_surjective Λ j) (pairModel Λ j) (fun F hF =>
      LinearMap.ext fun c => pairModel_coboundary Λ j F ((cohClass_eq_zero_iff Λ j F).mp hF) c)

theorem kronModel_cohClass (F : cohCycles Λ j) : kronModel Λ j (cohClass Λ j F) = pairModel Λ j F :=
  descend_apply _ _ _ _ _

theorem kronModel_mem (α : CohL Λ j) :
    kronModel Λ j α ∈ LinearMap.range (bridgeClass Λ j).dualMap := by
  obtain ⟨F, rfl⟩ := cohClass_surjective Λ j α
  let ψ : HomL Λ j →ₗ[ℂ] ℂ := descend (A := Zhom Λ j) (B := HomL Λ j) (C := ℂ) (bridgeClass Λ j)
    (bridgeClass_surjective Λ j) (pairModel Λ j F)
    (fun c hc => pairModel_kills_ker Λ j F c hc)
  refine ⟨ψ, ?_⟩
  apply LinearMap.ext
  intro c
  have h1 : ψ (bridgeClass Λ j c) = pairModel Λ j F c := descend_apply _ _ _ _ _
  change ψ (bridgeClass Λ j c) = kronModel Λ j (cohClass Λ j F) c
  rw [h1, kronModel_cohClass]

/-- The Kronecker pairing `H^{j+1}(Λ, ℂ) × H_{j+1}(Λ, ℂ) → ℂ`, defined through the two bridges. -/
def kron : CohL Λ j →ₗ[ℂ] Module.Dual ℂ (HomL Λ j) :=
  (LinearEquiv.ofInjective (bridgeClass Λ j).dualMap
    (LinearMap.dualMap_injective_of_surjective (bridgeClass_surjective Λ j))).symm.toLinearMap ∘ₗ
    (kronModel Λ j).codRestrict (LinearMap.range (bridgeClass Λ j).dualMap) (kronModel_mem Λ j)

theorem kron_bridge (α : CohL Λ j) (c : Zhom Λ j) :
    kron Λ j α (bridgeClass Λ j c) = kronModel Λ j α c := by
  have e := (LinearEquiv.ofInjective (bridgeClass Λ j).dualMap
    (LinearMap.dualMap_injective_of_surjective (bridgeClass_surjective Λ j))).apply_symm_apply
    ((kronModel Λ j).codRestrict (LinearMap.range (bridgeClass Λ j).dualMap) (kronModel_mem Λ j) α)
  have e' := congrArg (fun (t : ↥(LinearMap.range (bridgeClass Λ j).dualMap)) =>
    (t.1 : Module.Dual ℂ (Zhom Λ j)) c) e
  exact e'

/-- **Kronecker compatibility**: the pairing of the Mathlib classes of an invariant cocycle `F` and of a cycle
`c` modulo null chains is the pairing of the representatives, `∑ c(x) F(x)`. -/
theorem kron_class (F : cohCycles Λ j) (c : Zhom Λ j) :
    kron Λ j (cohClass Λ j F) (bridgeClass Λ j c) = Finsupp.linearCombination ℂ F.1.1 c.1 := by
  rw [kron_bridge, kronModel_cohClass]
  rfl

theorem kron_res_cor {Λ' Λ : Subgroup G} (h : Λ' ≤ Λ) (j : ℕ) (α : CohL Λ j) (β : HomL Λ' j) :
    kron Λ' j ((groupCohomology.map (Subgroup.inclusion h) (phiCoh h) (j + 1)).hom α) β =
      kron Λ j α ((groupHomology.map (Subgroup.inclusion h) (phiInc h) (j + 1)).hom β) := by
  obtain ⟨F, rfl⟩ := cohClass_surjective Λ j α
  obtain ⟨c, rfl⟩ := bridgeClass_surjective Λ' j β
  have h1 := cohClass_res h j F
  have h2 := bridgeClass_natural h j c
  have k1 := kron_class Λ' j ⟨restrInv h (j + 1) F.1, restrInv_mem_cohCycles h j F⟩ c
  have k2 := kron_class Λ j F ⟨c.1, Zhom_mono h j c.2⟩
  rw [h1, h2]
  exact k1.trans k2.symm

end Kronecker

end TernaryPeriodPolynomials.Argument.HomologyBridge
