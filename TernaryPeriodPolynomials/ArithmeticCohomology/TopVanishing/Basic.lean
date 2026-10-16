module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.CupProduct
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section


/-!
# Free resolutions by permutation modules and top-degree vanishing

Chains on a set with an action of a group `Λ` are finitely supported complex functions, on which
`Λ` acts by translating the support. A chain complex of such permutation modules is a free
resolution of `ℂ` of length `N` when it is augmented by a single point in index `0`, the action on
every other index is free, it is exact, and it has no cells beyond index `N + 1` (index `j + 1`
carries the cells of dimension `j`). The homogeneous-model statement `H⁴(Λ, ℂ) = 0` for a subgroup
`Λ` of a group `G` (vertices in `G`) is `IsTopVanishing Λ`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

open TernaryPeriodPolynomials.Duality

section Chains

variable (Λ : Type) [Group Λ]

/-- The translation of finitely supported chains on a `Λ`-set. -/
def chainAct {S : Type} [MulAction Λ S] (γ : Λ) : (S →₀ ℂ) →ₗ[ℂ] (S →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun s => γ • s)

/-- A linear map of chains commuting with all translations. -/
def Equivariant {S T : Type} [MulAction Λ S] [MulAction Λ T]
    (F : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)) : Prop :=
  ∀ γ : Λ, F ∘ₗ chainAct Λ γ = chainAct Λ γ ∘ₗ F

variable {Λ}

@[simp] theorem chainAct_single {S : Type} [MulAction Λ S] (γ : Λ) (s : S) (a : ℂ) :
    chainAct Λ γ (Finsupp.single s a) = Finsupp.single (γ • s) a := by
  rw [chainAct, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem chainAct_mul {S : Type} [MulAction Λ S] (γ δ : Λ) :
    chainAct Λ (γ * δ) = chainAct Λ γ ∘ₗ chainAct (S := S) Λ δ := by
  apply Finsupp.lhom_ext
  intro s a
  simp [mul_smul]

theorem chainAct_one {S : Type} [MulAction Λ S] : chainAct (S := S) Λ 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  simp

/-- Equivariance can be checked on basis chains. -/
theorem equivariant_of_single {S T : Type} [MulAction Λ S] [MulAction Λ T]
    {F : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)}
    (h : ∀ (γ : Λ) (s : S), F (Finsupp.single (γ • s) 1) = chainAct Λ γ (F (Finsupp.single s 1))) :
    Equivariant Λ F := by
  intro γ
  apply Finsupp.lhom_ext
  intro s a
  have hs : Finsupp.single s a = a • Finsupp.single s (1 : ℂ) := by simp
  have hs' : Finsupp.single (γ • s) a = a • Finsupp.single (γ • s) (1 : ℂ) := by simp
  simp only [LinearMap.comp_apply, chainAct_single]
  rw [hs, hs']
  simp only [map_smul, h]

theorem Equivariant.apply {S T : Type} [MulAction Λ S] [MulAction Λ T]
    {F : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)} (h : Equivariant Λ F) (γ : Λ) (v : S →₀ ℂ) :
    F (chainAct Λ γ v) = chainAct Λ γ (F v) :=
  LinearMap.congr_fun (h γ) v

theorem equivariant_id {S : Type} [MulAction Λ S] :
    Equivariant Λ (LinearMap.id : (S →₀ ℂ) →ₗ[ℂ] (S →₀ ℂ)) := fun γ => by
  rw [LinearMap.id_comp, LinearMap.comp_id]

theorem equivariant_zero {S T : Type} [MulAction Λ S] [MulAction Λ T] :
    Equivariant Λ (0 : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)) := fun γ => by
  rw [LinearMap.zero_comp, LinearMap.comp_zero]

theorem Equivariant.comp {S T U : Type} [MulAction Λ S] [MulAction Λ T] [MulAction Λ U]
    {F : (T →₀ ℂ) →ₗ[ℂ] (U →₀ ℂ)} {E : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)}
    (hF : Equivariant Λ F) (hE : Equivariant Λ E) : Equivariant Λ (F ∘ₗ E) := fun γ =>
  LinearMap.ext fun v => by simp only [LinearMap.comp_apply, hE.apply, hF.apply]

theorem Equivariant.sub {S T : Type} [MulAction Λ S] [MulAction Λ T]
    {F E : (S →₀ ℂ) →ₗ[ℂ] (T →₀ ℂ)}
    (hF : Equivariant Λ F) (hE : Equivariant Λ E) : Equivariant Λ (F - E) := fun γ =>
  LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, hF.apply, hE.apply, map_sub]

end Chains

/-- A chain complex of permutation modules: index `k + 1` maps to index `k`. -/
structure PermutationComplex (Λ : Type) [Group Λ] where
  /-- The cells in each index. -/
  cell : ℕ → Type
  /-- The action on the cells. -/
  [action : ∀ k, MulAction Λ (cell k)]
  /-- The boundary from index `k + 1` to index `k`. -/
  d : ∀ k, (cell (k + 1) →₀ ℂ) →ₗ[ℂ] (cell k →₀ ℂ)
  equivariant : ∀ k, Equivariant Λ (d k)
  d_comp_d : ∀ k, d k ∘ₗ d (k + 1) = 0

attribute [instance] PermutationComplex.action

namespace PermutationComplex

variable {Λ : Type} [Group Λ] (C : PermutationComplex Λ)

/-- Exactness of the augmented complex: the augmentation is onto and every cycle bounds. -/
def Exact : Prop :=
  LinearMap.range (C.d 0) = ⊤ ∧ ∀ k, LinearMap.ker (C.d k) ≤ LinearMap.range (C.d (k + 1))

/-- The action on the cells of every positive index is free. -/
def Free : Prop :=
  ∀ k (γ : Λ) (s : C.cell (k + 1)), γ • s = s → γ = 1

end PermutationComplex

/-- A free resolution of `ℂ` of length `N` by permutation modules: a single augmentation point in
index `0`, free actions in positive indices, exactness, and no cells of dimension `N + 1`
(index `N + 2`). It is the augmented cellular chain complex of an `N`-dimensional acyclic complex
with a free cellular action. -/
structure FreeResolution (Λ : Type) [Group Λ] (N : ℕ) extends PermutationComplex Λ where
  [point : Unique (cell 0)]
  free : toPermutationComplex.Free
  exact : toPermutationComplex.Exact
  top : IsEmpty (cell (N + 2))

/-- `H⁴(Λ, ℂ) = 0` in the homogeneous model with vertices in `G`: every invariant scalar
four-cocycle is the coboundary of an invariant scalar three-cochain. -/
def IsTopVanishing {G : Type} [Group G] (Λ : Subgroup G) : Prop :=
  ∀ f : (Fin 5 → G) → ℂ, (∀ (γ : Λ) x, f (fun i => γ.val * x i) = f x) →
    (∀ x, differentialFourRaw f x = 0) →
    ∃ θ : (Fin 4 → G) → ℂ, (∀ (γ : Λ) x, θ (fun i => γ.val * x i) = θ x) ∧
      ∀ x, differentialThreeRaw θ x = f x

end TernaryPeriodPolynomials.TopVanishing
