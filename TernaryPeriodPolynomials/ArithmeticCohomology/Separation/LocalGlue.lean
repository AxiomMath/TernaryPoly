module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Interface

@[expose] public section



/-!
# Glue for the local half: from an injective Hecke-equivariant model to `LocalUpperBound`

The local cusp computations produce an injective linear map `E` from the
local cohomology `H²(Γ_F, V)` into a model space `M` (an `H¹` of the Levi, or a space of classical
cusp forms) under which each local away-three Hecke operator becomes an affine expression
`α • 1 + β • T` in a model operator `T`. This file turns such data into `LocalUpperBound`:
the local joint generalized eigenspace embeds into the joint generalized eigenspace of the model
operators for the transformed character `(c t - α) / β`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral.CuspReduction

namespace TernaryPeriodPolynomials.Separation

section Generic

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- Affine reparametrization of generalized eigenspaces. -/
theorem maxGenEigenspace_affine (T : Module.End ℂ M) (α β μ : ℂ) (hβ : β ≠ 0) :
    (α • 1 + β • T).maxGenEigenspace μ = T.maxGenEigenspace ((μ - α) / β) := by
  have key : α • (1 : Module.End ℂ M) + β • T - μ • 1 = β • (T - ((μ - α) / β) • 1) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hβ, sub_smul]
    abel
  ext v
  simp only [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [key, smul_pow, LinearMap.smul_apply] at hk
    exact (smul_eq_zero.mp hk).resolve_left (pow_ne_zero _ hβ)
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [key, smul_pow, LinearMap.smul_apply, hk, smul_zero]

/-- An intertwining map sends generalized eigenvectors to generalized eigenvectors. -/
theorem map_mem_maxGenEigenspace (E : M →ₗ[ℂ] N) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (h : ∀ x, E (A x) = B (E x)) (μ : ℂ) {x : M} (hx : x ∈ A.maxGenEigenspace μ) :
    E x ∈ B.maxGenEigenspace μ :=
  intertwine_mem_maxGenEigenspace E A B h μ hx

end Generic

variable {n : ℕ}

/-- The local joint generalized eigenspace is contained in the joint generalized eigenspace of any
subfamily of the local operators. -/
theorem localJoint_le_subfamily (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) {ι : Type*} (τ : ι → {t : HeckeCorrespondence // AwayThree t}) :
    localJoint n χ c side good ≤
      ⨅ i, (localOp n χ (τ i).1 (τ i).2 side good).maxGenEigenspace (c (τ i).1) := by
  intro y hy
  simp only [localJoint, Submodule.mem_iInf] at hy ⊢
  exact fun i => hy (τ i)

/-- **Model embedding.** Let `E : H²(Γ_F, V) → M` be injective, and for a family `τ` of away-three
correspondences let `E ∘ localOp (τ i) = (α i • 1 + β i • T i) ∘ E` with `β i ≠ 0`. Then `E` maps
the local joint generalized eigenspace of `c` into the joint generalized eigenspace of the `T i`
for the character `(c (τ i) - α i) / β i`. -/
theorem map_localJoint_le (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : CuspH2 n χ side good →ₗ[ℂ] M) {ι : Type*}
    (τ : ι → {t : HeckeCorrespondence // AwayThree t}) (T : ι → Module.End ℂ M) (α β : ι → ℂ)
    (hβ : ∀ i, β i ≠ 0)
    (hE : ∀ i x, E (localOp n χ (τ i).1 (τ i).2 side good x) = (α i • 1 + β i • T i) (E x)) :
    (localJoint n χ c side good).map E ≤
      ⨅ i, (T i).maxGenEigenspace ((c (τ i).1 - α i) / β i) := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [Submodule.mem_iInf]
  intro i
  rw [← maxGenEigenspace_affine (T i) (α i) (β i) _ (hβ i)]
  exact map_mem_maxGenEigenspace E _ _ (hE i) _
    ((Submodule.mem_iInf _).mp (localJoint_le_subfamily χ c side good τ hy) i)

/-- **`LocalUpperBound` from a model.** Under the hypotheses of `map_localJoint_le`, if the model
joint generalized eigenspace is finite-dimensional of dimension at most `m`, the local upper
bound holds with multiplicity `m`. -/
theorem localUpperBound_of_model (χ : RankOneCharacter) (c : HeckeCorrespondence → ℂ)
    (side : Side) (good : Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : CuspH2 n χ side good →ₗ[ℂ] M) (hinj : Function.Injective E) {ι : Type*}
    (τ : ι → {t : HeckeCorrespondence // AwayThree t}) (T : ι → Module.End ℂ M) (α β : ι → ℂ)
    (hβ : ∀ i, β i ≠ 0)
    (hE : ∀ i x, E (localOp n χ (τ i).1 (τ i).2 side good x) = (α i • 1 + β i • T i) (E x))
    (m : ℕ)
    [hfin : FiniteDimensional ℂ
      ↥(⨅ i, (T i).maxGenEigenspace ((c (τ i).1 - α i) / β i) : Submodule ℂ M)]
    (hm : Module.finrank ℂ
      ↥(⨅ i, (T i).maxGenEigenspace ((c (τ i).1 - α i) / β i) : Submodule ℂ M) ≤ m) :
    LocalUpperBound n χ c side good m := by
  set W : Submodule ℂ M := ⨅ i, (T i).maxGenEigenspace ((c (τ i).1 - α i) / β i)
  have hle := map_localJoint_le χ c side good E τ T α β hβ hE
  -- the restriction of `E` to the local joint eigenspace, landing in `W`
  let F : localJoint n χ c side good →ₗ[ℂ] W :=
    { toFun := fun y => ⟨E y.1, hle ⟨y.1, y.2, rfl⟩⟩
      map_add' := fun y y' => by ext; simp
      map_smul' := fun a y => by ext; simp }
  have hF : Function.Injective F := by
    intro y y' h
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val h
  have : FiniteDimensional ℂ (localJoint n χ c side good) :=
    Module.Finite.of_injective F hF
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_injective hF).trans hm⟩

/-- Multiplicity one from a model: if the model joint generalized eigenspace has dimension at
most one, local multiplicity one holds. -/
theorem localMultiplicityOne_of_localUpperBound_one (χ : RankOneCharacter)
    (c : HeckeCorrespondence → ℂ) (side : Side) (good : Bool)
    (h : LocalUpperBound n χ c side good 1) : LocalMultiplicityOne n χ c side good := by
  obtain ⟨hfin, hdim⟩ := h
  intro y hy y' hy' hy0
  have hyL : (⟨y, hy⟩ : localJoint n χ c side good) ≠ 0 := by
    intro h0
    exact hy0 (congrArg Subtype.val h0)
  have hfree : Module.Free ℂ (localJoint n χ c side good) := Module.Free.of_divisionRing ℂ _
  have : Module.IsTorsionFree ℂ (localJoint n χ c side good) :=
    Module.Free.instIsTorsionFree ℂ _
  have hpos : 0 < Module.finrank ℂ (localJoint n χ c side good) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hyL⟩
  have h1 : Module.finrank ℂ (localJoint n χ c side good) = 1 := by omega
  have hone := (finrank_eq_one_iff_of_nonzero' (K := ℂ)
    (⟨y, hy⟩ : localJoint n χ c side good) hyL).mp h1
  obtain ⟨z, hz⟩ := hone ⟨y', hy'⟩
  exact ⟨z, (congrArg Subtype.val hz).symm⟩

end TernaryPeriodPolynomials.Separation
