module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Cover
public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.TrivialTensor
public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.StdCoinvariants
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent

@[expose] public section


/-!
# Homology bridge: homogeneous chains modulo null chains versus Mathlib's `groupHomology`

Formalized by Claude Sonnet 5.5.

For a group `G` (ambient vertices, e.g. `GL₃(ℚ)`) and a subgroup `Λ ≤ G`, the homogeneous chains
`Chains G k = ((Fin (k+1) → G) →₀ ℂ)` with the alternating boundary compute `H_k(Λ, ℂ)` after dividing
by the null chains `NullChains Λ k` (spans of `γ·x - x`): in degree `j + 1` the homogeneous cycles
modulo null chains `Zhom Λ j = {c | ∂c ∈ NullChains Λ j}` map onto `H_{j+1}(Λ, ℂ)` (Mathlib's
`groupHomology (Rep.trivial ℂ Λ ℂ) (j+1)`) by `bridgeClass`, and `bridgeClass c = bridgeClass d` iff
`c - d` is null plus a boundary (`bridgeClass_eq_iff`).  The proof is Mathlib's
`groupHomologyIso` for the bar resolution of `G` restricted to `Λ`, the chain
isomorphism with the standard (homogeneous) resolution, and the covering lemma `coverClass`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation MonoidalCategory
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains)

variable {G : Type} [Group G] (Λ : Subgroup G)

/-- The trivial representation. -/
abbrev triv : Rep ℂ G := Rep.trivial ℂ G ℂ

/-- `A ⊗ std`. -/
abbrev Ystd : ChainComplex (Rep ℂ G) ℕ :=
  ((tensorLeft (triv (G := G))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Rep.standardComplex ℂ G)

/-- The `Λ`-coinvariant complex of `A ⊗ std`. -/
abbrev Cstd : ChainComplex (ModuleCat ℂ) ℕ :=
  ((cN (k := ℂ) Λ).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Ystd (G := G))

example (n : ℕ) : ((Cstd Λ).X n : Type) = Coinvariants
    (((Representation.trivial ℂ G ℂ).tprod (Xstd (G := G) n).ρ).comp Λ.subtype) := by
  unfold Cstd Ystd
  rfl

/-- The covering of the coinvariant complex by homogeneous chains: `c ↦ [1 ⊗ c]`. -/
def sigma (n : ℕ) : Chains G n →ₗ[ℂ] ↑((Cstd Λ).X n) :=
  (toTensor Λ (Xstd (G := G) n).ρ) ∘ₗ
    (Coinvariants.mk ((Xstd (G := G) n).ρ.comp Λ.subtype)) ∘ₗ (toMA n).toLinearMap

theorem sigma_apply (n : ℕ) (c : Chains G n) :
    sigma Λ n c = toTensor Λ (Xstd (G := G) n).ρ
      (Coinvariants.mk ((Xstd (G := G) n).ρ.comp Λ.subtype) (toMA n c)) := rfl

theorem sigma_surjective (n : ℕ) : Function.Surjective (sigma Λ n) := by
  intro y
  obtain ⟨v, hv⟩ := Coinvariants.mk_surjective _ (fromTensor Λ (Xstd (G := G) n).ρ y)
  refine ⟨(toMA n).symm v, ?_⟩
  rw [sigma_apply, LinearEquiv.apply_symm_apply, hv]
  exact toTensor_fromTensor Λ (Xstd (G := G) n).ρ y

theorem sigma_eq_zero_iff (n : ℕ) (c : Chains G n) : sigma Λ n c = 0 ↔ c ∈ NullChains Λ n := by
  have h0 : sigma Λ n c = 0 ↔
      Coinvariants.mk ((Xstd (G := G) n).ρ.comp Λ.subtype) (toMA n c) = 0 := by
    constructor
    · intro h
      have := congrArg (fromTensor Λ (Xstd (G := G) n).ρ) h
      rw [sigma_apply, fromTensor_toTensor] at this
      exact this.trans (map_zero _)
    · intro h
      rw [sigma_apply, h]
      exact map_zero _
  rw [h0, Coinvariants.mk_eq_zero, ker_eq_null]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have : d = c := (toMA n).injective hdc
    rw [← this]; exact hd
  · intro hc
    exact ⟨c, hc, rfl⟩

theorem toMA_boundary_lin (n : ℕ) :
    (Rep.standardComplex.d ℂ G (n + 1)) ∘ₗ (toMA (n + 1)).toLinearMap =
      (toMA n).toLinearMap ∘ₗ
        TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (G := G) (n + 1) := by
  apply Finsupp.lhom_ext
  intro x r
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, toMA_single]
  rw [Rep.standardComplex.d_single]
  rw [show Finsupp.single x r = r • Finsupp.single x (1 : ℂ) by simp, map_smul,
    TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary_single]
  rw [map_smul, map_sum]
  refine Eq.trans ?_ (Finset.smul_sum ..).symm
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, toMA_single, smul_smul, MonoidAlgebra.smul_single]
  simp [mul_comm]

theorem toMA_boundary (n : ℕ) (c : Chains G (n + 1)) :
    ((Rep.standardComplex ℂ G).d (n + 1) n).hom (toMA (n + 1) c) =
      toMA n (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (n + 1) c) := by
  rw [Rep.standardComplex.d_apply]
  exact LinearMap.congr_fun (toMA_boundary_lin n) c

theorem sigma_d (n : ℕ) (c : Chains G (n + 1)) :
    (Cstd Λ).d (n + 1) n (sigma Λ (n + 1) c) =
      sigma Λ n (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (n + 1) c) := by
  rw [sigma_apply, sigma_apply, ← toMA_boundary]
  have key : ∀ m : MonoidAlgebra ℂ (Fin (n + 1 + 1) → G),
      (Cstd Λ).d (n + 1) n (toTensor Λ (Xstd (G := G) (n + 1)).ρ
        (Coinvariants.mk ((Xstd (G := G) (n + 1)).ρ.comp Λ.subtype) m)) =
      toTensor Λ (Xstd (G := G) n).ρ (Coinvariants.mk ((Xstd (G := G) n).ρ.comp Λ.subtype)
        (((Rep.standardComplex ℂ G).d (n + 1) n).hom m)) := by
    intro m
    rfl
  exact key _

/-- The comparison of the standard-resolution coinvariant complex with the bar-resolution one. -/
def isoCx : Cstd (G := G) Λ ≅ CxN Λ (YA (triv (G := G))) :=
  ((cN (k := ℂ) Λ).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
    (((tensorLeft (triv (G := G))).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (Rep.barComplex.isoStandardComplex ℂ G).symm)

/-- Group homology with trivial coefficients as the homology of the standard coinvariant complex. -/
def gIso (n : ℕ) : groupHomology (Rep.res Λ.subtype (triv (G := G))) n ≅ (Cstd Λ).homology n :=
  eN Λ (triv (G := G)) n ≪≫ (HomologicalComplex.homologyMapIso (isoCx Λ) n).symm

/-- The short complex around degree `j + 1`. -/
abbrev Sj (j : ℕ) : ShortComplex (ModuleCat ℂ) := (Cstd (G := G) Λ).sc' (j + 2) (j + 1) j

/-- `H_{j+1}` of the standard coinvariant complex is the homology of the short complex around it. -/
def homIsoSj (j : ℕ) : (Cstd (G := G) Λ).homology (j + 1) ≅ (Sj Λ j).homology :=
  HomologicalComplex.homologyIsoSc' _ (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
    (ChainComplex.next_nat_succ j)

open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)

theorem sj_h₁ (j : ℕ) (m : Chains G (j + 2)) :
    (Sj Λ j).f.hom (sigma Λ (j + 2) m) = sigma Λ (j + 1) (homogeneousBoundary (j + 2) m) :=
  sigma_d Λ (j + 1) m

theorem sj_h₂ (j : ℕ) (m : Chains G (j + 1)) :
    (Sj Λ j).g.hom (sigma Λ (j + 1) m) = sigma Λ j (homogeneousBoundary (j + 1) m) :=
  sigma_d Λ j m

/-- Homogeneous cycles modulo null chains in degree `j + 1`. -/
def Zhom (j : ℕ) : Submodule ℂ (Chains G (j + 1)) :=
  coverCycles (Sj Λ j) (sigma Λ j) (homogeneousBoundary (j + 1))

theorem mem_Zhom (j : ℕ) (c : Chains G (j + 1)) :
    c ∈ Zhom Λ j ↔ homogeneousBoundary (j + 1) c ∈ NullChains Λ j := by
  change sigma Λ j (homogeneousBoundary (j + 1) c) = 0 ↔ _
  exact sigma_eq_zero_iff Λ j _

/-- The class of a homogeneous cycle modulo null chains in group homology (Mathlib). -/
def bridgeClass (j : ℕ) : Zhom Λ j →ₗ[ℂ] groupHomology (Rep.res Λ.subtype (triv (G := G))) (j + 1) :=
  ((gIso Λ (j + 1)).inv.hom ∘ₗ (homIsoSj Λ j).inv.hom) ∘ₗ coverClass (sj_h₂ Λ j)

theorem bridgeClass_surjective (j : ℕ) : Function.Surjective (bridgeClass Λ j) := by
  intro y
  obtain ⟨z, hz⟩ := coverClass_surjective (sj_h₂ Λ j) (sigma_surjective Λ (j + 1))
    ((homIsoSj Λ j).hom.hom ((gIso Λ (j + 1)).hom.hom y))
  refine ⟨z, ?_⟩
  change (gIso Λ (j + 1)).inv.hom ((homIsoSj Λ j).inv.hom (coverClass (sj_h₂ Λ j) z)) = y
  rw [hz]
  simp

theorem bridgeClass_eq_zero_iff (j : ℕ) (c : Zhom Λ j) :
    bridgeClass Λ j c = 0 ↔
      (c : Chains G (j + 1)) ∈ NullChains Λ (j + 1) ⊔ LinearMap.range (homogeneousBoundary (j + 2)) := by
  have h1 : bridgeClass Λ j c = 0 ↔ coverClass (sj_h₂ Λ j) c = 0 := by
    change (gIso Λ (j + 1)).inv.hom ((homIsoSj Λ j).inv.hom (coverClass (sj_h₂ Λ j) c)) = 0 ↔ _
    constructor
    · intro h
      have := (ModuleCat.mono_iff_injective (gIso Λ (j + 1)).inv).mp inferInstance
        (h.trans (map_zero (gIso Λ (j + 1)).inv.hom).symm)
      exact (ModuleCat.mono_iff_injective (homIsoSj Λ j).inv).mp inferInstance
        (this.trans (map_zero (homIsoSj Λ j).inv.hom).symm)
    · intro h
      rw [h, map_zero, map_zero]
  rw [h1, coverClass_eq_zero_iff (sj_h₁ Λ j) (sj_h₂ Λ j) (sigma_surjective Λ (j + 2)) c]
  have hk : LinearMap.ker (sigma Λ (j + 1)) = NullChains Λ (j + 1) := by
    ext c'; exact sigma_eq_zero_iff Λ (j + 1) c'
  change (c : Chains G (j + 1)) ∈ LinearMap.ker (sigma Λ (j + 1)) ⊔
    LinearMap.range (homogeneousBoundary (j + 2)) ↔ _
  rw [hk]

theorem bridgeClass_eq_iff (j : ℕ) (c d : Zhom Λ j) :
    bridgeClass Λ j c = bridgeClass Λ j d ↔
      (c : Chains G (j + 1)) - d ∈ NullChains Λ (j + 1) ⊔ LinearMap.range (homogeneousBoundary (j + 2)) := by
  rw [← sub_eq_zero, ← map_sub, bridgeClass_eq_zero_iff]
  rfl

end TernaryPeriodPolynomials.Argument.HomologyBridge
