module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainCalculus
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.Basic.Complex.Basic

@[expose] public section


/-!
# The coinvariants of the standard resolution are chains modulo null chains

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains)

variable {G : Type} [Group G] (Λ : Subgroup G)

/-- Homogeneous chains as the monoid algebra of the standard resolution. -/
def toMA (n : ℕ) : Chains G n ≃ₗ[ℂ] MonoidAlgebra ℂ (Fin (n + 1) → G) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm

omit [Group G] in
theorem toMA_single (n : ℕ) (x : Fin (n + 1) → G) (r : ℂ) :
    toMA n (Finsupp.single x r) = MonoidAlgebra.single x r := rfl

/-- The `n`-th term of the standard resolution (definitionally `Rep.standardComplex.X n`, `xIso`). -/
abbrev Xstd (n : ℕ) : Rep ℂ G := Rep.ofMulAction ℂ G (Fin (n + 1) → G)

theorem Xstd_act (n : ℕ) (γ : G) (x : Fin (n + 1) → G) (r : ℂ) :
    (Xstd (G := G) n).ρ γ (MonoidAlgebra.single x r) = MonoidAlgebra.single (γ • x) r :=
  Representation.ofMulAction_single γ x r

/-- Left translation of all vertices. -/
def actC (γ : G) (n : ℕ) : Chains G n →ₗ[ℂ] Chains G n :=
  Finsupp.lmapDomain ℂ ℂ (fun x : Fin (n + 1) → G => γ • x)

theorem actC_single (γ : G) (n : ℕ) (x : Fin (n + 1) → G) (r : ℂ) :
    actC γ n (Finsupp.single x r) = Finsupp.single (γ • x) r := by
  simp [actC]

theorem toMA_actC (γ : G) (n : ℕ) (c : Chains G n) :
    toMA n (actC γ n c) = (Xstd (G := G) n).ρ γ (toMA n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single x r =>
    rw [actC_single, toMA_single, toMA_single, Xstd_act]

theorem actC_sub_mem_null (γ : Λ) (n : ℕ) (c : Chains G n) :
    actC (γ : G) n c - c ∈ NullChains Λ n := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    have : actC (γ : G) n (c + d) - (c + d) = (actC (γ : G) n c - c) + (actC (γ : G) n d - d) := by
      rw [map_add]; abel
    rw [this]
    exact Submodule.add_mem _ hc hd
  | single x r =>
    rw [actC_single]
    have : Finsupp.single ((γ : G) • x) r - Finsupp.single x r =
        r • (Finsupp.single (fun i => (γ : G) * x i) 1 - Finsupp.single x 1) := by
      simp [smul_sub]
      rfl
    rw [this]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨γ, x, rfl⟩)

theorem ker_eq_null (n : ℕ) :
    Coinvariants.ker ((Xstd (G := G) n).ρ.comp Λ.subtype) =
      (NullChains Λ n).map (toMA n).toLinearMap := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨γ, v⟩, rfl⟩
    refine ⟨actC (γ : G) n ((toMA n).symm v) - (toMA n).symm v, actC_sub_mem_null Λ γ n _, ?_⟩
    rw [map_sub]
    simp only [LinearEquiv.coe_coe, toMA_actC, LinearEquiv.apply_symm_apply]
    rfl
  · rintro _ ⟨c, hc, rfl⟩
    have hle : NullChains Λ n ≤ (Coinvariants.ker ((Xstd (G := G) n).ρ.comp Λ.subtype)).comap
        (toMA n).toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨γ, x, rfl⟩
      refine Submodule.subset_span ⟨(γ, toMA n (Finsupp.single x 1)), ?_⟩
      change ((Xstd (G := G) n).ρ (γ : G)) (MonoidAlgebra.single x (1 : ℂ)) -
          MonoidAlgebra.single x (1 : ℂ) =
        toMA n (Finsupp.single (fun i => (γ : G) * x i) 1) - toMA n (Finsupp.single x 1)
      rw [toMA_single, toMA_single]
      exact congrArg (fun z => z - MonoidAlgebra.single x (1 : ℂ)) (Xstd_act (G := G) n γ x 1)
    exact hle hc

end TernaryPeriodPolynomials.Argument.HomologyBridge
