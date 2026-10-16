module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.TraceChains

@[expose] public section


/-!
# Homogeneous chains: translations and boundaries modulo a subgroup

Chains of dimension `k` with vertices in a group `G` are finitely supported complex combinations
of `(k+1)`-tuples. A subgroup `Λ` acts by left translation of all vertices; a chain is null modulo
`Λ` when it lies in the span of the differences `γ·x - x` (`TraceChains.NullChains`), and it is a
boundary modulo `Λ` when it is a boundary plus a null chain (`BdryChains`). Right translation of all
vertices commutes with left translation, hence preserves both classes.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus

open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)

/-- Chains of dimension `k`: formal combinations of `(k+1)`-tuples of vertices. -/
abbrev Chains (G : Type) (k : ℕ) := (Fin (k + 1) → G) →₀ ℂ

variable {G : Type} [Group G]

/-- Chains that are boundaries modulo `Λ`-null chains. -/
def BdryChains (Λ : Subgroup G) (k : ℕ) : Submodule ℂ (Chains G k) :=
  NullChains Λ k ⊔ LinearMap.range (homogeneousBoundary (G := G) (k + 1))

/-- Left translation of all vertices. -/
def leftTranslate (g : G) (k : ℕ) : Chains G k →ₗ[ℂ] Chains G k :=
  Finsupp.lmapDomain ℂ ℂ (fun x i => g * x i)

/-- Right translation of all vertices. -/
def rightTranslate (h : G) (k : ℕ) : Chains G k →ₗ[ℂ] Chains G k :=
  Finsupp.lmapDomain ℂ ℂ (fun x i => x i * h)

theorem leftTranslate_single (g : G) {k : ℕ} (x : Fin (k + 1) → G) (a : ℂ) :
    leftTranslate g k (Finsupp.single x a) = Finsupp.single (fun i => g * x i) a := by
  rw [leftTranslate, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem rightTranslate_single (h : G) {k : ℕ} (x : Fin (k + 1) → G) (a : ℂ) :
    rightTranslate h k (Finsupp.single x a) = Finsupp.single (fun i => x i * h) a := by
  rw [rightTranslate, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
