module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsQuotient
public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsExtension

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory
open SingularLocalCap SingularLocalCap.Homology
variable (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ)

/-- Every V-valued map on rational homology is induced by an actual dual cocycle,
using extension from the full cycle subspace with no finite-dimensional hypothesis. -/
theorem evaluation_surjective : Function.Surjective (evaluation S V) := by
  intro ψ
  obtain ⟨φ,hφ⟩ := LinearMap.exists_extend (ψ.comp (cycleClass S))
  have hc : φ ∈ Cycles (dual S V) := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hφ (S.moduleCatToCycles x)
    change φ (S.f x) = ψ (cycleClass S (S.moduleCatToCycles x)) at h
    exact h.trans (by rw [cycleClass_boundary, map_zero]; rfl)
  refine ⟨cycleClass (dual S V) ⟨φ,hc⟩, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨c,rfl⟩ := SingularLocalCompactCap.Algebra.cycleClass_surjective S z
  rw [evaluation_cycleClasses]
  exact LinearMap.congr_fun hφ c

/-- A dual cocycle evaluating to zero on homology is an actual dual coboundary.
The factorization through the outgoing differential uses rational linear extension. -/
theorem evaluation_injective : Function.Injective (evaluation S V) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  obtain ⟨φ,rfl⟩ := SingularLocalCompactCap.Algebra.cycleClass_surjective (dual S V) z
  have hker : LinearMap.ker S.g.hom ≤ LinearMap.ker φ.val := by
    intro c hc
    have h := LinearMap.congr_fun hz (cycleClass S ⟨c,hc⟩)
    rw [evaluation_cycleClasses] at h
    exact h
  obtain ⟨ψ,hψ⟩ := factor_of_ker_le S.g.hom φ.val hker
  have he : (dual S V).moduleCatToCycles ψ = φ := Subtype.ext hψ
  rw [← he, cycleClass_boundary]

/-- Rational universal-coefficient isomorphism: actual dual cohomology is the full
V-valued linear Hom of actual homology, for every rational module V. -/
def evaluationEquiv : (dual S V).homology ≃ₗ[ℚ] (S.homology →ₗ[ℚ] V) :=
  LinearEquiv.ofBijective (evaluation S V) ⟨evaluation_injective S V, evaluation_surjective S V⟩

/-- The actual universal-coefficient isomorphism has literal scalar/vector evaluation on representatives. -/
theorem evaluationEquiv_cycleClasses (φ : Cycles (dual S V)) (c : Cycles S) :
    evaluationEquiv S V (cycleClass (dual S V) φ) (cycleClass S c) = φ.val c.val :=
  evaluation_cycleClasses S V φ c

end TernaryPoly.RationalHomologyCoefficients
