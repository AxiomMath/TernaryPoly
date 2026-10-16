module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingCompactMayerVietoris
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering CategoryTheory
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V)

/-- The actual connecting morphism of ordinary de Rham cohomology on the quotient. -/
def ordinaryConnecting (n : ℕ) :
    (coveringComplex ρ (hU.inter hV)).homology n ⟶ (coveringComplex ρ (hU.union hV)).homology (n + 1) :=
  (ordinarySequence_shortExact ρ hU hV).δ n (n + 1) rfl

theorem ordinaryConnecting_comp (n : ℕ) :
    ordinaryConnecting ρ hU hV n ≫ HomologicalComplex.homologyMap (ordinaryUnionMap ρ hU hV) (n + 1) = 0 :=
  (ordinarySequence_shortExact ρ hU hV).δ_comp n (n + 1) rfl

theorem ordinary_compConnecting (n : ℕ) :
    HomologicalComplex.homologyMap (ordinaryOverlapMap ρ hU hV) n ≫ ordinaryConnecting ρ hU hV n = 0 :=
  (ordinarySequence_shortExact ρ hU hV).comp_δ n (n + 1) rfl

/-- Exactness of the ordinary cohomology sequence at the union term. -/
theorem ordinary_cohomology_exact_union (n : ℕ) :
    (ShortComplex.mk (ordinaryConnecting ρ hU hV n)
      (HomologicalComplex.homologyMap (ordinaryUnionMap ρ hU hV) (n + 1))
      (ordinaryConnecting_comp ρ hU hV n)).Exact :=
  (ordinarySequence_shortExact ρ hU hV).homology_exact₁ n (n + 1) rfl

/-- Exactness of the ordinary cohomology sequence at the direct-sum term. -/
theorem ordinary_cohomology_exact_pair (n : ℕ) :
    ((ordinarySequence ρ hU hV).map (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n)).Exact :=
  (ordinarySequence_shortExact ρ hU hV).homology_exact₂ n

/-- Exactness of the ordinary cohomology sequence at the overlap term. -/
theorem ordinary_cohomology_exact_overlap (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (ordinaryOverlapMap ρ hU hV) n)
      (ordinaryConnecting ρ hU hV n) (ordinary_compConnecting ρ hU hV n)).Exact :=
  (ordinarySequence_shortExact ρ hU hV).homology_exact₃ n (n + 1) rfl

/-- The genuine compact-support connecting map, in the opposite Mayer-Vietoris direction. -/
def compactConnecting (n : ℕ) :
    (compactCoveringComplex ρ (hU.union hV)).homology n ⟶
      (compactCoveringComplex ρ (hU.inter hV)).homology (n + 1) :=
  (compactSequence_shortExact ρ hU hV).δ n (n + 1) rfl

theorem compactConnecting_comp (n : ℕ) :
    compactConnecting ρ hU hV n ≫ HomologicalComplex.homologyMap (compactIntersectionMap ρ hU hV) (n + 1) = 0 :=
  (compactSequence_shortExact ρ hU hV).δ_comp n (n + 1) rfl

theorem compact_compConnecting (n : ℕ) :
    HomologicalComplex.homologyMap (compactUnionMap ρ hU hV) n ≫ compactConnecting ρ hU hV n = 0 :=
  (compactSequence_shortExact ρ hU hV).comp_δ n (n + 1) rfl

theorem compact_cohomology_exact_overlap (n : ℕ) :
    (ShortComplex.mk (compactConnecting ρ hU hV n)
      (HomologicalComplex.homologyMap (compactIntersectionMap ρ hU hV) (n + 1))
      (compactConnecting_comp ρ hU hV n)).Exact :=
  (compactSequence_shortExact ρ hU hV).homology_exact₁ n (n + 1) rfl

theorem compact_cohomology_exact_pair (n : ℕ) :
    ((compactSequence ρ hU hV).map (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n)).Exact :=
  (compactSequence_shortExact ρ hU hV).homology_exact₂ n

theorem compact_cohomology_exact_union (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (compactUnionMap ρ hU hV) n)
      (compactConnecting ρ hU hV n) (compact_compConnecting ρ hU hV n)).Exact :=
  (compactSequence_shortExact ρ hU hV).homology_exact₃ n (n + 1) rfl

end TernaryPoly.SmoothDeRhamGluing
