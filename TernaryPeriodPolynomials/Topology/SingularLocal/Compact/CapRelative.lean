module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology
public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SingularLocalSupport EquivariantSingularSmall SphereOddDegree

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The support cochains are literally the relative kernel for the complement covering. -/
theorem supportCochains_eq_relative (K : Set B) :
    supportCochains p V K = relativeLocalCochains (restrictedProjection p Kᶜ) p
      (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ) (restricted_square p Kᶜ)
      (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) V := rfl

/-- The scalar support chains are literally the relative cokernel for the complement inclusion. -/
theorem supportChains_eq_relative (K : Set B) :
    RationalManifoldCompact.supportChains K = relativeScalarChains (sInclusion Kᶜ) := rfl

variable [IsCancelSMul G E]

/-- The actual relative cochain cap for a support and its complement covering. -/
def supportCap (K : Set B) (a b : ℕ) :
    (supportCochains p V K).X a →ₗ[ℚ]
      (RationalManifoldCompact.supportChains K).X (a+b) →ₗ[ℚ] (localChains p hp.out V).X b :=
  relativeCochainCap (restrictedProjection p Kᶜ) p
    (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ) (restricted_square p Kᶜ)
    (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) V a b

/-- On an actual scalar representative, the support cap is the geometric cap. -/
theorem supportCap_projection (K : Set B) (a b : ℕ)
    (φ : (supportCochains p V K).X a) (c : (scalarChains B).X (a+b)) :
    supportCap p V K a b φ ((cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (a+b) c) =
      cap p hp.out V a b ((supportInclusion p V K).f a φ) c :=
  relativeCochainCap_projection (restrictedProjection p Kᶜ) p
    (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ) (restricted_square p Kᶜ)
    (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) V a b φ c

/-- Support cap satisfies the proved geometric Leibniz identity. -/
theorem supportCap_leibniz (K : Set B) :
    Descent.Leibniz (supportCochains p V K) (RationalManifoldCompact.supportChains K)
      (localChains p hp.out V) (supportCap p V K) :=
  relativeCochainCap_leibniz (restrictedProjection p Kᶜ) p
    (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ) (restricted_square p Kᶜ)
    (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) V

/-- Genuine relative local cohomology caps actual scalar support homology to absolute local homology. -/
def supportCapHomology (K : Set B) (a b : ℕ) :
    (supportCochains p V K).homology a →ₗ[ℚ]
      (RationalManifoldCompact.supportChains K).homology (a+b) →ₗ[ℚ]
        (localChains p hp.out V).homology b :=
  relativeCochainCapHomology (restrictedProjection p Kᶜ) p
    (sInclusion (p ⁻¹' Kᶜ)) (sInclusion Kᶜ) (restricted_square p Kᶜ)
    (restrictedQuotientCovering p Kᶜ) hp.out (fun _ _ => rfl) V a b

/-- The actual support pairing retains its concrete relative-cycle formula. -/
theorem supportCapHomology_representatives (K : Set B) (a b : ℕ)
    (x : Homology.Cycles ((supportCochains p V K).sc' (a-1) a (a+1)))
    (c : Homology.Cycles ((RationalManifoldCompact.supportChains K).sc' (a+b+1) (a+b) (a+b-1))) :
    supportCapHomology p V K a b (Descent.cochainClass _ a x) (Descent.chainClass _ (a+b) c) =
      Descent.chainClass (localChains p hp.out V) b
        ⟨supportCap p V K a b x.val c.val,
          Descent.cycles _ _ _ _ (supportCap_leibniz p V K) a b x c⟩ :=
  Descent.homology_representatives _ _ _ _ (supportCap_leibniz p V K) a b x c

end TernaryPoly.SingularLocalCompactCap
