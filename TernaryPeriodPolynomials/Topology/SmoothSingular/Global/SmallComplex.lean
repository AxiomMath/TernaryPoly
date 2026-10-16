module

/- Adapted from the rational predecessor EquivariantSingularSmallComplex.lean by explicit base-ring
replacement to ℝ and the actual SmoothSingularGlobal chain model. -/
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallBasis

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory FreeActionLinearization SmoothSingularGlobal
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (P : (n : ℕ) → SingularSimplex E n → Prop)
  (hP : ∀ n (g : G) (σ : SingularSimplex E n), P n σ → P n (g • σ))
  (hD : ∀ n c, c ∈ predicateSpan E (n+1) (P (n+1)) →
    ((underlyingChains E).d (n+1) n) c ∈ predicateSpan E n (P n))

/-- The actual invariant simplex-family span in a fixed degree. -/
abbrev familyRep (n : ℕ) : Rep ℝ G :=
  predicateRep G E n (P n) (hP := ⟨hP n⟩)

/-- Restriction of the actual singular boundary to the invariant family spans. -/
def familyD (n : ℕ) : familyRep G E P hP (n+1) ⟶ familyRep G E P hP n :=
  Rep.ofHom ⟨((underlyingChains E).d (n+1) n).hom.restrict (hD n), fun g => by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun m => m.hom c.val) ((scalarChainMap G E g).comm (n+1) n)⟩

/-- The restricted actual singular boundaries still square to zero as representation morphisms. -/
theorem familyD_squared (n : ℕ) :
    familyD G E P hP hD (n+1) ≫ familyD G E P hP hD n = 0 := by
  ext c
  exact congrArg (fun m => m.hom c.val) ((underlyingChains E).d_comp_d (n+2) (n+1) n)

/-- The genuine equivariant singular-chain complex spanned by the invariant simplex family. -/
def familyComplex : ChainComplex (Rep ℝ G) ℕ :=
  ChainComplex.of (familyRep G E P hP) (familyD G E P hP hD) (familyD_squared G E P hP hD)

/-- Each actual family-chain degree is projective whenever the space action is free. -/
instance familyComplex_projective [IsCancelSMul G E] (n : ℕ) :
    Projective ((familyComplex G E P hP hD).X n) :=
  predicateRep_projective G E n (P n) (hP := ⟨hP n⟩)

/-- The inclusion of each actual span into singular chains is a representation morphism. -/
def familyInclusionDegree (n : ℕ) : familyRep G E P hP n ⟶ chainRep G E n :=
  Rep.ofHom ⟨(predicateSpan E n (P n)).subtype, fun _ => rfl⟩

/-- The literal inclusion from actual family chains to actual equivariant singular chains. -/
def familyInclusion : familyComplex G E P hP hD ⟶ equivariantChains G E where
  f := familyInclusionDegree G E P hP
  comm' i j hij := by
    obtain rfl : i = j+1 := hij.symm
    simp only [familyComplex, ChainComplex.of_d]
    ext c
    rfl

variable (Q : (n : ℕ) → SingularSimplex E n → Prop)
  (hQ : ∀ n (g : G) (σ : SingularSimplex E n), Q n σ → Q n (g • σ))
  (hDQ : ∀ n c, c ∈ predicateSpan E (n+1) (Q (n+1)) →
    ((underlyingChains E).d (n+1) n) c ∈ predicateSpan E n (Q n))
  (hPQ : ∀ n σ, P n σ → Q n σ)

include hPQ in
/-- Containment of actual simplex families gives containment of their actual generator spans. -/
theorem predicateSpan_mono (n : ℕ) : predicateSpan E n (P n) ≤ predicateSpan E n (Q n) := by
  apply Submodule.span_mono
  rintro c ⟨σ,hσ,hc⟩
  exact ⟨σ,hPQ n σ hσ,hc⟩

/-- The genuine equivariant inclusion of two nested invariant family-chain complexes. -/
def familyMap : familyComplex G E P hP hD ⟶ familyComplex G E Q hQ hDQ where
  f n := Rep.ofHom ⟨Submodule.inclusion (predicateSpan_mono E P Q hPQ n), fun _ => rfl⟩
  comm' i j hij := by
    obtain rfl : i = j+1 := hij.symm
    simp only [familyComplex, ChainComplex.of_d]
    ext c
    rfl

/-- Nested family inclusion maps retain the literal underlying chain. -/
theorem familyMap_apply (n : ℕ) (c : (familyComplex G E P hP hD).X n) :
    (((familyMap G E P hP hD Q hQ hDQ hPQ).f n c).val : (underlyingChains E).X n) = c.val := rfl

end TernaryPoly.SmoothSingularGlobal
