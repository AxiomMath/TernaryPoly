module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVConnecting
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVSquares
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace ComposableArrows
open SingularLocalSupport SingularLocalCompactMV SingularLocalCompactCap
open EquivariantSingularSmall RationalManifoldCompact RationalLocalOrientation

/-- Multiplying a rational module isomorphism by the genuine cap sign preserves invertibility. -/
theorem signed_isIso {A B : ModuleCat.{0} ℚ} (f : A ⟶ B) [IsIso f] (a : ℕ) :
    IsIso ((-1 : ℤ)^a • f) := by
  have hs : (-1 : ℤ)^a * (-1 : ℤ)^a = 1 := by
    rw [← pow_add,← two_mul,pow_mul]
    norm_num
  refine ⟨⟨(-1 : ℤ)^a • inv f,?_,?_⟩⟩ <;>
    simp only [Preadditive.zsmul_comp,Preadditive.comp_zsmul,smul_smul,hs,one_zsmul,
      IsIso.hom_inv_id,IsIso.inv_hom_id]

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  [T2Space B] [LocallyCompactSpace B] (U D : Opens B) (hUD : U ⊔ D = ⊤)

/-- Five consecutive genuine compact-support Mayer–Vietoris terms. -/
def compactRow (a : ℕ) : ComposableArrows (ModuleCat ℚ) 4 :=
  mk₄ (compactDiagonal p V U D a) (compactSum p V U D a)
    (compactConnecting p V U D hUD a) (compactDiagonal p V U D (a+1))

/-- Exactness of all three positions in the genuine compact-support five-term row. -/
theorem compactRow_exact (a : ℕ) : (compactRow p V U D hUD a).Exact := by
  have h₀ := (compactMiddleSegment_exact p V U D hUD a).exact_toComposableArrows
  have h₁ := (compactAmbientSegment_exact p V U D hUD a).exact_toComposableArrows
  have h₂ := (compactIntersectionSegment_exact p V U D hUD a).exact_toComposableArrows
  change (mk₂ (compactMiddleSegment p V U D hUD a).f (compactMiddleSegment p V U D hUD a).g).Exact at h₀
  change (mk₂ (compactAmbientSegment p V U D hUD a).f (compactAmbientSegment p V U D hUD a).g).Exact at h₁
  change (mk₂ (compactIntersectionSegment p V U D hUD a).f (compactIntersectionSegment p V U D hUD a).g).Exact at h₂
  rw [compactMiddleSegment_f,compactMiddleSegment_g] at h₀
  rw [compactAmbientSegment_f,compactAmbientSegment_g] at h₁
  rw [compactIntersectionSegment_f,compactIntersectionSegment_g] at h₂
  exact exact_of_δ₀ h₀ (exact_of_δ₀ h₁ h₂)

variable [IsCancelSMul G E]

/-- Five consecutive genuine ordinary Mayer–Vietoris terms in the cap-compatible direction. -/
def ordinaryRow (b : ℕ) : ComposableArrows (ModuleCat ℚ) 4 :=
  mk₄ (ordinaryDiagonal p V U D (b+1)) (ordinarySum p V U D (b+1))
    (ordinaryConnecting p V U D hUD b) (ordinaryDiagonal p V U D b)

omit [T2Space B] [LocallyCompactSpace B] in
/-- Exactness of all three positions in the actual ordinary five-term row. -/
theorem ordinaryRow_exact (b : ℕ) : (ordinaryRow p V U D hUD b).Exact := by
  have h₀ := (ordinaryMiddleSegment_exact p V U D hUD (b+1)).exact_toComposableArrows
  have h₁ := (ordinaryAmbientSegment_exact p V U D hUD b).exact_toComposableArrows
  have h₂ := (ordinaryIntersectionSegment_exact p V U D hUD b).exact_toComposableArrows
  change (mk₂ (ordinaryMiddleSegment p V U D hUD (b+1)).f (ordinaryMiddleSegment p V U D hUD (b+1)).g).Exact at h₀
  change (mk₂ (ordinaryAmbientSegment p V U D hUD b).f (ordinaryAmbientSegment p V U D hUD b).g).Exact at h₁
  change (mk₂ (ordinaryIntersectionSegment p V U D hUD b).f (ordinaryIntersectionSegment p V U D hUD b).g).Exact at h₂
  rw [ordinaryMiddleSegment_f,ordinaryMiddleSegment_g] at h₀
  rw [ordinaryAmbientSegment_f,ordinaryAmbientSegment_g] at h₁
  rw [ordinaryIntersectionSegment_f,ordinaryIntersectionSegment_g] at h₂
  exact exact_of_δ₀ h₀ (exact_of_δ₀ h₁ h₂)

end TernaryPoly.SingularLocalCompactCapMV
