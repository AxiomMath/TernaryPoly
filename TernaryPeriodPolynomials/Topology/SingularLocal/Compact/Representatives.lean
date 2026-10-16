module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Every compact-support cohomology class is represented by a genuine fixed-support class. -/
theorem compactClass_exists_rep (k : ℕ) (c : compactCohomology p V k) :
    ∃ (K : Compacts B) (x : (supportCochains p V (K : Set B)).homology k),
      compactClassMap p V K k x = c :=
  Concrete.colimit_exists_rep (compactCohomologyDiagram p V k) c

/-- Two actual compact-support representatives coincide precisely after a common compact enlargement. -/
theorem compactClass_eq_iff (k : ℕ) (K L : Compacts B)
    (x : (supportCochains p V (K : Set B)).homology k)
    (y : (supportCochains p V (L : Set B)).homology k) :
    compactClassMap p V K k x = compactClassMap p V L k y ↔
      ∃ (M : Compacts B) (hKM : K ≤ M) (hLM : L ≤ M),
        homologyMap (supportMap p V (K : Set B) (M : Set B) hKM) k x =
          homologyMap (supportMap p V (L : Set B) (M : Set B) hLM) k y := by
  constructor
  · intro h
    obtain ⟨M,f,g,hfg⟩ := Concrete.colimit_exists_of_rep_eq (compactCohomologyDiagram p V k) x y h
    exact ⟨M,leOfHom f,leOfHom g,hfg⟩
  · rintro ⟨M,hKM,hLM,hxy⟩
    exact Concrete.colimit_rep_eq_of_exists (compactCohomologyDiagram p V k) x y
      ⟨M,homOfLE hKM,homOfLE hLM,hxy⟩

/-- A fixed-support class becomes zero in compact-support cohomology exactly when it dies on a
larger compact support. -/
theorem compactClass_zero_iff (k : ℕ) (K : Compacts B)
    (x : (supportCochains p V (K : Set B)).homology k) :
    compactClassMap p V K k x = 0 ↔ ∃ (L : Compacts B) (hKL : K ≤ L),
      homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) k x = 0 := by
  rw [← map_zero (compactClassMap p V K k).hom,compactClass_eq_iff]
  constructor
  · rintro ⟨L,hKL,_,h⟩
    exact ⟨L,hKL,by simpa only [map_zero] using h⟩
  · rintro ⟨L,hKL,h⟩
    exact ⟨L,hKL,hKL,by simpa only [map_zero] using h⟩

/-- Linear maps out of actual compact-support cohomology are determined on fixed-support classes. -/
theorem compactCohomology_hom_ext (k : ℕ) (M : ModuleCat.{0} ℚ)
    (f g : compactCohomology p V k ⟶ M)
    (h : ∀ K : Compacts B, compactClassMap p V K k ≫ f = compactClassMap p V K k ≫ g) :
    f = g :=
  colimit.hom_ext h

end TernaryPoly.SingularLocalSupport
