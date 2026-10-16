module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsRepresentatives

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory HomologicalComplex
open SingularLocalCap SingularLocalCap.Homology SingularLocalCompactCap.Algebra

/-- The V-valued Hom functor sends actual chain maps to actual contravariant cochain maps. -/
def homCochainsMap {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ L)
    (V : ModuleCat.{0} ℚ) : homCochains L V ⟶ homCochains K V where
  f a := ModuleCat.ofHom (precompose (f.f a) V)
  comm' i j _ := by
    rw [homCochains_d, homCochains_d]
    apply ModuleCat.hom_ext
    ext φ c
    exact congrArg φ (congrArg (fun g => g c) (f.comm j i)).symm

/-- An actual complex map sends a genuine cycle to its literal image cycle. -/
def mapComplexCycle {s : ComplexShape ℕ} {K L : HomologicalComplex (ModuleCat.{0} ℚ) s}
    (f : K ⟶ L) (i j k : ℕ) (c : Cycles (K.sc' i j k)) : Cycles (L.sc' i j k) :=
  ⟨f.f j c.val, by
    have h := congrArg (fun g => g c.val) (f.comm j k)
    change L.d j k (f.f j c.val) = f.f k (K.d j k c.val) at h
    exact h.trans (by erw [c.property, map_zero]; rfl)⟩

/-- The full-complex universal coefficient isomorphism is natural for actual chain maps,
with literal evaluation on both actual homology classes. -/
theorem homologyEvaluationEquiv_natural {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (f : K ⟶ L) (V : ModuleCat.{0} ℚ) (a : ℕ)
    (h : (homCochains L V).homology a) (c : K.homology a) :
    homologyEvaluationEquiv K V a (homologyMap (homCochainsMap f V) a h) c =
      homologyEvaluationEquiv L V a h (homologyMap f a c) := by
  obtain ⟨φ,rfl⟩ := cochainClass_surjective (homCochains L V) a h
  obtain ⟨x,rfl⟩ := chainClass_surjective K a c
  rw [cochainClass_natural (homCochainsMap f V) a φ
    (mapComplexCycle (homCochainsMap f V) (a-1) a (a+1) φ) rfl]
  rw [chainClass_natural f a x (mapComplexCycle f (a+1) a (a-1) x) rfl]
  erw [homologyEvaluationEquiv_classes, homologyEvaluationEquiv_classes]
  rfl

end TernaryPoly.RationalHomologyCoefficients
