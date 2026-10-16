module

public import TernaryPeriodPolynomials.Topology.Rational.Homology.CoefficientsIso

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory
open SingularLocalCap SingularLocalCap.Homology SingularLocalCompactCap.Algebra

/-- A genuine short-complex map sends an actual cycle to its actual image cycle. -/
def mapCycle {S T : ShortComplex (ModuleCat.{0} ℚ)} (f : S ⟶ T) (c : Cycles S) : Cycles T :=
  ⟨f.τ₂ c.val, by
    have h := congrArg (fun g => g c.val) f.comm₂₃
    change T.g (f.τ₂ c.val) = f.τ₃ (S.g c.val) at h
    exact h.trans (by rw [c.property, map_zero])⟩

/-- The actual short-complex homology map preserves the exact quotient-cycle class. -/
theorem cycleClass_natural {S T : ShortComplex (ModuleCat.{0} ℚ)} (f : S ⟶ T) (c : Cycles S) :
    ShortComplex.homologyMap f (cycleClass S c) = cycleClass T (mapCycle f c) := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [cycleClass_opcycles]
  change (ShortComplex.homologyMap f ≫ T.homologyι) _ = _
  rw [ShortComplex.homologyι_naturality]
  change S.opcyclesMap f (S.homologyι _) = _
  rw [cycleClass_opcycles]
  exact congrArg (fun g => g c.val) (S.p_opcyclesMap f)

/-- Actual Hom-dual functoriality is precomposition in all three degrees. -/
def dualMap {S T : ShortComplex (ModuleCat.{0} ℚ)} (f : S ⟶ T) (V : ModuleCat.{0} ℚ) :
    dual T V ⟶ dual S V where
  τ₁ := ModuleCat.ofHom (precompose f.τ₃ V)
  τ₂ := ModuleCat.ofHom (precompose f.τ₂ V)
  τ₃ := ModuleCat.ofHom (precompose f.τ₁ V)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    ext φ x
    exact congrArg φ (congrArg (fun g => g x) f.comm₂₃).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext φ x
    exact congrArg φ (congrArg (fun g => g x) f.comm₁₂).symm

/-- The actual universal-coefficient isomorphism is natural under every genuine
short-complex map, with the literal evaluation convention on both sides. -/
theorem evaluation_natural {S T : ShortComplex (ModuleCat.{0} ℚ)} (f : S ⟶ T)
    (V : ModuleCat.{0} ℚ) (h : (dual T V).homology) (c : S.homology) :
    evaluationEquiv S V (ShortComplex.homologyMap (dualMap f V) h) c =
      evaluationEquiv T V h (ShortComplex.homologyMap f c) := by
  obtain ⟨φ,rfl⟩ := cycleClass_surjective (dual T V) h
  obtain ⟨x,rfl⟩ := cycleClass_surjective S c
  rw [cycleClass_natural, cycleClass_natural, evaluationEquiv_cycleClasses, evaluationEquiv_cycleClasses]
  rfl

end TernaryPoly.RationalHomologyCoefficients
