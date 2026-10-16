module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Normalization
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalHomologyCoefficients
open CategoryTheory
open SingularLocalCap SingularLocalCap.Homology

/-- Precomposition with an actual rational linear map, with arbitrary rational target V. -/
def precompose {A B : ModuleCat.{0} ℚ} (f : A ⟶ B) (V : ModuleCat.{0} ℚ) :
    (B →ₗ[ℚ] V) →ₗ[ℚ] (A →ₗ[ℚ] V) where
  toFun φ := φ.comp f.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual V-valued Hom dual of a rational short complex. -/
abbrev dual (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ) :
    ShortComplex (ModuleCat.{0} ℚ) :=
  ShortComplex.mk (ModuleCat.ofHom (precompose S.g V)) (ModuleCat.ofHom (precompose S.f V)) (by
    apply ModuleCat.hom_ext
    ext φ x
    change φ (S.g (S.f x)) = 0
    have h := congrArg (fun f => f x) S.zero
    change S.g (S.f x) = 0 at h
    rw [h, map_zero])

/-- The cocycle condition is exactly vanishing on the chain-boundary image. -/
theorem dual_cycle_boundary (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ)
    (φ : Cycles (dual S V)) (x : S.X₁) : φ.val (S.f x) = 0 :=
  LinearMap.congr_fun φ.property x

/-- A rational chain boundary represents zero in the actual short-complex homology. -/
theorem cycleClass_boundary (S : ShortComplex (ModuleCat.{0} ℚ)) (x : S.X₁) :
    cycleClass S (S.moduleCatToCycles x) = 0 := by
  change S.moduleCatHomologyIso.inv ((Boundaries S).mkQ (S.moduleCatToCycles x)) = 0
  rw [show (Boundaries S).mkQ (S.moduleCatToCycles x) = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩]
  exact map_zero _

/-- Restricting a genuine dual cocycle to actual chain cycles annihilates actual boundaries. -/
theorem cycleRestriction_boundaries (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ)
    (φ : Cycles (dual S V)) :
    Boundaries S ≤ LinearMap.ker (φ.val.comp (Cycles S).subtype) := by
  rintro c ⟨x,rfl⟩
  exact dual_cycle_boundary S V φ x

/-- The canonical evaluation of a dual cocycle on actual homology: restrict to cycles
and descend through their boundary quotient, then use the actual Mathlib comparison. -/
def evaluateCycle (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ)
    (φ : Cycles (dual S V)) : S.homology →ₗ[ℚ] V :=
  ((Boundaries S).liftQ (φ.val.comp (Cycles S).subtype) (cycleRestriction_boundaries S V φ)).comp
    S.moduleCatHomologyIso.hom.hom

/-- The canonical cycle evaluation is literal application to every actual cycle representative. -/
theorem evaluateCycle_cycleClass (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ)
    (φ : Cycles (dual S V)) (c : Cycles S) :
    evaluateCycle S V φ (cycleClass S c) = φ.val c.val := by
  have h := congrArg (fun f => f ((Boundaries S).mkQ c)) S.moduleCatHomologyIso.inv_hom_id
  change S.moduleCatHomologyIso.hom (S.moduleCatHomologyIso.inv ((Boundaries S).mkQ c)) =
    (Boundaries S).mkQ c at h
  change (Boundaries S).liftQ _ (cycleRestriction_boundaries S V φ) (S.moduleCatHomologyIso.hom
    (S.moduleCatHomologyIso.inv ((Boundaries S).mkQ c))) = _
  rw [h]
  rfl

/-- Evaluation on homology is linear in the actual dual cocycle. -/
def evaluateCycles (S : ShortComplex (ModuleCat.{0} ℚ)) (V : ModuleCat.{0} ℚ) :
    Cycles (dual S V) →ₗ[ℚ] (S.homology →ₗ[ℚ] V) where
  toFun := evaluateCycle S V
  map_add' φ ψ := by
    ext z
    obtain ⟨c,rfl⟩ := SingularLocalCompactCap.Algebra.cycleClass_surjective S z
    rw [LinearMap.add_apply, evaluateCycle_cycleClass, evaluateCycle_cycleClass, evaluateCycle_cycleClass]
    rfl
  map_smul' r φ := by
    ext z
    obtain ⟨c,rfl⟩ := SingularLocalCompactCap.Algebra.cycleClass_surjective S z
    rw [LinearMap.smul_apply, evaluateCycle_cycleClass, evaluateCycle_cycleClass]
    rfl

end TernaryPoly.RationalHomologyCoefficients
