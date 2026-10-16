module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Leibniz
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Bilinear

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCap.Homology
open CategoryTheory

abbrev Cycles (S : ShortComplex (ModuleCat.{0} ℚ)) := LinearMap.ker S.g.hom
abbrev Boundaries (S : ShortComplex (ModuleCat.{0} ℚ)) := LinearMap.range S.moduleCatToCycles
abbrev QuotientHomology (S : ShortComplex (ModuleCat.{0} ℚ)) := Cycles S ⧸ Boundaries S

/-- A cycle represents its actual Mathlib homology class, via the canonical kernel/quotient comparison. -/
def cycleClass (S : ShortComplex (ModuleCat.{0} ℚ)) : Cycles S →ₗ[ℚ] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (Boundaries S).mkQ

/-- Restrict a concrete bilinear operation to actual cycles once its cycle identity is proved. -/
def restrictCycles (S T U : ShortComplex (ModuleCat.{0} ℚ))
    (β : S.X₂ →ₗ[ℚ] T.X₂ →ₗ[ℚ] U.X₂)
    (hz : ∀ x : Cycles S, ∀ y : Cycles T, U.g (β x.val y.val) = 0) :
    Cycles S →ₗ[ℚ] Cycles T →ₗ[ℚ] Cycles U where
  toFun x := ((β x.val).comp (Cycles T).subtype).codRestrict (Cycles U) (hz x)
  map_add' x y := by
    ext z
    exact congrArg (fun f => f z.val) (map_add β x.val y.val)
  map_smul' r x := by
    ext z
    exact congrArg (fun f => f z.val) (map_smul β r x.val)

/-- A concrete pairing of cycles descends bilinearly through both boundary quotients. -/
def descend (S T U : ShortComplex (ModuleCat.{0} ℚ))
    (β : Cycles S →ₗ[ℚ] Cycles T →ₗ[ℚ] Cycles U)
    (hS : ∀ x y, β (S.moduleCatToCycles x) y ∈ Boundaries U)
    (hT : ∀ x y, β x (T.moduleCatToCycles y) ∈ Boundaries U) :
    S.homology →ₗ[ℚ] T.homology →ₗ[ℚ] U.homology := by
  let γ := β.compr₂ (Boundaries U).mkQ
  have h₁ : Boundaries S ≤ LinearMap.ker γ := by
    rintro z ⟨x,rfl⟩
    apply LinearMap.ext
    intro y
    exact (Submodule.Quotient.mk_eq_zero (Boundaries U)).mpr (hS x y)
  have h₂ : Boundaries T ≤ LinearMap.ker γ.flip := by
    rintro z ⟨y,rfl⟩
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero (Boundaries U)).mpr (hT x y)
  let q := γ.liftQ₂ (Boundaries S) (Boundaries T) h₁ h₂
  exact ((q.compl₂ T.moduleCatHomologyIso.hom.hom).comp S.moduleCatHomologyIso.hom.hom).compr₂
    U.moduleCatHomologyIso.inv.hom

/-- The descended operation has exactly the prescribed value on represented actual cycles. -/
theorem descend_cycleClass (S T U : ShortComplex (ModuleCat.{0} ℚ))
    (β : Cycles S →ₗ[ℚ] Cycles T →ₗ[ℚ] Cycles U)
    (hS : ∀ x y, β (S.moduleCatToCycles x) y ∈ Boundaries U)
    (hT : ∀ x y, β x (T.moduleCatToCycles y) ∈ Boundaries U)
    (x : Cycles S) (y : Cycles T) :
    descend S T U β hS hT (cycleClass S x) (cycleClass T y) = cycleClass U (β x y) := by
  unfold descend cycleClass
  erw [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  have hx : S.moduleCatHomologyIso.hom (S.moduleCatHomologyIso.inv ((Boundaries S).mkQ x)) =
      (Boundaries S).mkQ x := by
    exact congrArg (fun f => f ((Boundaries S).mkQ x)) S.moduleCatHomologyIso.inv_hom_id
  have hy : T.moduleCatHomologyIso.hom (T.moduleCatHomologyIso.inv ((Boundaries T).mkQ y)) =
      (Boundaries T).mkQ y := by
    exact congrArg (fun f => f ((Boundaries T).mkQ y)) T.moduleCatHomologyIso.inv_hom_id
  erw [hx, hy]
  rfl

/-- Descend a concrete operation on chain groups after proving its cycle and boundary identities. -/
def induced (S T U : ShortComplex (ModuleCat.{0} ℚ))
    (β : S.X₂ →ₗ[ℚ] T.X₂ →ₗ[ℚ] U.X₂)
    (hz : ∀ x : Cycles S, ∀ y : Cycles T, U.g (β x.val y.val) = 0)
    (hS : ∀ x : S.X₁, ∀ y : Cycles T, ∃ u : U.X₁, U.f u = β (S.f x) y.val)
    (hT : ∀ x : Cycles S, ∀ y : T.X₁, ∃ u : U.X₁, U.f u = β x.val (T.f y)) :
    S.homology →ₗ[ℚ] T.homology →ₗ[ℚ] U.homology :=
  descend S T U (restrictCycles S T U β hz)
    (fun x y => by
      obtain ⟨u,hu⟩ := hS x y
      exact ⟨u, Subtype.ext hu⟩)
    (fun x y => by
      obtain ⟨u,hu⟩ := hT x y
      exact ⟨u, Subtype.ext hu⟩)

end TernaryPoly.SingularLocalCap.Homology
