module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalWindow

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

/-- Literal submodules of an actual real bicomplex stable under both actual differentials. -/
structure BicomplexSubmodules (K : RealBicomplex) where
  term : ∀ p q, Submodule ℝ ((K.X p).X q)
  horizontal_mem : ∀ p q (x : (K.X p).X q), x ∈ term p q → horizontal K p q x ∈ term (p+1) q
  vertical_mem : ∀ p q (x : (K.X p).X q), x ∈ term p q → vertical K p q x ∈ term p (q+1)

namespace BicomplexSubmodules
variable {K : RealBicomplex} (P : BicomplexSubmodules K)

/-- Restricted literal vertical differential. -/
def verticalD (p q : ℕ) : P.term p q →ₗ[ℝ] P.term p (q+1) where
  toFun x := ⟨vertical K p q x.val,P.vertical_mem p q x.val x.property⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

/-- Restricted literal horizontal differential. -/
def horizontalD (p q : ℕ) : P.term p q →ₗ[ℝ] P.term (p+1) q where
  toFun x := ⟨horizontal K p q x.val,P.horizontal_mem p q x.val x.property⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

/-- The genuine subcomplex in each column. -/
def column (p : ℕ) : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of ℝ (P.term p q))
    (fun q => ModuleCat.ofHom (P.verticalD p q)) (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subtype.ext (vertical_squared K p q x.val))

/-- The genuine horizontal cochain map between subcomplex columns. -/
def horizontalChain (p : ℕ) : P.column p ⟶ P.column (p+1) :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (P.horizontalD p q)) (by
    intro q
    simp only [column,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (horizontal_vertical K p q x.val))

/-- The actual bicomplex on the stable submodules. -/
def toBicomplex : RealBicomplex :=
  CochainComplex.of P.column P.horizontalChain (by
    intro p
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext (horizontal_squared K p q x.val))

theorem vertical_eq (p q : ℕ) : vertical P.toBicomplex p q = P.verticalD p q := by
  simp only [vertical,toBicomplex,column,CochainComplex.of_d,ModuleCat.hom_ofHom]
  rfl

theorem horizontal_eq (p q : ℕ) : horizontal P.toBicomplex p q = P.horizontalD p q := by
  simp only [horizontal,toBicomplex,CochainComplex.of_d]
  rfl

/-- Actual inclusion of each supported column into its original column. -/
def columnInclusion (p : ℕ) : P.column p ⟶ K.X p :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (P.term p q).subtype) (by
    intro q
    simp only [column,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- Literal bicomplex inclusion, the eventual support-forgetting map of the total span. -/
def inclusion : P.toBicomplex ⟶ K :=
  CochainComplex.ofHom P.columnInclusion (by
    intro p
    simp only [toBicomplex,CochainComplex.of_d]
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end BicomplexSubmodules
end TernaryPoly.SmoothSingularGlobal
