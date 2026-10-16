module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellChains
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section



/-!
# The cell chains already live in the symmetric space

`cellAtSpace n C` is the chain of the cell in the singular chains of `Space` (the interior of the
bordification); `cellAt_eq_embedding_map` : `cellAt n C = embedding_* (cellAtSpace n C)`.  Its simplices are
`nuSp ∘ (barycentric combination)`, the images in `Space` of affine simplices of positive definite forms.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory Finsupp TernaryPoly TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularCoverNaturality TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.FreeActionLinearization
  TernaryPeriodPolynomials.FreeResolution

/-- The space of trace-one positive forms as an object of `TopCat`. -/
abbrev SpaceTop : TopCat.{0} := TopCat.of Space

/-- The embedding of the symmetric space into the bordification, as a morphism of spaces. -/
def embeddingHom : SpaceTop ⟶ TopCat.of Glued :=
  TopCat.ofHom ⟨embedding, continuous_embedding⟩

/-- `nu` with values in the symmetric space itself. -/
def nuSp : C(PDMat, Space) := ⟨nuSpace, continuous_nuSpace⟩

/-- The singular simplex of the symmetric space attached to an ordered affine simplex of forms. -/
def affSingS {n : ℕ} (y : AffSimp PDMat n) : SingularSimplex SpaceTop n :=
  (SpaceTop.toSSetObjEquiv _).symm (nuSp.comp (affMap n y))

theorem projection_affSingS {n : ℕ} (y : AffSimp PDMat n) :
    CoveringSingularOrbits.projection embeddingHom n (affSingS y) = affSing y := by
  apply ((TopCat.of Glued).toSSetObjEquiv _).injective
  ext t
  simp [CoveringSingularOrbits.projection, affSingS, affSing, nu, nuSp, embeddingHom]
  rfl

/-- Realization in the singular chains of the symmetric space. -/
def realizeS (n : ℕ) : AffChain PDMat n →ₗ[ℚ] (underlyingChains SpaceTop).X n :=
  linearCombination ℚ (fun y => sing SpaceTop (affSingS y))

/-- The chain of a cell in the symmetric space itself (the interior of the bordification). -/
def cellAtSpace (n : ℕ) (C : Cell) : (underlyingChains SpaceTop).X n :=
  realizeS n (coneData.phi n C)

theorem map_sing_embedding {n : ℕ} (σ : SingularSimplex SpaceTop n) :
    ((underlyingMap embeddingHom).f n).hom (sing SpaceTop σ) =
      sing (TopCat.of Glued) (CoveringSingularOrbits.projection embeddingHom n σ) := by
  have h := congrArg (fun m => m.hom (1 : ℚ))
    (generator_map embeddingHom n σ)
  exact h

theorem realize_eq_map (n : ℕ) (c : AffChain PDMat n) :
    realize n c = ((underlyingMap embeddingHom).f n).hom (realizeS n c) := by
  have h : realize n =
      ((underlyingMap embeddingHom).f n).hom ∘ₗ realizeS n := by
    apply Finsupp.lhom_ext
    intro y a
    simp only [LinearMap.comp_apply, realize_single, realizeS, linearCombination_single, map_smul,
      map_sing_embedding, projection_affSingS]
  exact LinearMap.congr_fun h c

/-- **The cell chains of `Glued` are the images of chains of the symmetric space**:
`cellAt n C = (embedding)_* (cellAtSpace n C)`. -/
theorem cellAt_eq_embedding_map (n : ℕ) (C : Cell) :
    cellAt n C = ((underlyingMap embeddingHom).f n).hom (cellAtSpace n C) :=
  realize_eq_map n _

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
