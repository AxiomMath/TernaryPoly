module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.DoubleCosetFinite
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Level

@[expose] public section


/-!
# The spherical level `GL₂(Ẑ)` and its double cosets

`GL₂(Ẑ)` is a compact open subgroup of `GL₂(𝔸_f)`, so every double coset `K γ K` is a finite
union of left cosets.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.RepresentationTheory

/-- `GL₂(Ẑ)` inside `GL₂(𝔸_f)`. -/
def sphericalFinite : Subgroup BinaryFiniteGL :=
  (GeneralLinearGroup.map integralEmbedding (n := Fin 2)).range

theorem sphericalFinite_isOpen : IsOpen (sphericalFinite : Set BinaryFiniteGL) := by
  have := BinaryLevel.integralMap_isOpenMap (size := 2) _ isOpen_univ
  simpa [sphericalFinite, Set.image_univ] using this

theorem sphericalFinite_isCompact : IsCompact (sphericalFinite : Set BinaryFiniteGL) := by
  let : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  exact isCompact_range BinaryLevel.integralMap_continuous

instance sphericalFinite_finiteQuotient (γ : BinaryFiniteGL) :
    Finite (sphericalFinite ⧸ conjIntersection sphericalFinite γ) := by
  have : CompactSpace sphericalFinite := isCompact_iff_compactSpace.mp sphericalFinite_isCompact
  apply Subgroup.quotient_finite_of_isOpen
  have hconj : IsOpen ((sphericalFinite.map (MulAut.conj γ).toMonoidHom : Subgroup BinaryFiniteGL) :
      Set BinaryFiniteGL) := by
    rw [Subgroup.coe_map]
    have hmap : IsOpenMap (fun x : BinaryFiniteGL => γ * x * γ⁻¹) :=
      ((Homeomorph.mulLeft γ).trans (Homeomorph.mulRight γ⁻¹)).isOpenMap
    exact hmap _ sphericalFinite_isOpen
  exact hconj.preimage continuous_subtype_val

end TernaryPeriodPolynomials.RepresentationTheory
