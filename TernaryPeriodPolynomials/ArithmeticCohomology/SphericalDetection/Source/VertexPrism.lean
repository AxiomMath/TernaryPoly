module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneGroupCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RealTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def homogeneousVertexPrism {X V : Type*} [AddCommGroup V]
    (cochain : (Fin 3 → X) → V) (projection : X → X) (vertices : Fin 2 → X) : V :=
  cochain ![projection (vertices 0), vertices 0, vertices 1] -
    cochain ![projection (vertices 0), projection (vertices 1), vertices 1]

theorem homogeneousVertexPrism_differential {X V : Type*} [AddCommGroup V]
    (cochain : (Fin 3 → X) → V)
    (closed : ∀ vertices : Fin 4 → X,
      cochain ![vertices 1, vertices 2, vertices 3] - cochain ![vertices 0, vertices 2, vertices 3] +
        cochain ![vertices 0, vertices 1, vertices 3] - cochain ![vertices 0, vertices 1, vertices 2] = 0)
    (projection : X → X) (vertices : Fin 3 → X) :
    homogeneousVertexPrism cochain projection ![vertices 1, vertices 2] -
      homogeneousVertexPrism cochain projection ![vertices 0, vertices 2] +
      homogeneousVertexPrism cochain projection ![vertices 0, vertices 1] =
        cochain vertices - cochain (fun index => projection (vertices index)) := by
  have first := closed ![projection (vertices 0), vertices 0, vertices 1, vertices 2]
  have second := closed ![projection (vertices 0), projection (vertices 1), vertices 1, vertices 2]
  have third := closed ![projection (vertices 0), projection (vertices 1), projection (vertices 2), vertices 2]
  have tuple : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  have projected : ![projection (vertices 0), projection (vertices 1), projection (vertices 2)] =
      fun index => projection (vertices index) := by
    funext index
    fin_cases index <;> rfl
  change cochain ![vertices 0, vertices 1, vertices 2] -
    cochain ![projection (vertices 0), vertices 1, vertices 2] +
    cochain ![projection (vertices 0), vertices 0, vertices 2] -
    cochain ![projection (vertices 0), vertices 0, vertices 1] = 0 at first
  change cochain ![projection (vertices 1), vertices 1, vertices 2] -
    cochain ![projection (vertices 0), vertices 1, vertices 2] +
    cochain ![projection (vertices 0), projection (vertices 1), vertices 2] -
    cochain ![projection (vertices 0), projection (vertices 1), vertices 1] = 0 at second
  change cochain ![projection (vertices 1), projection (vertices 2), vertices 2] -
    cochain ![projection (vertices 0), projection (vertices 2), vertices 2] +
    cochain ![projection (vertices 0), projection (vertices 1), vertices 2] -
    cochain ![projection (vertices 0), projection (vertices 1), projection (vertices 2)] = 0 at third
  rw [tuple] at first
  rw [projected] at third
  change (cochain ![projection (vertices 1), vertices 1, vertices 2] -
      cochain ![projection (vertices 1), projection (vertices 2), vertices 2]) -
    (cochain ![projection (vertices 0), vertices 0, vertices 2] -
      cochain ![projection (vertices 0), projection (vertices 2), vertices 2]) +
    (cochain ![projection (vertices 0), vertices 0, vertices 1] -
      cochain ![projection (vertices 0), projection (vertices 1), vertices 1]) = _
  linear_combination (norm := abel) -first + second - third

def sourceProjectedRealTranslate {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (projection : RealGL3 → RealGL3)
    (real : RealGL3) (finite : FiniteGL) (vertices : Fin 3 → RealGL3) : HomogeneousPoly degree :=
  realCoefficientComponent degree character real⁻¹
    (source (fun index => projection (real * vertices index)) (atFinite finite))

def sourceRealVertexPrism {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (projection : RealGL3 → RealGL3)
    (real : RealGL3) (finite : FiniteGL) (vertices : Fin 2 → RealGL3) : HomogeneousPoly degree :=
  realCoefficientComponent degree character real⁻¹
    (homogeneousVertexPrism (fun vertices => source vertices (atFinite finite)) projection
      (fun index => real * vertices index))

/-- Straightening the translated vertices keeps the full twisted coefficient action. -/
theorem sourceRealTranslate_prism {degree : ℕ} (data : InducingData degree) (side : Side)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data side source)
    (projection : RealGL3 → RealGL3) (real : RealGL3) (finite : FiniteGL)
    (vertices : Fin 3 → RealGL3) :
    sourceRealTranslate data.chi source real finite vertices -
      sourceProjectedRealTranslate data.chi source projection real finite vertices =
    sourceRealVertexPrism data.chi source projection real finite ![vertices 1, vertices 2] -
      sourceRealVertexPrism data.chi source projection real finite ![vertices 0, vertices 2] +
      sourceRealVertexPrism data.chi source projection real finite ![vertices 0, vertices 1] := by
  have closed := homogeneousVertexPrism_differential (fun vertices => source vertices (atFinite finite))
    (fun vertices => cocycle.2.2.2 vertices (atFinite finite)) projection (fun index => real * vertices index)
  have translated_pair (first second : RealGL3) :
      (fun index : Fin 2 => real * ![first, second] index) = ![real * first, real * second] := by
    funext index
    fin_cases index <;> rfl
  rw [sourceRealVertexPrism, sourceRealVertexPrism, sourceRealVertexPrism,
    translated_pair, translated_pair, translated_pair, ← map_sub, ← map_add, closed]
  exact (map_sub (realCoefficientComponent degree data.chi real⁻¹) _ _).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
