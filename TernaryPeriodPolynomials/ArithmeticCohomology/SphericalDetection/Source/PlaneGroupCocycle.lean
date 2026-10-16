module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneCuspidalAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def homogeneousGroupTwoCocycle {G : Type} [Group G] (representation : Rep ℂ G)
    (cochain : (Fin 3 → G) → representation)
    (equivariant : ∀ element vertices, cochain (fun index => element * vertices index) = representation.ρ element (cochain vertices))
    (closed : ∀ vertices : Fin 4 → G,
      cochain ![vertices 1, vertices 2, vertices 3] - cochain ![vertices 0, vertices 2, vertices 3] +
        cochain ![vertices 0, vertices 1, vertices 3] - cochain ![vertices 0, vertices 1, vertices 2] = 0) :
    groupCohomology.cocycles₂ representation :=
  ⟨fun pair => cochain ![1, pair.1, pair.1 * pair.2], by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro first second third
    have relation := closed ![1, first, first * second, first * second * third]
    have action := equivariant first ![1, second, second * third]
    have tuple : (fun index : Fin 3 => first * ![1, second, second * third] index) =
        ![first, first * second, first * second * third] := by
      funext index
      fin_cases index <;> simp [mul_assoc]
    rw [tuple] at action
    change cochain ![first, first * second, first * second * third] -
      cochain ![1, first * second, first * second * third] +
      cochain ![1, first, first * second * third] - cochain ![1, first, first * second] = 0 at relation
    rw [action, mul_assoc] at relation
    change cochain ![1, first * second, first * second * third] + cochain ![1, first, first * second] =
      representation.ρ first (cochain ![1, second, second * third]) + cochain ![1, first, first * (second * third)]
    rw [mul_assoc]
    linear_combination (norm := abel) -relation⟩

theorem sourcePlaneCuspidalValues_closed {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 4 → RealGL3) (base : AdelicGL) :
    sourcePlaneCuspidalValues data source cocycle ![vertices 1, vertices 2, vertices 3] base -
      sourcePlaneCuspidalValues data source cocycle ![vertices 0, vertices 2, vertices 3] base +
      sourcePlaneCuspidalValues data source cocycle ![vertices 0, vertices 1, vertices 3] base -
      sourcePlaneCuspidalValues data source cocycle ![vertices 0, vertices 1, vertices 2] base = 0 := by
  apply Subtype.ext
  funext argument
  have scaled := congrArg (fun polynomial : HomogeneousPoly degree =>
    normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) • polynomial)
    (cocycle.2.2.2 vertices (planeLevi argument 1 * base))
  simp only [smul_sub, smul_add, smul_zero] at scaled
  exact scaled

def sourcePlaneGroupHomogeneous {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealPlaneGroup) :
    realPlaneCuspidalRep degree data.cusp data.chi :=
  sourcePlaneCuspidalValues data source cocycle (fun index => realPlaneMatrix (vertices index)) 1

theorem sourcePlaneGroupHomogeneous_equivariant {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (element : RealPlaneGroup) (vertices : Fin 3 → RealPlaneGroup) :
    sourcePlaneGroupHomogeneous data source cocycle (fun index => element * vertices index) =
      (realPlaneCuspidalRep degree data.cusp data.chi).ρ element (sourcePlaneGroupHomogeneous data source cocycle vertices) := by
  simp only [sourcePlaneGroupHomogeneous, map_mul]
  exact sourcePlaneCuspidalValues_equivariant data source cocycle _ element

theorem sourcePlaneGroupHomogeneous_closed {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 4 → RealPlaneGroup) :
    sourcePlaneGroupHomogeneous data source cocycle ![vertices 1, vertices 2, vertices 3] -
      sourcePlaneGroupHomogeneous data source cocycle ![vertices 0, vertices 2, vertices 3] +
      sourcePlaneGroupHomogeneous data source cocycle ![vertices 0, vertices 1, vertices 3] -
      sourcePlaneGroupHomogeneous data source cocycle ![vertices 0, vertices 1, vertices 2] = 0 := by
  have tuple (first second third : RealPlaneGroup) :
      (fun index : Fin 3 => realPlaneMatrix (![first, second, third] index)) =
        ![realPlaneMatrix first, realPlaneMatrix second, realPlaneMatrix third] := by
    funext index
    fin_cases index <;> rfl
  simp only [sourcePlaneGroupHomogeneous, tuple]
  exact sourcePlaneCuspidalValues_closed data source cocycle (fun index => realPlaneMatrix (vertices index)) 1

/-- The given source determines an actual two-cocycle of the real plane parabolic. -/
def sourcePlaneGroupCocycle {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) :
    groupCohomology.cocycles₂ (realPlaneCuspidalRep degree data.cusp data.chi) :=
  homogeneousGroupTwoCocycle _ (sourcePlaneGroupHomogeneous data source cocycle)
    (sourcePlaneGroupHomogeneous_equivariant data source cocycle)
    (sourcePlaneGroupHomogeneous_closed data source cocycle)

theorem sourcePlaneGroupCocycle_apply {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (first second : RealPlaneGroup) (argument : BinaryAdelicGL) :
    (sourcePlaneGroupCocycle data source cocycle (first, second)).val argument =
      normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
        source ![1, realPlaneMatrix first, realPlaneMatrix first * realPlaneMatrix second] (planeLevi argument 1) := by
  change normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
    source (fun index => realPlaneMatrix (![1, first, first * second] index)) (planeLevi argument 1 * 1) = _
  have tuple : (fun index : Fin 3 => realPlaneMatrix (![1, first, first * second] index)) =
      ![1, realPlaneMatrix first, realPlaneMatrix first * realPlaneMatrix second] := by
    funext index
    fin_cases index <;> simp
  rw [tuple, mul_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
