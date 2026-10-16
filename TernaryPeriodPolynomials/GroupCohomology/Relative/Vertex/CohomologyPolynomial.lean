module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyDiagonal
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Actions

@[expose] public section

open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open RelativeStabilizerParameters RadicalFirstCohomologyLattice RadicalTopCohomology
open RadicalCoinvariantAlgebra LowDegreeHochschildSerre

/-- Actual integral polynomial coefficients on the two proved semidirect products. -/
abbrev planePolynomial (n : ℕ) : Rep ℚ (planeRadical ⋊[planeAction] GL2) :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp planeLift)
abbrev linePolynomial (n : ℕ) : Rep ℚ (lineRadical ⋊[lineAction] (ℤˣ × Gamma)) :=
  Rep.of ((PolynomialGLAction.integralAction n 0).comp lineLift)

@[simp] theorem planePolynomial_inl (n : ℕ) (u : planeRadical) :
    (planePolynomial n).ρ (nIn planeAction u) = PolynomialGLAction.integralAction n 0 u.val := by
  change PolynomialGLAction.integralAction n 0 (planeLift (SemidirectProduct.inl u)) = _
  simp [planeLift]

@[simp] theorem linePolynomial_inl (n : ℕ) (u : lineRadical) :
    (linePolynomial n).ρ (nIn lineAction u) = PolynomialGLAction.integralAction n 0 u.val := by
  change PolynomialGLAction.integralAction n 0 (lineLift (SemidirectProduct.inl u)) = _
  simp [lineLift]

@[simp] theorem planePolynomial_inr (n : ℕ) (M : GL2) :
    (planePolynomial n).ρ (qIn planeAction M) = PolynomialGLAction.integralAction n 0 (planeLevi M) := by
  change PolynomialGLAction.integralAction n 0 (planeLift (SemidirectProduct.inr M)) = _
  simp [planeLift]

@[simp] theorem linePolynomial_inr (n : ℕ) (q : ℤˣ × Gamma) :
    (linePolynomial n).ρ (qIn lineAction q) = PolynomialGLAction.integralAction n 0 (lineLevi q) := by
  change PolynomialGLAction.integralAction n 0 (lineLift (SemidirectProduct.inr q)) = _
  simp [lineLift]

/-- The identity coefficient map between the literal restricted polynomial modules. -/
def planeRadicalCoefficient (n : ℕ) :
    Rep.res (MonoidHom.id planeRadical) (radicalRep planeAction (planePolynomial n)) ⟶
      planeSubgroupRep n := Rep.ofHom ⟨(LinearMap.id : H n →ₗ[ℚ] H n), fun u => by
        change LinearMap.id.comp ((planePolynomial n).ρ (nIn planeAction u)) =
          (PolynomialGLAction.integralAction n 0 u.val).comp LinearMap.id
        simpa only [LinearMap.id_comp,LinearMap.comp_id] using planePolynomial_inl n u⟩

def lineRadicalCoefficient (n : ℕ) :
    Rep.res (MonoidHom.id lineRadical) (radicalRep lineAction (linePolynomial n)) ⟶
      lineSubgroupRep n := Rep.ofHom ⟨(LinearMap.id : H n →ₗ[ℚ] H n), fun u => by
        change LinearMap.id.comp ((linePolynomial n).ρ (nIn lineAction u)) =
          (PolynomialGLAction.integralAction n 0 u.val).comp LinearMap.id
        simpa only [LinearMap.id_comp,LinearMap.comp_id] using linePolynomial_inl n u⟩

/-- Genuine all-degree comparison with the actual radical cohomology. -/
def planeRadicalIso (n k : ℕ) :
    groupCohomology (radicalRep planeAction (planePolynomial n)) k ≅
      groupCohomology (planeSubgroupRep n) k :=
  groupCohomology.mapIso (MulEquiv.refl _) (LinearEquiv.refl ℚ (H n)) (fun u => by
    change LinearMap.id.comp ((planePolynomial n).ρ (nIn planeAction u)) =
      (PolynomialGLAction.integralAction n 0 u.val).comp LinearMap.id
    simpa only [LinearMap.id_comp,LinearMap.comp_id] using planePolynomial_inl n u) k

def lineRadicalIso (n k : ℕ) :
    groupCohomology (radicalRep lineAction (linePolynomial n)) k ≅
      groupCohomology (lineSubgroupRep n) k :=
  groupCohomology.mapIso (MulEquiv.refl _) (LinearEquiv.refl ℚ (H n)) (fun u => by
    change LinearMap.id.comp ((linePolynomial n).ρ (nIn lineAction u)) =
      (PolynomialGLAction.integralAction n 0 u.val).comp LinearMap.id
    simpa only [LinearMap.id_comp,LinearMap.comp_id] using linePolynomial_inl n u) k

theorem planeRadicalIso_hom (n k : ℕ) : (planeRadicalIso n k).hom =
    groupCohomology.map (MonoidHom.id _) (planeRadicalCoefficient n) k := rfl

theorem lineRadicalIso_hom (n k : ℕ) : (lineRadicalIso n k).hom =
    groupCohomology.map (MonoidHom.id _) (lineRadicalCoefficient n) k := rfl

/-- Actual inverse conjugation and coefficients commute with the radical comparison in every degree. -/
theorem planeRadicalIso_natural (n k : ℕ) (M : GL2) :
    (planeRadicalIso n k).hom ≫
      groupCohomology.map (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) k =
    groupCohomology.map (planeAction M⁻¹).toMonoidHom
      (coefficientHom planeAction (planePolynomial n) M) k ≫ (planeRadicalIso n k).hom := by
  rw [planeRadicalIso_hom]
  have hc : groupCohomology.cochainsMap (MonoidHom.id _) (planeRadicalCoefficient n) ≫
      groupCohomology.cochainsMap (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) =
    cochainsAction planeAction (planePolynomial n) M ≫
      groupCohomology.cochainsMap (MonoidHom.id _) (planeRadicalCoefficient n) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext g
    change PolynomialGLAction.integralAction n 0 (planeElement M 0)
      (c (fun i => planeSubgroupChange M (g i))) =
      (planePolynomial n).ρ (qIn planeAction M) (c (fun i => planeAction M⁻¹ (g i)))
    rw [planePolynomial_inr,planeAction_inverse]
    rfl
  exact (HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f k) hc).trans
      (HomologicalComplex.homologyMap_comp _ _ k))

theorem lineRadicalIso_natural (n k : ℕ) (ε : ℤˣ × ℤˣ) :
    (lineRadicalIso n k).hom ≫
      groupCohomology.map (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) k =
    groupCohomology.map (lineAction (lineDiagonal ε)⁻¹).toMonoidHom
      (coefficientHom lineAction (linePolynomial n) (lineDiagonal ε)) k ≫ (lineRadicalIso n k).hom := by
  rw [lineRadicalIso_hom]
  have hc : groupCohomology.cochainsMap (MonoidHom.id _) (lineRadicalCoefficient n) ≫
      groupCohomology.cochainsMap (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) =
    cochainsAction lineAction (linePolynomial n) (lineDiagonal ε) ≫
      groupCohomology.cochainsMap (MonoidHom.id _) (lineRadicalCoefficient n) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext g
    change PolynomialGLAction.integralAction n 0 (diagonalHom ε)
      (c (fun i => lineSubgroupChange ε (g i))) =
      (linePolynomial n).ρ (qIn lineAction (lineDiagonal ε))
        (c (fun i => lineAction (lineDiagonal ε)⁻¹ (g i)))
    rw [linePolynomial_inr,lineAction_inverse_diagonal,lineLevi_diagonal]
  exact (HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f k) hc).trans
      (HomologicalComplex.homologyMap_comp _ _ k))

theorem planeRadicalIso_action (n k : ℕ) (M : GL2)
    (v : groupCohomology (radicalRep planeAction (planePolynomial n)) k) :
    (planeRadicalIso n k).hom ((cohomologyRep planeAction (planePolynomial n) k).ρ M v) =
      groupCohomology.map (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) k
        ((planeRadicalIso n k).hom v) := by
  have he := congrArg (fun f => f v) (planeRadicalIso_natural n k M)
  exact he.symm

theorem lineRadicalIso_action (n k : ℕ) (ε : ℤˣ × ℤˣ)
    (v : groupCohomology (radicalRep lineAction (linePolynomial n)) k) :
    (lineRadicalIso n k).hom
      ((cohomologyRep lineAction (linePolynomial n) k).ρ (lineDiagonal ε) v) =
      groupCohomology.map (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) k
        ((lineRadicalIso n k).hom v) := by
  have he := congrArg (fun f => f v) (lineRadicalIso_natural n k ε)
  exact he.symm

end TernaryPoly.RelativeVertexCohomology
