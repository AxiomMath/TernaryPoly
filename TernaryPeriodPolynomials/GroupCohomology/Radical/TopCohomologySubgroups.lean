module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyLine

@[expose] public section

open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.RadicalTopCohomology
open LatticeTopCohomology RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The actual matrix-subgroup cohomology is identified through the proved parameter isomorphism. -/
def planeParameterH2Iso (n : ℕ) :
    groupCohomology (planeRep n) 2 ≅ groupCohomology (planeSubgroupRep n) 2 :=
  groupCohomology.mapIso planeParamEquiv (LinearEquiv.refl ℚ (H n)) (fun _ => rfl) 2

def lineParameterH2Iso (n : ℕ) :
    groupCohomology (lineRep n) 2 ≅ groupCohomology (lineSubgroupRep n) 2 :=
  groupCohomology.mapIso lineParamEquiv (LinearEquiv.refl ℚ (H n)) (fun _ => rfl) 2

def planeParameterCoefficient (n : ℕ) :
    Rep.res planeParamEquiv.toMonoidHom (planeSubgroupRep n) ⟶ planeRep n :=
  Rep.ofHom ⟨(LinearMap.id : H n →ₗ[ℚ] H n), fun _ => rfl⟩

def lineParameterCoefficient (n : ℕ) :
    Rep.res lineParamEquiv.toMonoidHom (lineSubgroupRep n) ⟶ lineRep n :=
  Rep.ofHom ⟨(LinearMap.id : H n →ₗ[ℚ] H n), fun _ => rfl⟩

theorem planeParameterH2Iso_inv (n : ℕ) : (planeParameterH2Iso n).inv =
    groupCohomology.map planeParamEquiv.toMonoidHom (planeParameterCoefficient n) 2 := rfl

theorem lineParameterH2Iso_inv (n : ℕ) : (lineParameterH2Iso n).inv =
    groupCohomology.map lineParamEquiv.toMonoidHom (lineParameterCoefficient n) 2 := rfl

/-- Inverse Levi conjugation on the actual integral plane subgroup. -/
def planeSubgroupChange (M : GL2) : planeRadical ≃* planeRadical :=
  (planeParamEquiv.symm.trans (matrixLattice M⁻¹)).trans planeParamEquiv

/-- Inverse diagonal conjugation on the actual integral line subgroup. -/
def lineSubgroupChange (ε : ℤˣ × ℤˣ) : lineRadical ≃* lineRadical :=
  (lineParamEquiv.symm.trans (lineLattice ε)).trans lineParamEquiv

@[simp] theorem planeSubgroupChange_parameter (M : GL2) (g : Lattice) :
    planeSubgroupChange M (planeParamEquiv g) = planeParamEquiv (matrixLattice M⁻¹ g) := by
  simp [planeSubgroupChange]

@[simp] theorem lineSubgroupChange_parameter (ε : ℤˣ × ℤˣ) (g : Lattice) :
    lineSubgroupChange ε (lineParamEquiv g) = lineParamEquiv (lineLattice ε g) := by
  simp [lineSubgroupChange]

theorem planeSubgroupChange_conjugation (M : GL2) (g : planeRadical) :
    (planeSubgroupChange M g).val = (planeElement M 0)⁻¹ * g.val * planeElement M 0 := by
  obtain ⟨u,rfl⟩ := planeParamEquiv.surjective g
  rw [planeSubgroupChange_parameter]
  change planeHom (matrixLattice M⁻¹ u) = (planeElement M 0)⁻¹ * planeHom u * planeElement M 0
  have h := congrArg (fun z => (planeElement M 0)⁻¹ * z) (plane_inverse_commute M u)
  simpa [mul_assoc] using h

theorem lineSubgroupChange_conjugation (ε : ℤˣ × ℤˣ) (g : lineRadical) :
    (lineSubgroupChange ε g).val = (diagonalHom ε)⁻¹ * g.val * diagonalHom ε := by
  obtain ⟨u,rfl⟩ := lineParamEquiv.surjective g
  rw [lineSubgroupChange_parameter]
  change lineHom (lineLattice ε u) = (diagonalHom ε)⁻¹ * lineHom u * diagonalHom ε
  have h := congrArg (fun z => (diagonalHom ε)⁻¹ * z) (line_inverse_commute ε u)
  simpa [mul_assoc] using h

def planeSubgroupCoefficientHom (n : ℕ) (M : GL2) :
    Rep.res (planeSubgroupChange M).toMonoidHom (planeSubgroupRep n) ⟶ planeSubgroupRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n 0 (planeElement M 0), fun g => by
    change PolynomialGLAction.integralAction n 0 (planeElement M 0) *
      PolynomialGLAction.integralAction n 0 (planeSubgroupChange M g).val =
      PolynomialGLAction.integralAction n 0 g.val *
        PolynomialGLAction.integralAction n 0 (planeElement M 0)
    rw [← map_mul, ← map_mul, planeSubgroupChange_conjugation]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]⟩

def lineSubgroupCoefficientHom (n : ℕ) (ε : ℤˣ × ℤˣ) :
    Rep.res (lineSubgroupChange ε).toMonoidHom (lineSubgroupRep n) ⟶ lineSubgroupRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n 0 (diagonalHom ε), fun g => by
    change PolynomialGLAction.integralAction n 0 (diagonalHom ε) *
      PolynomialGLAction.integralAction n 0 (lineSubgroupChange ε g).val =
      PolynomialGLAction.integralAction n 0 g.val *
        PolynomialGLAction.integralAction n 0 (diagonalHom ε)
    rw [← map_mul, ← map_mul, lineSubgroupChange_conjugation]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]⟩

/-- Literal conjugation/coefficient action on actual plane-subgroup H². -/
def planeSubgroupH2Action (n : ℕ) (M : GL2) :
    groupCohomology (planeSubgroupRep n) 2 ⟶ groupCohomology (planeSubgroupRep n) 2 :=
  groupCohomology.map (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) 2

def lineSubgroupH2Action (n : ℕ) (ε : ℤˣ × ℤˣ) :
    groupCohomology (lineSubgroupRep n) 2 ⟶ groupCohomology (lineSubgroupRep n) 2 :=
  groupCohomology.map (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) 2

@[reassoc] theorem planeParameterCohomology_natural (n k : ℕ) (M : GL2) :
    groupCohomology.map planeParamEquiv.toMonoidHom (planeParameterCoefficient n) k ≫
      groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHom n M) k =
    groupCohomology.map (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) k ≫
      groupCohomology.map planeParamEquiv.toMonoidHom (planeParameterCoefficient n) k := by
  have hc : groupCohomology.cochainsMap planeParamEquiv.toMonoidHom (planeParameterCoefficient n) ≫
      groupCohomology.cochainsMap (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHom n M) =
    groupCohomology.cochainsMap (planeSubgroupChange M).toMonoidHom (planeSubgroupCoefficientHom n M) ≫
      groupCohomology.cochainsMap planeParamEquiv.toMonoidHom (planeParameterCoefficient n) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext g
    change PolynomialGLAction.integralAction n 0 (planeElement M 0)
      (c (fun i => planeParamEquiv (matrixLattice M⁻¹ (g i)))) =
      PolynomialGLAction.integralAction n 0 (planeElement M 0)
        (c (fun i => planeSubgroupChange M (planeParamEquiv (g i))))
    congr 2
    funext i
    exact (planeSubgroupChange_parameter M (g i)).symm
  exact (HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    ((congrArg (fun F => HomologicalComplex.homologyMap F k) hc).trans
      (HomologicalComplex.homologyMap_comp _ _ k))

@[reassoc] theorem lineParameterCohomology_natural (n k : ℕ) (ε : ℤˣ × ℤˣ) :
    groupCohomology.map lineParamEquiv.toMonoidHom (lineParameterCoefficient n) k ≫
      groupCohomology.map (lineLattice ε).toMonoidHom (lineCoefficientHom n ε) k =
    groupCohomology.map (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) k ≫
      groupCohomology.map lineParamEquiv.toMonoidHom (lineParameterCoefficient n) k := by
  have hc : groupCohomology.cochainsMap lineParamEquiv.toMonoidHom (lineParameterCoefficient n) ≫
      groupCohomology.cochainsMap (lineLattice ε).toMonoidHom (lineCoefficientHom n ε) =
    groupCohomology.cochainsMap (lineSubgroupChange ε).toMonoidHom (lineSubgroupCoefficientHom n ε) ≫
      groupCohomology.cochainsMap lineParamEquiv.toMonoidHom (lineParameterCoefficient n) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext g
    change PolynomialGLAction.integralAction n 0 (diagonalHom ε)
      (c (fun i => lineParamEquiv (lineLattice ε (g i)))) =
      PolynomialGLAction.integralAction n 0 (diagonalHom ε)
        (c (fun i => lineSubgroupChange ε (lineParamEquiv (g i))))
    congr 2
    funext i
    exact (lineSubgroupChange_parameter ε (g i)).symm
  exact (HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    ((congrArg (fun F => HomologicalComplex.homologyMap F k) hc).trans
      (HomologicalComplex.homologyMap_comp _ _ k))

@[reassoc] theorem planeParameterH2Iso_action (n : ℕ) (M : GL2) :
    (planeParameterH2Iso n).inv ≫ planeH2Action n M =
      planeSubgroupH2Action n M ≫ (planeParameterH2Iso n).inv := by
  rw [planeParameterH2Iso_inv]
  exact planeParameterCohomology_natural n 2 M

@[reassoc] theorem lineParameterH2Iso_action (n : ℕ) (ε : ℤˣ × ℤˣ) :
    (lineParameterH2Iso n).inv ≫ lineH2Action n ε =
      lineSubgroupH2Action n ε ≫ (lineParameterH2Iso n).inv := by
  rw [lineParameterH2Iso_inv]
  exact lineParameterCohomology_natural n 2 ε

/-- Actual integral plane-radical H² has no fixed vectors under its actual Levi normalizer. -/
theorem planeSubgroupH2_fixed_zero (n : ℕ) (v : groupCohomology (planeSubgroupRep n) 2)
    (hv : ∀ M : GL2, planeSubgroupH2Action n M v = v) : v = 0 := by
  apply (ModuleCat.mono_iff_injective (planeParameterH2Iso n).inv).mp inferInstance
  rw [map_zero]
  apply planeH2_fixed_zero
  intro M
  have h := congrArg (fun f => f v) (planeParameterH2Iso_action n M)
  change planeH2Action n M ((planeParameterH2Iso n).inv v) =
    (planeParameterH2Iso n).inv (planeSubgroupH2Action n M v) at h
  simpa [hv M] using h

/-- Actual integral line-radical H² has no fixed vectors under its diagonal normalizer subgroup. -/
theorem lineSubgroupH2_fixed_zero (n : ℕ) (v : groupCohomology (lineSubgroupRep n) 2)
    (hv : ∀ ε : ℤˣ × ℤˣ, lineSubgroupH2Action n ε v = v) : v = 0 := by
  apply (ModuleCat.mono_iff_injective (lineParameterH2Iso n).inv).mp inferInstance
  rw [map_zero]
  apply lineH2_fixed_zero
  intro ε
  have h := congrArg (fun f => f v) (lineParameterH2Iso_action n ε)
  change lineH2Action n ε ((lineParameterH2Iso n).inv v) =
    (lineParameterH2Iso n).inv (lineSubgroupH2Action n ε v) at h
  simpa [hv ε] using h

end TernaryPoly.RadicalTopCohomology
