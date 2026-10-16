module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyQuotient

@[expose] public section


open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace TernaryPoly.LatticeFirstCohomology
open LatticeTopCohomology

variable (A : Rep ℚ Lattice)

/-- The two actual lattice coboundary differences. -/
def differencePair : A →ₗ[ℚ] (Fin 2 → A) where
  toFun v := ![A.ρ first v-v,A.ρ second v-v]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> abel
  map_smul' r x := by
    funext i
    fin_cases i <;> simp [smul_sub]

/-- The signed curl in the genuine two-generator lattice cochain complex. -/
def curl : (Fin 2 → A) →ₗ[ℚ] A where
  toFun v := v 0+A.ρ first (v 1)-A.ρ second (v 0)-v 1
  map_add' x y := by simp; abel
  map_smul' r x := by simp [smul_add,smul_sub]

theorem curl_differencePair (v : A) : curl A (differencePair A v)=0 := by
  have hcomm : A.ρ first (A.ρ second v)=A.ρ second (A.ρ first v) := by
    rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul,mul_comm]
  change (A.ρ first v-v)+A.ρ first (A.ρ second v-v)-
    A.ρ second (A.ρ first v-v)-(A.ρ second v-v)=0
  rw [map_sub,map_sub,hcomm]
  abel

/-- Closed lattice pairs, with no Lie-algebra comparison assumed. -/
abbrev closedPairs := LinearMap.ker (curl A)

/-- Common differences as elements of the closed-pair space. -/
def commonDifference : A →ₗ[ℚ] closedPairs A :=
  (differencePair A).codRestrict _ (curl_differencePair A)

/-- The exact elementary quotient computing first lattice cohomology. -/
abbrev PairQuotient := closedPairs A ⧸ LinearMap.range (commonDifference A)

/-- The explicit three-term difference complex. -/
def pairComplex : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.mk (ModuleCat.ofHom (differencePair A)) (ModuleCat.ofHom (curl A)) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact curl_differencePair A)

/-- The degree-zero Hom coordinate is evaluation at the regular generator. -/
abbrev zeroCoordinate : ((homComplex A).X 0) ≃ₗ[ℚ] A := Rep.leftRegularHomEquiv A

private theorem regular_equivariant_single (f : P₀ ⟶ A) (g : Lattice) :
    f.hom (MonoidAlgebra.single g 1)=A.ρ g (f.hom (MonoidAlgebra.single 1 1)) := by
  obtain ⟨v,rfl⟩ := (Rep.leftRegularHomEquiv A).symm.surjective f
  change (A.ρ.leftRegularMapEquiv.symm v) (MonoidAlgebra.single g 1)=
    A.ρ g ((A.ρ.leftRegularMapEquiv.symm v) (MonoidAlgebra.single 1 1))
  simp

/-- The degree-zero Hom differential is the literal pair of generator differences. -/
theorem first_differential (f : P₀ ⟶ A) :
    edgeCoordinate A (((homComplex A).d 0 1).hom f)=differencePair A (zeroCoordinate A f) := by
  funext i
  change f.hom (d₁.hom (Finsupp.single i (MonoidAlgebra.single 1 1)))=_
  rw [d₁_single]
  simp only [one_smul,one_mul,map_sub]
  rw [regular_equivariant_single]
  fin_cases i <;> rfl

/-- Both generator-coordinate identifications commute with the actual Hom differential. -/
def coordinateIso : (homComplex A).sc' 0 1 2 ≅ pairComplex A :=
  ShortComplex.isoMk (zeroCoordinate A).toModuleIso (edgeCoordinate A).toModuleIso
    (topCoordinate A).toModuleIso (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (first_differential A f).symm) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (top_differential A f).symm)

/-- The actual Hom-complex first cohomology is the closed-pair quotient. -/
def homologyPairQuotientIso : (homComplex A).homology 1 ≅ ModuleCat.of ℚ (PairQuotient A) :=
  (homComplex A).homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (coordinateIso A) ≪≫ (pairComplex A).moduleCatHomologyIso

/-- Genuine group cohomology of the integral rank-two lattice, computed from its resolution. -/
def groupCohomologyPairQuotientIso : groupCohomology A 1 ≅ ModuleCat.of ℚ (PairQuotient A) :=
  groupCohomologyIso A 1 resolution ≪≫ homologyPairQuotientIso A

end TernaryPoly.LatticeFirstCohomology
