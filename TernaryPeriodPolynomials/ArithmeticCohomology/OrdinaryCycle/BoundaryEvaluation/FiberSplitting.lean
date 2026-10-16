module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.CoefficientFunctor
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryPolynomial

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence ModThreeGoodAction
open OrdinaryBoundaryCommonRoot OrdinaryCovectors PolynomialGLAction SymmetricSpaceBoundaryFull
open SymmetricSpaceAllTopBoundary

/-- Principal six fixes every residue covector, so the restricted 26-fiber system splits literally. -/
theorem principalSix_rowMove (g : principalSix) (r : NonzeroCovector) : rowMove g.val r = r := by
  apply Subtype.ext
  change Matrix.vecMul r.val (reduction g.val).val = r.val
  have hg : reduction g.val = 1 := principalSix_le_three g.property
  rw [hg, Units.val_one, Matrix.vecMul_one]

/-- Coordinate projection onto each actual principal-six polynomial coefficient. -/
def coefficientFiberProjection (n : ℕ) (e : ℤ) (r : NonzeroCovector) :
    restrictedCoefficients n e ⟶ polynomialCoefficients n e :=
  Rep.ofHom ⟨LinearMap.proj r, fun g => LinearMap.ext (fun v => by
    change integralAction n e g.val (v (rowMove g.val r)) = integralAction n e g.val (v r)
    rw [principalSix_rowMove])⟩

/-- Coordinate insertion into the literal fixed residue fiber. -/
def coefficientFiberInsertion (n : ℕ) (e : ℤ) (r : NonzeroCovector) :
    polynomialCoefficients n e ⟶ restrictedCoefficients n e := by
  classical
  refine Rep.ofHom ⟨LinearMap.single ℚ (fun _ : NonzeroCovector => HomogeneousPoly n) r, fun g => LinearMap.ext (fun v => ?_)⟩
  funext s
  change (Pi.single r (integralAction n e g.val v) : Coefficients n) s =
    integralAction n e g.val ((Pi.single r v : Coefficients n) (rowMove g.val s))
  rw [principalSix_rowMove]
  by_cases h : s = r
  · subst s
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, map_zero]

/-- The entire actual coefficient identity is the finite sum of its 26 literal coordinate splittings. -/
theorem coefficientFiber_sum (n : ℕ) (e : ℤ) :
    ∑ r : NonzeroCovector, coefficientFiberProjection n e r ≫ coefficientFiberInsertion n e r =
      𝟙 (restrictedCoefficients n e) := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change (∑ r : NonzeroCovector, Pi.single r (v r)) = v
  exact Finset.univ_sum_single v

/-- Surjectivity of an additive natural transformation passes to an actual finite coefficient splitting. -/
theorem natural_surjective_of_finite_splitting {C : Type*} [Category C] [Preadditive C]
    (F T : C ⥤ ModuleCat ℚ) [F.Additive] [T.Additive] (α : F ⟶ T)
    (U V : C) {ι : Type} [Fintype ι]
    (p : ι → (V ⟶ U)) (j : ι → (U ⟶ V))
    (hid : ∑ i, p i ≫ j i = 𝟙 V)
    (hsurj : Function.Surjective (α.app U).hom) :
    Function.Surjective (α.app V).hom := by
  classical
  intro y
  choose x hx using fun i => hsurj ((T.map (p i)).hom y)
  refine ⟨∑ i, (F.map (j i)).hom (x i), ?_⟩
  rw [map_sum]
  trans ∑ i, (T.map (j i)).hom ((T.map (p i)).hom y)
  · apply Finset.sum_congr rfl
    intro i _
    have hn := congrArg (fun f => f.hom (x i)) (α.naturality (j i))
    change (α.app V).hom ((F.map (j i)).hom (x i)) = (T.map (j i)).hom ((α.app U).hom (x i)) at hn
    rw [hx] at hn
    exact hn
  · have hmap : ∑ i, T.map (p i ≫ j i) = 𝟙 (T.obj V) := by
      rw [← Functor.map_sum, hid, CategoryTheory.Functor.map_id]
    have hv := congrArg (fun f => f.hom y) hmap
    simp only [Functor.map_comp, ModuleCat.hom_sum, LinearMap.sum_apply] at hv
    exact hv

end TernaryPoly.OrdinaryBoundaryActualEvaluation
