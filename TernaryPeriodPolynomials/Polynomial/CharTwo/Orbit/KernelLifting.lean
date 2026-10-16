module

public import TernaryPeriodPolynomials.Building.Good.OrbitRelations
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section


/-! Conditional lifting from the three reference relations. The inclusion
`ker orbitMap ≤ relations` is an explicit completeness hypothesis throughout;
this file does not prove that inclusion. -/

noncomputable section
namespace TernaryPoly.OrbitKernelLifting

open GoodBuilding GoodChainComplex GoodUnimodularOrbit GoodOrbitRelations
open ReferenceCoefficientMatrices

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The exact three relations required of the reference value in a K-representation. -/
structure ReferenceRelations (ρ : Representation ℚ K E) (f : E) : Prop where
  norm : f + ρ aK f + ρ (aK ^ 2) f = 0
  cyclic : ρ cK f = f
  swap : ρ sK f = -f

/-- Evaluation on the free orbit sends its generator at g to the actual translate of f. -/
def freeEvaluation (ρ : Representation ℚ K E) (f : E) : FreeOrbit →ₗ[ℚ] E :=
  Finsupp.lsum ℚ fun g => LinearMap.toSpanSingleton ℚ E (ρ g f)

@[simp] theorem freeEvaluation_delta (ρ : Representation ℚ K E) (f : E) (g : K) :
    freeEvaluation ρ f (delta g) = ρ g f := by
  simp only [freeEvaluation, delta, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    one_smul]

/-- Each translated norm relation is annihilated by free evaluation. -/
theorem freeEvaluation_normRelation (ρ : Representation ℚ K E) (f : E)
    (hf : ReferenceRelations ρ f) (g : K) : freeEvaluation ρ f (normRelation g) = 0 := by
  rw [normRelation, map_add, map_add, freeEvaluation_delta,
    freeEvaluation_delta, freeEvaluation_delta]
  simpa only [map_add, map_mul, Module.End.mul_apply, map_zero] using congrArg (ρ g) hf.norm

/-- Each translated cyclic relation is annihilated by free evaluation. -/
theorem freeEvaluation_cyclicRelation (ρ : Representation ℚ K E) (f : E)
    (hf : ReferenceRelations ρ f) (g : K) : freeEvaluation ρ f (cyclicRelation g) = 0 := by
  rw [cyclicRelation, map_sub, freeEvaluation_delta, freeEvaluation_delta,
    map_mul, Module.End.mul_apply, hf.cyclic, sub_self]

/-- Each translated orientation relation is annihilated by free evaluation. -/
theorem freeEvaluation_swapRelation (ρ : Representation ℚ K E) (f : E)
    (hf : ReferenceRelations ρ f) (g : K) : freeEvaluation ρ f (swapRelation g) = 0 := by
  rw [swapRelation, map_add, freeEvaluation_delta, freeEvaluation_delta,
    map_mul, Module.End.mul_apply, hf.swap, map_neg, neg_add_cancel]

/-- The whole supplied relation submodule is killed, without assuming completeness. -/
theorem relations_le_ker_freeEvaluation (ρ : Representation ℚ K E) (f : E)
    (hf : ReferenceRelations ρ f) : relations ≤ LinearMap.ker (freeEvaluation ρ f) := by
  apply Submodule.span_le.mpr
  intro x hx
  change freeEvaluation ρ f x = 0
  rcases hx with (⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨g, rfl⟩
  · exact freeEvaluation_normRelation ρ f hf g
  · exact freeEvaluation_cyclicRelation ρ f hf g
  · exact freeEvaluation_swapRelation ρ f hf g

/-- Under the explicit completeness inclusion, evaluation descends through the
actual orbit-map kernel and its first-isomorphism equivalence onto cycles. -/
def liftMap (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f) :
    GoodChainComplex.Cycles →ₗ[ℚ] E :=
  ((LinearMap.ker orbitMap).liftQ (freeEvaluation ρ f)
    (hcomplete.trans (relations_le_ker_freeEvaluation ρ f hf))).comp
    (orbitMap.quotKerEquivOfSurjective orbitMap_surjective).symm.toLinearMap

/-- The descended map agrees exactly with free evaluation on every orbit-map image. -/
theorem liftMap_orbitMap (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f) (x : FreeOrbit) :
    liftMap hcomplete ρ f hf (orbitMap x) = freeEvaluation ρ f x := by
  change (LinearMap.ker orbitMap).liftQ (freeEvaluation ρ f)
    (hcomplete.trans (relations_le_ker_freeEvaluation ρ f hf))
    ((orbitMap.quotKerEquivOfSurjective orbitMap_surjective).symm (orbitMap x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The value on each actual orbit generator is the stipulated translate of f. -/
@[simp] theorem liftMap_orbit (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f) (g : K) :
    liftMap hcomplete ρ f hf (complex.cyclesAction g referenceApartment) = ρ g f := by
  rw [← orbitMap_delta, liftMap_orbitMap, freeEvaluation_delta]

/-- In particular the constructed extension has the supplied reference value. -/
@[simp] theorem liftMap_reference (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f) :
    liftMap hcomplete ρ f hf referenceApartment = f := by
  simpa only [map_one, Module.End.one_apply] using liftMap_orbit hcomplete ρ f hf (1 : K)

/-- Equivariance on orbit generators extends to every cycle by the actual orbit-span theorem. -/
theorem liftMap_equivariant (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f)
    (g : K) (c : GoodChainComplex.Cycles) :
    liftMap hcomplete ρ f hf (complex.cyclesAction g c) =
      ρ g (liftMap hcomplete ρ f hf c) := by
  have hm : (liftMap hcomplete ρ f hf).comp (complex.cyclesAction g) =
      (ρ g).comp (liftMap hcomplete ρ f hf) := by
    apply GoodOrbitSpan.orbit_ext
    intro h
    simp only [LinearMap.comp_apply]
    have ha : complex.cyclesAction g (complex.cyclesAction h referenceApartment) =
        complex.cyclesAction (g * h) referenceApartment := by
      rw [map_mul, Module.End.mul_apply]
    rw [ha, liftMap_orbit, liftMap_orbit, map_mul, Module.End.mul_apply]
  exact LinearMap.congr_fun hm c

/-- An equivariant map with the supplied reference value is necessarily the constructed map. -/
theorem liftMap_unique (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f)
    (φ : GoodChainComplex.Cycles →ₗ[ℚ] E)
    (hφ : ∀ (g : K) (c : GoodChainComplex.Cycles), φ (complex.cyclesAction g c) = ρ g (φ c))
    (href : φ referenceApartment = f) : φ = liftMap hcomplete ρ f hf := by
  apply GoodOrbitSpan.orbit_ext
  intro g
  rw [hφ, href, liftMap_orbit]

/-- Exact conditional extension and uniqueness, with kernel completeness visible in the statement. -/
theorem existsUnique_equivariant_extension (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f) :
    ∃! φ : GoodChainComplex.Cycles →ₗ[ℚ] E,
      (∀ (g : K) (c : GoodChainComplex.Cycles), φ (complex.cyclesAction g c) = ρ g (φ c)) ∧
        φ referenceApartment = f :=
  ⟨liftMap hcomplete ρ f hf,
    ⟨liftMap_equivariant hcomplete ρ f hf, liftMap_reference hcomplete ρ f hf⟩,
    fun φ hφ => liftMap_unique hcomplete ρ f hf φ hφ.1 hφ.2⟩

/-- The conditional extension bundled as a cycle map for the exact supplied representation. -/
def cycleMap (hcomplete : LinearMap.ker orbitMap ≤ relations)
    (ρ : Representation ℚ K E) (f : E) (hf : ReferenceRelations ρ f) : complex.CycleMap E where
  action := ρ
  map := liftMap hcomplete ρ f hf
  equivariant := liftMap_equivariant hcomplete ρ f hf

/-- Conditional specialization to the actual homogeneous determinant-twisted coefficient action. -/
def polynomialCycleMap (hcomplete : LinearMap.ker orbitMap ≤ relations)
    {n : ℕ} {e : ℤ} (f : PolynomialGLAction.HomogeneousPoly n)
    (hf : ReferenceRelations (GoodChainComplex.coefficientAction n e) f) :
    GoodChainComplex.PolynomialCycleMap n e where
  map := liftMap hcomplete (GoodChainComplex.coefficientAction n e) f hf
  equivariant := liftMap_equivariant hcomplete (GoodChainComplex.coefficientAction n e) f hf

@[simp] theorem polynomialCycleMap_reference (hcomplete : LinearMap.ker orbitMap ≤ relations)
    {n : ℕ} {e : ℤ} (f : PolynomialGLAction.HomogeneousPoly n)
    (hf : ReferenceRelations (GoodChainComplex.coefficientAction n e) f) :
    (polynomialCycleMap hcomplete f hf).map referenceApartment = f :=
  liftMap_reference hcomplete (GoodChainComplex.coefficientAction n e) f hf

/-- The homogeneous polynomial extension is also unique, conditional on the same completeness premise. -/
theorem polynomialCycleMap_existsUnique (hcomplete : LinearMap.ker orbitMap ≤ relations)
    {n : ℕ} {e : ℤ} (f : PolynomialGLAction.HomogeneousPoly n)
    (hf : ReferenceRelations (GoodChainComplex.coefficientAction n e) f) :
    ∃! F : GoodChainComplex.PolynomialCycleMap n e, F.map referenceApartment = f := by
  refine ⟨polynomialCycleMap hcomplete f hf, polynomialCycleMap_reference hcomplete f hf, ?_⟩
  intro F hF
  apply GoodOrbitSpan.polynomialCycleMap_ext
  rw [hF, polynomialCycleMap_reference]

end TernaryPoly.OrbitKernelLifting
