module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.ExtObstructionAbstract
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ExtObstructionSequences

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeExtObstruction
open CategoryTheory CategoryTheory.Abelian
open RelativeExtObstructionAbstract RelativeExtObstructionSequences

/-- Standard universe-sized Ext exists for this genuine representation category. -/
instance repHasExt : HasExt.{1} (Rep.{0} ℚ K) := HasExt.standard _

/-- Both stated outside Ext vanishings kill the actual relative-cycle obstruction. -/
theorem quotientExt_one_subsingleton (E : Rep.{0} ℚ K)
    (h₁ : Subsingleton (Ext.{1} RelativeEdgesRep E 1))
    (h₀ : Subsingleton (Ext.{1} RelativeVerticesRep E 2)) :
    Subsingleton (Ext.{1} QuotientCyclesRep E 1) := by
  have : Subsingleton (Ext.{1} relativeSequence.X₂ E 1) := h₁
  have : Subsingleton (Ext.{1} relativeSequence.X₃ E 2) := h₀
  exact ext_one_subsingleton relativeSequence_shortExact E

/-- Every actual equivariant Good-cycle morphism extends, conditional on the two explicit Ext premises. -/
theorem extend_morphism (E : Rep.{0} ℚ K)
    (h₁ : Subsingleton (Ext.{1} RelativeEdgesRep E 1))
    (h₀ : Subsingleton (Ext.{1} RelativeVerticesRep E 2))
    (f : GoodCyclesRep ⟶ E) :
    ∃ F : OrdinaryCyclesRep ⟶ E, goodCycleInclusion ≫ F = f := by
  have : Subsingleton (Ext.{1} cycleSequence.X₃ E 1) := quotientExt_one_subsingleton E h₁ h₀
  exact extends_of_ext_one_subsingleton cycleSequence_shortExact E f

/-- Literal equivariant linear maps inherit the categorical extension with the same coefficients and action. -/
theorem extends_linear {E : Type} [AddCommGroup E] [Module ℚ E]
    (ρ : Representation ℚ K E)
    (h₁ : Subsingleton (Ext.{1} RelativeEdgesRep (Rep.of ρ) 1))
    (h₀ : Subsingleton (Ext.{1} RelativeVerticesRep (Rep.of ρ) 2))
    (f : GoodChainComplex.Cycles →ₗ[ℚ] E)
    (hf : ∀ g c, f (GoodChainComplex.complex.cyclesAction g c) = ρ g (f c)) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) = ρ g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f := by
  let φ : GoodCyclesRep ⟶ Rep.of ρ := Rep.ofHom ⟨f,fun g => by apply LinearMap.ext; intro c; exact hf g c⟩
  obtain ⟨F,hF⟩ := extend_morphism (Rep.of ρ) h₁ h₀ φ
  refine ⟨F.hom.toLinearMap,?_,?_⟩
  · intro g c
    exact LinearMap.congr_fun (F.hom.isIntertwining' g) c
  · have he := congrArg (fun f : GoodCyclesRep ⟶ Rep.of ρ => f.hom.toLinearMap) hF
    exact he

/-- The literal degree-n untwisted coefficient representation used in the even alternating route. -/
abbrev coefficientRep (n : ℕ) : Rep.{0} ℚ K := Rep.of (GoodChainComplex.coefficientAction n 0)

/-- The actual homogeneous polynomial-valued Good-cycle map extends under explicit Ext assumptions. -/
theorem homogeneous_extension (n : ℕ)
    (h₁ : Subsingleton (Ext.{1} RelativeEdgesRep (coefficientRep n) 1))
    (h₀ : Subsingleton (Ext.{1} RelativeVerticesRep (coefficientRep n) 2))
    (f : GoodChainComplex.PolynomialCycleMap n 0) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) =
        GoodChainComplex.coefficientAction n 0 g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f.map :=
  extends_linear (GoodChainComplex.coefficientAction n 0) h₁ h₀ f.map f.equivariant

end TernaryPoly.RelativeExtObstruction
