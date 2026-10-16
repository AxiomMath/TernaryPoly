module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.FullClass

@[expose] public section


/-!
# Lemma 3.3 at level `G`: descent (coinvariants in homology, invariants in cohomology) preserves the pairing

Formalized by Claude Sonnet 5.5.

Paper: "Taking finite-group coinvariants in homology and invariants in cohomology is exact and
preserves the pairing, giving descent to the stated level."

For an arbitrary neat-level boundary cohomology class `x` (not necessarily invariant), the corestriction `Cor(j_* PD_∂⁻¹ x) ∈
H₃(G, M)` equals the corestriction of the image of the transferred class `transfer x ∈ H¹(∂X̄_G; M)` (`corN_boundaryImage`):
the `G/Γ(6)`-average of the neat-level Steinberg functional of `j_* PD_∂⁻¹ x` is the functional of the transfer
(`avg_boundaryImage_eq`, checked on frames; the sums over left cosets `G/Γ(6)` of `GroupHomology.avg` and over right cosets of
`transfer` are identified by inversion, `sum_rightCosets_eq`).  Hence, in terms of neat-level boundary homology,
`Cor(j_* c) = Cor(j_* avG(c))` (`corN_avG`), the pairing of `Cor(j_*c)` is `⟨transfer(PD_∂ c), ∂a⟩` (`levelG_diagram_all`), and
`avG` is the identity on `H₃(∂X̄_G; 𝓜)` (`avG_fixed`).  This is the averaged form of the `G`-equivariance of `j_*` and `PD_∂`; the actual-action statements are `BoundaryAction.lean`/`BoundaryCap.lean`,
and `Averages.lean` proves `avG` is the average of the geometric action.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.OrdinaryApartmentPresentation
  TernaryPoly.OrdinaryBoundaryCone TernaryPoly.RationalCohomologyDescent
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.AppendixBResidue

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.LevelG

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- A sum over right cosets of a coset-invariant function equals the sum over left cosets of its inversion. -/
theorem sum_rightCosets_eq {E : Type*} [AddCommMonoid E] (T : IntegralGL → E)
    (hT : ∀ a b, b * a⁻¹ ∈ principalSix → T a = T b) :
    ∑ q : RightCosets principalSix, T q.out = ∑ q : IntegralGL ⧸ principalSix, T q.out⁻¹ := by
  refine Fintype.sum_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel principalSix) _ _ ?_
  intro q
  apply hT
  have h1 : QuotientGroup.quotientRightRelEquivQuotientLeftRel principalSix q =
      (QuotientGroup.mk q.out⁻¹ : IntegralGL ⧸ principalSix) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have h2 : (QuotientGroup.mk (QuotientGroup.quotientRightRelEquivQuotientLeftRel principalSix q).out :
      IntegralGL ⧸ principalSix) = QuotientGroup.mk q.out⁻¹ := by
    rw [QuotientGroup.out_eq', h1]
  exact QuotientGroup.eq.mp h2

variable (n : ℕ) (e : ℤ)

/-- The neat-level boundary image `j_* PD_∂⁻¹ x` of an arbitrary neat-level boundary cohomology class. -/
def boundaryImage (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1) :
    groupHomology (restrictedCoefficients n e) 3 :=
  SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3
    ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
      SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom
      ((boundaryCohomologyIso (restrictedCoefficients n e)).hom x))

/-- The summand of the averaged pairing, a function of the group element. -/
def pairTerm (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) (a h : IntegralGL) :
    actualCoefficients n e :=
  (actualCoefficients n e).ρ h⁻¹
    ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
      ((fullBoundaryChains.X 1).ρ (h * a) apartmentChainFull))

theorem pairTerm_invariant (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1)
    (a : IntegralGL) :
    ∀ h h', h' * h⁻¹ ∈ principalSix → pairTerm n e x₀ a h = pairTerm n e x₀ a h' := by
  intro h h' hh
  set m : principalSix := ⟨h' * h⁻¹, hh⟩ with hm
  have hh' : h' = m.1 * h := by simp [hm]
  have key := Rep.hom_comm_apply (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀) m
    ((fullBoundaryChains.X 1).ρ (h * a) apartmentChainFull)
  have e1 : (fullBoundaryChains.X 1).ρ ((m.1 * h) * a) apartmentChainFull =
      (fullBoundaryChains.X 1).ρ m.1 ((fullBoundaryChains.X 1).ρ (h * a) apartmentChainFull) := by
    rw [mul_assoc, map_mul]
    rfl
  have key' : (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
      ((fullBoundaryChains.X 1).ρ m.1 ((fullBoundaryChains.X 1).ρ (h * a) apartmentChainFull)) =
      (actualCoefficients n e).ρ m.1
        ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
          ((fullBoundaryChains.X 1).ρ (h * a) apartmentChainFull)) := key
  unfold pairTerm
  rw [hh', e1, key', ← Module.End.mul_apply, ← map_mul]
  simp

/-- Frame values of the neat-level functional of `j_* PD⁻¹ x`. -/
theorem boundaryImage_frame (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) (b : IntegralGL) :
    psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
        (boundaryImage n e ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀))
        (frameCycle b) =
      (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
        ((fullBoundaryChains.X 1).ρ b apartmentChainFull) := by
  rw [psiGen_apply]
  have h := cappedBoundary_ordinary_apply (restrictedCoefficients n e)
    ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀)
  change ((groupOrdinaryIso (restrictedCoefficients n e)).hom
    (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3
      ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom
        ((boundaryCohomologyIso (restrictedCoefficients n e)).hom
          ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀))))).hom (frameCycle b) = _
  rw [h]
  exact boundaryOrdinaryEvaluation_frame (restrictedCoefficients n e) x₀ b

/-- The `G/Γ(6)`-average of the neat-level functional, on a frame. -/
theorem avg_frame (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) (a : IntegralGL) :
    avg stG (actualCoefficients n e).ρ principalSix
        (psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
          (boundaryImage n e ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀)))
        (frameCycle a) =
      (Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹ •
        ∑ q : IntegralGL ⧸ principalSix, pairTerm n e x₀ a q.out⁻¹ := by
  change (Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹ • avgSum stG (actualCoefficients n e).ρ principalSix _ _ = _
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold GroupHomology.term pairTerm
  change (actualCoefficients n e).ρ q.out (psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e) _
    (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral q.out⁻¹) (frameCycle a))) = _
  rw [OrdinaryFullAction.frameCycle_equivariant, boundaryImage_frame, inv_inv]

/-- Frame values of the neat-level functional of the transferred (averaged) class. -/
theorem descent_frame_raw (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) (a : IntegralGL) :
    psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
        (normalizedBoundaryClassToGroup n e
          ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀)) (frameCycle a) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ •
        ∑ r : RightCosets principalSix, (actualCoefficients n e).ρ r.out⁻¹
          ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
            ((fullBoundaryChains.X 1).ρ r.out ((fullBoundaryChains.X 1).ρ a apartmentChainFull))) := by
  rw [psiGen_apply, normalizedBoundaryClassToGroup_ordinary]
  have h := congrArg (fun f => f x₀)
    (homologyπ_naturality (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  change homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀) =
    (homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 (averagedBoundaryCocycle n e x₀) at h
  rw [h, boundaryOrdinaryEvaluation_frame, averagedBoundaryCocycle_value]
  change (transferHom principalSix (fullBoundaryChains.X 1) (actualCoefficients n e)
    (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀)).hom
    ((fullBoundaryChains.X 1).ρ a apartmentChainFull) = _
  erw [transferHom_apply]
  congr! 1

theorem descent_frame (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) (a : IntegralGL) :
    psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
        (normalizedBoundaryClassToGroup n e
          ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀)) (frameCycle a) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ •
        ∑ r : RightCosets principalSix, pairTerm n e x₀ a r.out := by
  rw [descent_frame_raw]
  have hp : ∀ r : IntegralGL, (actualCoefficients n e).ρ r⁻¹
      ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
        ((fullBoundaryChains.X 1).ρ r ((fullBoundaryChains.X 1).ρ a apartmentChainFull))) =
      pairTerm n e x₀ a r := fun r => by
    unfold pairTerm
    rw [map_mul]
    rfl
  simp only [hp]

theorem natCard_rightCosets :
    Nat.card (RightCosets principalSix) = Fintype.card (IntegralGL ⧸ principalSix) := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel principalSix), Nat.card_eq_fintype_card]

/-- **Descent preserves the functional**: the `G/Γ(6)`-average of the neat-level functional of `j_* PD⁻¹ x` is the functional
of the transferred class (`transfer` = rational averaging of cochains). -/
theorem avg_boundaryImage_eq (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1) :
    avg stG (actualCoefficients n e).ρ principalSix
        (psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e) (boundaryImage n e x)) =
      psiGen principalSix (MulEquiv.refl principalSix) (actualCoefficients n e)
        (normalizedBoundaryClassToGroup n e x) := by
  obtain ⟨x₀, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1)).mp inferInstance x
  apply cycle_functional_ext
  intro a
  rw [avg_frame, descent_frame, natCard_rightCosets,
    sum_rightCosets_eq (pairTerm n e x₀ a) (pairTerm_invariant n e x₀ a)]

/-- **Lemma 3.3 descent for arbitrary neat-level boundary classes** (O-G1 and O-G2 in averaged form): the corestriction of
`j_* PD_∂⁻¹ x` to `H₃(G, M)` equals the corestriction of the image of the transferred (invariant) class.  Equivalently,
`j_* ∘ PD_∂⁻¹` intertwines the `G/Γ(6)`-averages. -/
theorem corN_boundaryImage (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1) :
    corN principalSix (actualCoefficients n e) 3 (boundaryImage n e x) =
      corN principalSix (actualCoefficients n e) 3 (normalizedBoundaryClassToGroup n e x) := by
  apply (thetaG (actualCoefficients n e)).injective
  apply Subtype.ext
  rw [thetaG_corN, psiGen_avgN (neatDualityEquivariantGen_of_capEps (actualCoefficients n e)
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (actualCoefficients n e))),
    avg_boundaryImage_eq]
  exact (levelG_functional n e (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 x)).symm

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing) in
/-- The averaging (descent) projector of boundary homology onto `H₃(∂X̄_G; 𝓜)`: Poincaré dual, transfer, Poincaré dual back. -/
def avG (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    H3boundaryG n e :=
  ⟨resToBoundary n e (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1
    (PDboundary (restrictedCoefficients n e) c)), ⟨_, rfl⟩⟩

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing) in
theorem boundaryImage_PD (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    boundaryImage n e (PDboundary (restrictedCoefficients n e) c) =
      SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c := by
  unfold boundaryImage PDboundary
  change SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3
    ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
      SymmetricSpaceBoundaryOrientation.boundaryOrientation).hom
      ((boundaryCohomologyIso (restrictedCoefficients n e)).hom
        ((boundaryCohomologyIso (restrictedCoefficients n e)).inv
          ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
            SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv c)))) = _
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing) in
/-- **The averaged boundary class has the same image in `H₃(G, M)`**: `Cor(j_* c) = Cor(j_* avG(c))` for every neat-level
boundary class `c`.  (Geometric `G`-equivariance of `j_*` and `PD_∂`, in averaged form.) -/
theorem corN_avG (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c) =
      corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 (avG n e c).1) := by
  have h := corN_boundaryImage n e (PDboundary (restrictedCoefficients n e) c)
  rw [boundaryImage_PD] at h
  exact h

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing) in
/-- **Lemma 3.3 at level `G` for an arbitrary neat-level boundary class** (descent preserves the pairing):
`F_{Cor j_* c}(ℓ) = ⟨transfer(PD_∂ c), ∂a⟩`. -/
theorem levelG_diagram_all (c : (SingularLocalHomology.boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    topEvaluationG (actualCoefficients n e)
        (corG n e (SymmetricSpaceBoundaryDuality.boundaryToGroup (restrictedCoefficients n e) 3 c)) =
      fullBoundaryPairing n e
        (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1
          (PDboundary (restrictedCoefficients n e) c)) := by
  have h := corN_boundaryImage n e (PDboundary (restrictedCoefficients n e) c)
  rw [boundaryImage_PD] at h
  change topEvaluationG (actualCoefficients n e)
    (corN principalSix (actualCoefficients n e) 3 _) = _
  rw [h]
  exact levelG_diagram n e _

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing) in
/-- Transfer of the neat-level Poincaré dual of a level-`G` boundary class is the class itself. -/
theorem transfer_PD (c : H3boundaryG n e) :
    homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1
        (PDboundary (restrictedCoefficients n e) c.1) = PDG n e c := by
  obtain ⟨ω, hω⟩ := c.2
  have hc : c = (PDG n e).symm ω := Subtype.ext hω.symm
  subst hc
  rw [LinearEquiv.apply_symm_apply, PDG_symm_apply]
  have h : (homologyMap (boundaryTransfer n e) 1).hom ((homologyMap (boundaryRestriction n e) 1).hom ω) = ω := by
    have := congrArg (fun (f : fullBoundaryCochains n e ⟶ fullBoundaryCochains n e) => (homologyMap f 1).hom ω)
      (boundaryRestriction_transfer n e)
    simpa [homologyMap_comp] using this
  refine Eq.trans ?_ h
  change (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1).hom
    ((boundaryCohomologyIso (restrictedCoefficients n e)).inv
      ((SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv (resToBoundary n e ω))) = _
  have e1 : (SymmetricSpaceBoundaryManifold.boundaryH1CapIso (restrictedCoefficients n e)
        SymmetricSpaceBoundaryOrientation.boundaryOrientation).inv (resToBoundary n e ω) =
      (homologyMap (boundaryRestriction n e) 1).hom ω :=
    Iso.hom_inv_id_apply _ _
  rw [e1]
  have e2 : homologyMap (boundaryTransfer n e) 1 = homologyMap (restrictedLocalIso n e).inv 1 ≫
      homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 := by
    rw [← homologyMap_comp]
    rfl
  rw [e2]
  rfl

open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing) in
/-- `avG` is the identity on `H₃(∂X̄_G; 𝓜)`: the descent projector is idempotent with image the level-`G` subspace. -/
theorem avG_fixed (c : H3boundaryG n e) : avG n e c.1 = c := by
  apply Subtype.ext
  change resToBoundary n e _ = _
  rw [transfer_PD]
  exact PDG_symm_apply n e (PDG n e c) ▸ congrArg Subtype.val ((PDG n e).symm_apply_apply c)

/-- **Average formula for the pairing at level `G`**: `F_{Cor j_* PD⁻¹ x}(ℓ) = [G:Γ(6)]⁻¹ ∑_q ρ(q⁻¹)⟨x, q·∂a⟩`, the
sum over the cosets of `Γ(6)` (the functional `φ` then selects, for `M = Ind_K^G E`, the component of the identity
coset; see `Shapiro.lean`). -/
theorem levelG_diagram_formula (x₀ : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    topEvaluationG (actualCoefficients n e)
        (corG n e (boundaryImage n e ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀))) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ •
        ∑ q : RightCosets principalSix, (actualCoefficients n e).ρ q.out⁻¹
          ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x₀).hom
            ((fullBoundaryChains.X 1).ρ q.out apartmentChainFull)) := by
  have h := corN_boundaryImage n e ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀)
  change topEvaluationG (actualCoefficients n e) (corN principalSix (actualCoefficients n e) 3 _) = _
  rw [h]
  have h2 := topEvaluationG_fullClass n e
    (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1
      ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x₀))
  exact h2.trans (normalizedBoundaryClassToGroup_evaluation n e x₀)

end TernaryPeriodPolynomials.Argument.Lemma33.LevelG
