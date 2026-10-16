module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KMaps
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.BoundaryFrobenius
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Invariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Fixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.CoefficientNaturality.Assemble

@[expose] public section


/-!
# Lemma 3.3, induction clause: the Frobenius partner of a `K`-level boundary class, restricted to the neat cover

Formalized by Claude Sonnet 5.5.

For `ω` a class of `H¹(Hom_K(Res C_*(∂X̃), E_{n,t}))` (`cochainsK`), the Frobenius isomorphism `frobCochains` produces the `G`-equivariant
cochain `frob ω` with values in `M_{n,t}`.  Its restriction to the neat cover (`restrBd`) is the sum, over the cosets `s` of `G/K`, of the
translates `(rep s)⁻¹ · ι_*(res ω)` of the identity-coset embedding of the neat-level restriction `res ω` of the `K`-level class
(`frob_restr_chain` at cochain level, `restr_frob_class` on cohomology).  This is the cochain-level half of the proof that the transported
map `fullBoundaryClassToK` equals the map descended from the neat-level objects.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.PolynomialGLAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.CoefficientNaturality (coefHomPost)
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Restriction of `K`-equivariant boundary cochains with values in `E_{n,t}` to the neat level `Γ(6)`. -/
def resKc (n : ℕ) (t : Fin 2) :
    cochainsK n t ⟶ homCochains boundaryChains (Rep.res principalSix.subtype (Vnt n t)) where
  f m := ModuleCat.ofHom
    { toFun := fun φ => (Rep.resFunctor (Subgroup.inclusion principalSix_le_K)).map φ
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    rfl

theorem rowMove_rep_inv_iff (s r : NonzeroCovector) :
    rowMove (representative s)⁻¹ r = distinguished ↔ r = s := by
  have h1 : rowMove (representative s) distinguished = s := by
    rw [rowMove_distinguished, representative_row]
  constructor
  · intro h
    have h2 : rowMove (representative s) (rowMove (representative s)⁻¹ r) = rowMove (representative s) distinguished :=
      congrArg _ h
    rw [← rowMove_mul, inv_mul_cancel, h1] at h2
    simpa using h2
  · intro h
    have : rowMove (representative s)⁻¹ r = rowMove (representative s)⁻¹ (rowMove (representative s) distinguished) := by
      rw [h1, h]
    rw [this, ← rowMove_mul, mul_inv_cancel, rowMove_one]

/-- The neat-level restriction of a `K`-equivariant `1`-cochain. -/
def φR (n : ℕ) (t : Fin 2) {m : ℕ} (φ : (resC fullBoundaryChains).X m ⟶ EK n t) :
    boundaryChains.X m ⟶ Rep.res principalSix.subtype (Vnt n t) :=
  (Rep.resFunctor (Subgroup.inclusion principalSix_le_K)).map φ

theorem frob_partner_apply (n : ℕ) (t : Fin 2) (m : ℕ) (φ : (resC fullBoundaryChains).X m ⟶ EK n t)
    (x : ↑(fullBoundaryChains.X m)) (r : NonzeroCovector) :
    (((frobCochains n t fullBoundaryChains).hom.f m φ).hom x) r =
      integralAction n (expT t) (representative r)⁻¹ (φ.hom ((fullBoundaryChains.X m).ρ (representative r) x)) := by
  change ((coinducedIso n (expT t)).inv.hom ((Rep.resCoindToHom K.subtype (fullBoundaryChains.X m) (EK n t) φ).hom x)) r = _
  rfl

theorem frob_term_eval (n : ℕ) (t : Fin 2) {m : ℕ} (φ : (resC fullBoundaryChains).X m ⟶ EK n t)
    (x : ↑(boundaryChains.X m)) (s r : NonzeroCovector) :
    ((conjHom (bdryAct.act m) (GAct.ofRep principalSix (MG n t)) (representative s)⁻¹
          (φR n t φ ≫ iotaN n t)).hom x) r =
      if r = s then integralAction n (expT t) (representative s)⁻¹
        (φ.hom ((fullBoundaryChains.X m).ρ (representative s) x)) else 0 := by
  rw [conjHom_apply]
  change ((MG n t).ρ (representative s)⁻¹ (((iotaN n t).hom) (φ.hom ((fullBoundaryChains.X m).ρ (representative s)⁻¹⁻¹ x)))) r = _
  rw [inv_inv]
  change integralAction n (expT t) (representative s)⁻¹
    (((iotaK n t).hom (φ.hom ((fullBoundaryChains.X m).ρ (representative s) x))) (rowMove (representative s)⁻¹ r)) = _
  rw [iotaK_apply]
  by_cases hrs : r = s
  · subst hrs
    rw [ite_eq_left rfl, (rowMove_rep_inv_iff r r).mpr rfl, Pi.single_eq_same]
  · rw [ite_eq_right hrs]
    have : rowMove (representative s)⁻¹ r ≠ distinguished := fun h => hrs ((rowMove_rep_inv_iff s r).mp h)
    rw [Pi.single_eq_of_ne this, map_zero]

/-- **The `G`-partner of a `K`-equivariant cochain is the sum of the `26` translates of its identity-coset embedding**:
as an `Γ(6)`-equivariant cochain, `frob(φ) = ∑_s (rep s)⁻¹ · (ι ∘ φ)`. -/
theorem frob_partner_sum (n : ℕ) (t : Fin 2) {m : ℕ} (φ : (resC fullBoundaryChains).X m ⟶ EK n t)
    (x : ↑(boundaryChains.X m)) :
    ((frobCochains n t fullBoundaryChains).hom.f m φ).hom x =
      ∑ s : NonzeroCovector, ((conjHom (bdryAct.act m) (GAct.ofRep principalSix (MG n t)) (representative s)⁻¹
          (φR n t φ ≫ iotaN n t)).hom x) := by
  funext r
  refine (frob_partner_apply n t m φ x r).trans ?_
  rw [Finset.sum_apply]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun s _ => (frob_term_eval n t φ x s r).symm)
  simp

/-- **Cochain-level identity**: `res_{Γ(6)} ∘ frob = ∑_s (rep s)⁻¹ · (ι ∘ res_K)` as maps of cochain complexes. -/
theorem frob_restr_chain (n : ℕ) (t : Fin 2) :
    (frobCochains n t fullBoundaryChains).hom ≫ restrBd n (expT t) =
      ∑ s : NonzeroCovector, (resKc n t ≫ (coefHomPost boundaryChains (iotaN n t)) ≫
        hcAct bdryAct (GAct.ofRep principalSix (MG n t)) (representative s)⁻¹) := by
  apply HomologicalComplex.hom_ext
  intro m
  rw [HomologicalComplex.comp_f, cochain_sum_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply rep_hom_ext'
  intro x
  have h := frob_partner_sum n t φ x
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  change (((frobCochains n t fullBoundaryChains).hom.f m φ).hom x) = _
  rw [h]
  erw [rep_sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rfl

theorem modhom_sum_apply {R : Type} [Ring R] {X Y : ModuleCat.{0} R} {ι : Type} (s : Finset ι) (f : ι → (X ⟶ Y)) (x : X) :
    (ConcreteCategory.hom (∑ i ∈ s, f i)) x = ∑ i ∈ s, (ConcreteCategory.hom (f i)) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The map on neat-level boundary cohomology induced by the coefficient inclusion `ι`. -/
def iotaHc (n : ℕ) (t : Fin 2) : Hc (Vnt n t) →ₗ[ℚ] Hc (MG n t) :=
  (homologyMap (coefHomPost boundaryChains (iotaN n t)) 1).hom

/-- The neat-level restriction of `K`-level boundary cohomology. -/
def resK (n : ℕ) (t : Fin 2) : (cochainsK n t).homology 1 →ₗ[ℚ] Hc (Vnt n t) :=
  (homologyMap (resKc n t) 1).hom

/-- **The restriction of the `G`-partner of a `K`-class is the sum of the translates of its identity-coset embedding**
(class level): `res(frob ω) = ∑_s (rep s)⁻¹ · ι_*(res_K ω)`. -/
theorem restr_frob_class (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) :
    (homologyMap (restrBd n (expT t)) 1).hom ((frobH1 n t).hom ω) =
      ∑ s : NonzeroCovector, hcL (MG n t) (representative s)⁻¹ (iotaHc n t (resK n t ω)) := by
  have h : homologyMap (frobCochains n t fullBoundaryChains).hom 1 ≫ homologyMap (restrBd n (expT t)) 1 =
      ∑ s : NonzeroCovector, (homologyMap (resKc n t) 1 ≫ homologyMap (coefHomPost boundaryChains (iotaN n t)) 1 ≫
        homologyMap (hcAct bdryAct (GAct.ofRep principalSix (MG n t)) (representative s)⁻¹) 1) := by
    rw [← homologyMap_comp, frob_restr_chain, homologyMap_sum']
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [homologyMap_comp, homologyMap_comp]
  have h2 := ConcreteCategory.congr_hom h ω
  refine h2.trans ?_
  rw [modhom_sum_apply]
  rfl

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
