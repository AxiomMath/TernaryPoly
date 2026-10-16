module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.Compat
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KMaps
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.KSurjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Normalized.Natural
public import TernaryPeriodPolynomials.Polynomial.PositiveInnerVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.PolynomialGate

@[expose] public section


/-!
# Proof of Proposition 3.4, passage to the boundary, at the level `K`

Formalized by Claude Sonnet 5.5.  Paper: `thm:boundary-evaluation`, first paragraph of the proof:

> Put `Δ = K/Γ'`.  Rational Hochschild--Serre and averaging give `H₃(K,E_{n,t}) ≅ H₃(Γ',E_{n,t})_Δ`.  The same finite-cover descent applies to boundary
> homology and commutes with its map to ordinary homology, so exact averaging preserves the surjection at level `K`.

Here `Γ' = Γ(6) ∩ K` (neat), `E = E_{n,t}`, `K ≤ GL₃(ℤ)` the arithmetic subgroup of the statements.
`j_surjective_Vnt`: the neat-level boundary map `H₃(∂X̄_{Γ'}; E_{n,t}) → H₃(Γ', E_{n,t})` is surjective for `n > 0` (the library's surjectivity for
the 26-covector module, transported by the retraction `ev ∘ ι = id`).
`boundary_descent_K`: the three descent statements at level `K`, all with `Δ = K/Γ'` coinvariants:
(i) `H₃(K,E) ≅ H₃(Γ',E)_Δ`, `[z] ↦ Cor z`; (ii) `H₃(∂X̄_K; E) ≅ H₃(∂X̄_{Γ'}; E)_Δ`, `[c] ↦ q c`; (iii) these isomorphisms intertwine `j_*` on
coinvariants with `j^K_*`, and both are surjective.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.PolynomialGLAction TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalHomology Representation
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.Lemma33.Normalized (boundaryToGroup_natural)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Evaluation at the distinguished covector after the unit `ι` is the identity. -/
theorem evN_iotaN_apply (n : ℕ) (t : Fin 2) (a : V n) : (evN n t).hom ((iotaN n t).hom a) = a := by
  have h := evaluation_iotaK n t 1 a
  have h1 : (iotaN n t).hom a = Pi.single distinguished a := iotaK_apply n t a
  have h3 : coefficientAction n (expT t) 1 (Pi.single distinguished a) = Pi.single distinguished a := by
    rw [map_one]; rfl
  have h4 : evaluation n (Pi.single distinguished a) = a := by
    have := h
    rw [h3, ite_eq_left K.one_mem, map_one] at this
    exact this
  change evaluation n ((iotaN n t).hom a) = a
  rw [h1]
  exact h4

/-- `ι` followed by evaluation at the distinguished covector is the identity of the neat-level coefficients. -/
theorem iotaN_evN (n : ℕ) (t : Fin 2) : iotaN n t ≫ evN n t = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  exact evN_iotaN_apply n t a

/-- A retract inherits surjectivity of the neat-level boundary map `H₃(∂X̄_{Γ(6)}; -) → H₃(Γ(6), -)`. -/
theorem j_surjective_of_retract {V W : Rep.{0} ℚ principalSix} (ι : V ⟶ W) (ev : W ⟶ V) (h : ι ≫ ev = 𝟙 V)
    (hW : Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup W 3).hom) :
    Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup V 3).hom := by
  intro y
  obtain ⟨x, hx⟩ := hW ((groupHomology.map (MonoidHom.id principalSix) ι 3).hom y)
  have h' : (SymmetricSpaceBoundaryDuality.boundaryToGroup V 3).hom
      ((homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering ev) 3).hom x) =
      (groupHomology.map (MonoidHom.id principalSix) ev 3).hom ((SymmetricSpaceBoundaryDuality.boundaryToGroup W 3).hom x) :=
    ConcreteCategory.congr_hom (boundaryToGroup_natural ev) x
  have e : groupHomology.map (MonoidHom.id principalSix) (ι ≫ ev) 3 =
      groupHomology.map (MonoidHom.id principalSix) ι 3 ≫ groupHomology.map (MonoidHom.id principalSix) ev 3 :=
    groupHomology.map_id_comp _ _ _
  rw [h, groupHomology.map_id] at e
  refine ⟨(homologyMap (localCoefficientMap boundaryProjection boundaryQuotientCovering ev) 3).hom x, ?_⟩
  rw [h', hx]
  exact ConcreteCategory.congr_hom e.symm y

/-- **Surjectivity of the neat-level boundary map for `E_{n,t}`** (`n > 0`): the library's `H₃(∂X̄_{Γ(6)}; M) → H₃(Γ(6), M)` is surjective for the
26-covector module `M`; `E_{n,t}` is a retract of `Res M`. -/
theorem j_surjective_Vnt (n : ℕ) (hn : 0 < n) (t : Fin 2) :
    Function.Surjective (SymmetricSpaceBoundaryDuality.boundaryToGroup (Rep.res principalSix.subtype (Vnt n t)) 3).hom :=
  j_surjective_of_retract (iotaN n t) (evN n t) (iotaN_evN n t)
    (OrdinaryBoundaryActualEvaluation.coefficient_boundary_surjective_of_inner_vanishing
      SymmetricSpaceAllTopBoundary.positivePolynomialInnerVanishing n hn (expT t))

/-- **Proposition 3.4, passage to the boundary at level `K`.**  With `Δ = K/Γ(6)-in-K` and `E = E_{n,t}`:
the descent isomorphisms for group homology and for boundary homology (both on `Δ`-coinvariants) send the classes of the neat level to the
corestriction and to the quotient class respectively, are compatible with the boundary map (`j^K_*` corresponds to `j_*` on coinvariants), and
the boundary map is surjective on coinvariants, hence `j^K_*` is surjective. -/
theorem boundary_descent_K (n : ℕ) (hn : 0 < n) (t : Fin 2) :
    (∀ z : groupHomology (Rep.res (NH K).subtype (MH K (Vnt n t))) 3,
        groupCoinvDelta K (Vnt n t) (Coinvariants.mk (repDeltaN K (Vnt n t)) z) = corN (NH K) (MH K (Vnt n t)) 3 z) ∧
      (∀ c : Bd (Vnt n t), boundaryCoinvDelta K principalSix_le_K (Vnt n t) (Coinvariants.mk (repDeltaBd K (Vnt n t)) c) =
        (qBdH K principalSix_le_K (Vnt n t)).hom c) ∧
      (∀ w, jQH K principalSix_le_K (Vnt n t) (boundaryCoinvDelta K principalSix_le_K (Vnt n t) w) =
        groupCoinvDelta K (Vnt n t) (jCoinvDelta K principalSix_le_K (Vnt n t) w)) ∧
      Function.Surjective (jCoinvDelta K principalSix_le_K (Vnt n t)) ∧
      Function.Surjective (jQH K principalSix_le_K (Vnt n t)) :=
  ⟨fun z => groupCoinvDelta_mk K (Vnt n t) z, fun c => boundaryCoinvDelta_mk K principalSix_le_K (Vnt n t) c,
    fun w => jQH_boundaryCoinvDelta K principalSix_le_K (Vnt n t) w,
    jCoinvDelta_surjective K principalSix_le_K (Vnt n t) (j_surjective_Vnt n hn t),
    jQH_surjective K principalSix_le_K (Vnt n t) (j_surjective_Vnt n hn t)⟩

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
