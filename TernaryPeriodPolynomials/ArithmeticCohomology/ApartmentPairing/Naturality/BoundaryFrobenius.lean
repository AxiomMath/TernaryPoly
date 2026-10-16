module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.ShapiroCor
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.FullClass

@[expose] public section


/-!
# Induction of coefficients for the boundary pairing (Lemma 3.3)

Formalized by Claude Sonnet 5.5.

For `M = M_{n,t} = Ind_K^G E_{n,t}` (the library's 26-covector system, `inducedIso`) and any chain complex `C` of `G`-representations,
`frobCochains`: `Hom_K(Res C, E) ≅ Hom_G(C, M)` as cochain complexes (Mathlib's `Res ⊣ Coind` adjunction transported along
`coinducedIso`), with the explicit formula `evaluation (frob⁻¹-partner φ)(c) = φ(c)` (`frobCochains_eval`): the identity coset is selected,
not the sum of all covectors.  For the boundary chains of the universal bordification this gives the `K`-level boundary cohomology
`cochainsK n t`, the isomorphism `frobH1`, the `K`-level pairing `fullBoundaryPairingK` with `fullBoundaryPairingK_frob`
(`⟨ω, ∂a⟩_E = evaluation ⟨frob ω, ∂a⟩_M`), and `levelK_diagram`: the `K`-level diagram `eq:apartment-boundary-diagram`
(`F_{j^K_* PD⁻¹ ω}(ℓ) = ⟨ω, ∂a⟩`), `j^K_* PD⁻¹ := Sh ∘ j^G_* PD⁻¹ ∘ frob` with the identity-coset Shapiro isomorphism `shapiroG`.
`evaluator_mathlibShapiro` is the corresponding equation for Mathlib's `indIso`, with the factor `[G:K]`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.OrdinaryBoundaryCone TernaryPoly.OrdinaryCovectors
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.EquivariantSingularSmall TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.OrdinaryApartmentPresentation
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPoly.PolynomialGLAction

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

local instance : HasForget₂ (Rep.{0} ℚ ↥K) Ab :=
  HasForget₂.trans (Rep ℚ ↥K) (ModuleCat ℚ) Ab
local instance : (forget₂ (Rep.{0} ℚ ↥K) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ ↥K) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)
local instance : (forget₂ (Rep.{0} ℚ ↥K) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ ↥K) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- Restriction of a chain complex of `G`-representations to `K`. -/
abbrev resC (C : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ) : ChainComplex (Rep.{0} ℚ ↥K) ℕ :=
  ((Rep.resFunctor K.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Frobenius reciprocity for cochains, step 1 (Mathlib's `Hom(Res C, E) ≅ Hom(C, Coind E)`). -/
def frobCochains1 (C : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ) (E : Rep.{0} ℚ ↥K) :
    (resC C).linearYonedaObj ℚ E ≅ C.linearYonedaObj ℚ (Rep.coind K.subtype E) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (Rep.resCoindHomEquiv.{0} _ _ _).toModuleIso) fun _ _ _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => Rep.hom_ext <| by
        ext; simp [← ModuleCat.ofHom_comp, Rep.resCoindHomEquiv, Rep.hom_comm_apply])

/-- Postcomposition with an isomorphism of coefficients, as an isomorphism of cochain complexes. -/
def yonedaCongr (C : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ) {Y Y' : Rep.{0} ℚ IntegralGL} (e : Y ≅ Y') :
    C.linearYonedaObj ℚ Y ≅ C.linearYonedaObj ℚ Y' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (LinearEquiv.ofLinearMap (Linear.rightComp ℚ (C.X i) e.hom) (Linear.rightComp ℚ (C.X i) e.inv)
      (by ext f; simp) (by ext f; simp)).toModuleIso) fun i j _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => by
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        let f' : C.X i ⟶ Y := f
        change C.d j i ≫ (f' ≫ e.hom) = (C.d j i ≫ f') ≫ e.hom
        exact (Category.assoc _ _ _).symm)

/-- **Frobenius reciprocity for cochains**: `Hom_K(Res C, E_{n,t}) ≅ Hom_G(C, M_{n,t})` as cochain complexes. -/
def frobCochains (n : ℕ) (t : Fin 2) (C : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ) :
    (resC C).linearYonedaObj ℚ (EK n t) ≅ C.linearYonedaObj ℚ (MG n t) :=
  frobCochains1 C (EK n t) ≪≫ yonedaCongr C (coinducedIso n (expT t)).symm

theorem evaluation_fromCoinduced (n : ℕ) (e : ℤ) (F : Coinduced n e) :
    evaluation n (fromCoinduced n e F) = F.val 1 := by
  have hk : representative distinguished ∈ K := (representative_mem_K_iff _).mpr rfl
  have h := F.property ⟨representative distinguished, hk⟩ 1
  change F.val (representative distinguished * 1) = integralAction n e (representative distinguished) (F.val 1) at h
  rw [mul_one] at h
  change integralAction n e (representative distinguished)⁻¹ (F.val (representative distinguished)) = _
  rw [h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem frobCochains_eval (n : ℕ) (t : Fin 2) (C : ChainComplex (Rep.{0} ℚ IntegralGL) ℕ) (i : ℕ)
    (φ : (resC C).X i ⟶ EK n t) (c : C.X i) :
    evaluation n (((frobCochains n t C).hom.f i φ).hom c) = φ.hom c := by
  change evaluation n ((coinducedIso n (expT t)).inv.hom ((Rep.resCoindToHom K.subtype (C.X i) (EK n t) φ).hom c)) = _
  have h1 : ∀ F, (coinducedIso n (expT t)).inv.hom F = fromCoinduced n (expT t) F := fun F => rfl
  let φ' : Rep.res K.subtype (C.X i) ⟶ EK n t := φ
  refine (congrArg (evaluation n) (h1 _)).trans ((evaluation_fromCoinduced n (expT t) _).trans ?_)
  change φ'.hom ((C.X i).ρ 1 c) = φ'.hom c
  simp

/-- The `K`-level cochains of the boundary: `Hom_K(Res C_*(∂X̃), E_{n,t})`. -/
abbrev cochainsK (n : ℕ) (t : Fin 2) : CochainComplex (ModuleCat ℚ) ℕ :=
  (resC fullBoundaryChains).linearYonedaObj ℚ (EK n t)

/-- `H¹(∂X̄_K; E_{n,t}) ≅ H¹(∂X̄_G; M_{n,t})`, the induction (Frobenius) isomorphism on boundary cohomology. -/
def frobH1 (n : ℕ) (t : Fin 2) :
    (cochainsK n t).homology 1 ≅ (fullBoundaryCochains n (expT t)).homology 1 :=
  (HomologicalComplex.homologyFunctor _ _ 1).mapIso (frobCochains n t fullBoundaryChains)

/-- The cycle `∂a` of the coordinate apartment in the `K`-restricted boundary chains. -/
def apartmentCycleK : (resC fullBoundaryChains).cycles 1 :=
  (resC fullBoundaryChains).cyclesMk (apartmentChainFull : (resC fullBoundaryChains).X 1) 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) apartmentChainFull_boundary

/-- The class of `∂a` in `H₁(Res ∂X̃)`. -/
def apartmentClassK : (resC fullBoundaryChains).homology 1 :=
  (resC fullBoundaryChains).homologyπ 1 apartmentCycleK

/-- **The bottom arrow at level `K`**: `ω ↦ ⟨ω, ∂a⟩ ∈ E_{n,t}`. -/
def fullBoundaryPairingK (n : ℕ) (t : Fin 2) : (cochainsK n t).homology 1 ⟶ ModuleCat.of ℚ (EK n t) :=
  homologyEvaluation (resC fullBoundaryChains) (EK n t) 1 ≫
    ModuleCat.ofHom
      { toFun := fun f => f.hom apartmentClassK
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

theorem fullBoundaryPairingK_cocycle (n : ℕ) (t : Fin 2) (x : (cochainsK n t).cycles 1) :
    fullBoundaryPairingK n t ((cochainsK n t).homologyπ 1 x) =
      (cocycleValue (resC fullBoundaryChains) (EK n t) 1 x).hom apartmentChainFull := by
  change (homologyEvaluation (resC fullBoundaryChains) (EK n t) 1
    ((cochainsK n t).homologyπ 1 x)).hom apartmentClassK = _
  rw [apartmentClassK, homologyEvaluation_apply]
  congr 1
  exact HomologicalComplex.i_cyclesMk (resC fullBoundaryChains) apartmentChainFull 0 _ apartmentChainFull_boundary

/-- **The induction (Frobenius) isomorphism preserves the bottom arrow**: `⟨ω, ∂a⟩_E = evaluation ⟨frob ω, ∂a⟩_M`,
the identity-coset component. -/
theorem fullBoundaryPairingK_frob (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) :
    fullBoundaryPairingK n t ω =
      evaluation n (fullBoundaryPairing n (expT t) ((frobH1 n t).hom ω)) := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((cochainsK n t).homologyπ 1)).mp inferInstance ω
  rw [fullBoundaryPairingK_cocycle]
  have h1 : (frobH1 n t).hom ((cochainsK n t).homologyπ 1 x) =
      (fullBoundaryCochains n (expT t)).homologyπ 1 (cyclesMap (frobCochains n t fullBoundaryChains).hom 1 x) :=
    congrArg (fun f => f x) (homologyπ_naturality (frobCochains n t fullBoundaryChains).hom 1)
  rw [h1, fullBoundaryPairing_cocycle]
  have h2 : cocycleValue fullBoundaryChains (MG n t) 1 (cyclesMap (frobCochains n t fullBoundaryChains).hom 1 x) =
      (frobCochains n t fullBoundaryChains).hom.f 1 (cocycleValue (resC fullBoundaryChains) (EK n t) 1 x) :=
    congrArg (fun f => f x) (HomologicalComplex.cyclesMap_i (frobCochains n t fullBoundaryChains).hom 1)
  rw [h2]
  exact (frobCochains_eval n t fullBoundaryChains 1 _ _).symm

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- The map `j^K_* ∘ PD⁻¹ : H¹(∂X̄_K; E) → H₃(K, E)` obtained by induction: the Frobenius isomorphism, the level-`G` map and the
Shapiro isomorphism `shapiroG` (identity-coset normalization). -/
def fullBoundaryClassToK (n : ℕ) (t : Fin 2) : (cochainsK n t).homology 1 ⟶ groupHomology (EK n t) 3 :=
  (frobH1 n t).hom ≫ fullBoundaryClassToG n (expT t) ≫ ModuleCat.ofHom (shapiroG n t).toLinearMap

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **Lemma 3.3 at level `K` for the induced coefficient system** (`eq:apartment-boundary-diagram` with `G` replaced by `K` and
`M` by `E_{n,t}`, the induction clause of the paper): the value `F_z(ℓ)` of the `K`-level Steinberg functional of
`z = j^K_* PD⁻¹ ω` on the identity apartment is the `K`-level boundary pairing `⟨ω, ∂a⟩`, for `ω` in the `K`-level boundary cohomology
`H¹(Hom_K(Res C_*(∂X̃), E_{n,t}))`.  Identity-coset normalization (`shapiroG`). -/
theorem levelK_diagram (n : ℕ) (t : Fin 2) (ω : (cochainsK n t).homology 1) :
    (H3_K_equiv n t (fullBoundaryClassToK n t ω)).1 identityApartment = fullBoundaryPairingK n t ω := by
  rw [fullBoundaryPairingK_frob]
  change (H3_K_equiv n t (shapiroG n t (fullBoundaryClassToG n (expT t) ((frobH1 n t).hom ω)))).1
    identityApartment = _
  rw [shapiroG_evaluation, levelG_diagram]

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **The identity-coset equation for Mathlib's Shapiro isomorphism, with the index factor**: the `K`-level evaluator of
`mathlibShapiro z` is `[G:K]` times the identity-coset component of the `G`-level evaluator (for `shapiroG` the factor is `1`,
`shapiroG_evaluation`). -/
theorem evaluator_mathlibShapiro (n : ℕ) (t : Fin 2) (z : groupHomology (MG n t) 3) :
    (H3_K_equiv n t ((mathlibShapiro n t).hom z)).1 identityApartment =
      ((Nat.card (IntegralGL ⧸ K) : ℚ)) • evaluation n (topEvaluationG (MG n t) z) := by
  rw [shapiroComparison_scaled]
  change ((Nat.card (IntegralGL ⧸ K) : ℚ) • (frobenius n t (thetaG (MG n t) z)).1) identityApartment = _
  rw [LinearMap.smul_apply]
  rfl

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
