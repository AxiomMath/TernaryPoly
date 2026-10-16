module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Lemma33Diagram
public import Mathlib.RepresentationTheory.Coinvariants
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.BoundaryFrobenius
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.LevelG.Fixed

@[expose] public section


/-!
# Lemma 3.3: the relative local-coefficient class `a_φ` and `⟨ω, ∂a_φ⟩ = φ(⟨ω, ∂a⟩)`

Formalized by Claude Sonnet 5.5.

Paper: "With constant coefficient `φ` on the universal flat,
it gives a relative homology class `a_φ ∈ H₂(X̄_G, ∂X̄_G; 𝓜*)`" (then the equivariant quotient).

Neat level `Γ(6)`, coefficients `W` (a `Γ(6)`-module): `W* = Hom_ℚ(W, ℚ)` (`Wd`), the equivariant chains with coefficients in `W*` are
`(W* ⊗ C)_{Γ(6)}` (`FW`, `CoC`).  The sequence `0 → ∂ → X̄ → (X̄, ∂)` of actual upstairs chains stays short exact after taking
`W*`-coinvariants (`coinvSES_shortExact`: the relative chain groups are projective, so it splits in each degree).  `aPhi` is the class of the
relative cycle `φ ⊗ [flat]` (the actual compactified flat `flatRelChain`), `delta_aPhi` computes its boundary `φ ⊗ [∂ flat]` (the hexagon
`hexBoundaryChain`) with the connecting homomorphism of the coinvariant sequence, and `homologyEvalF` is the Kronecker pairing
`H¹(Hom_Γ(C, W)) × H₁((W* ⊗ C)_Γ) → ℚ` (`⟨f, φ ⊗ c⟩ = φ(f c)`).  `kronecker_aPhi`: `⟨ω, ∂a_φ⟩ = φ(flatBoundaryPairing ω)` for every neat-level
boundary class; `kronecker_aPhi_G` for level-`G` classes (through the `G/Γ(6)`-invariant neat restriction), and `kronecker_aPhi_K` for
`φ_λ(F) = λ(F(ℓ))` and a `K`-level class `ω` (induced coefficients): `⟨frob ω, ∂a_{φ_λ}⟩ = λ(⟨ω, ∂a⟩_E)`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.OrdinaryBoundaryActualEvaluation
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.EquivariantSingularSmall
open TernaryPeriodPolynomials.Argument.Statements.Lemma33Diagram (PDboundary flatBoundaryPairing flatBoundaryPairing_apply)
open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPoly.EquivariantSingularResolution TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SingularBoundaryRestriction
open TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryCone
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

local instance : HasForget₂ (Rep.{0} ℚ principalSix) Ab :=
  HasForget₂.trans (Rep ℚ principalSix) (ModuleCat ℚ) Ab
local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)
local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- The contragredient `W* = Hom_ℚ(W, ℚ)` of a representation of `Γ(6)`. -/
abbrev Wd (W : Rep.{0} ℚ principalSix) : Rep.{0} ℚ principalSix := Rep.of W.ρ.dual

/-- Coinvariant chains with coefficients in `W*`: `C ↦ (W* ⊗ C)_{Γ(6)}`. -/
abbrev FW (W : Rep.{0} ℚ principalSix) : Rep.{0} ℚ principalSix ⥤ ModuleCat.{0} ℚ :=
  (Rep.coinvariantsTensor ℚ principalSix).obj (Wd W)

/-- The equivariant quotient of a chain complex of `Γ(6)`-modules, with coefficients in `W*`. -/
abbrev CoC (W : Rep.{0} ℚ principalSix) (C : ChainComplex (Rep.{0} ℚ principalSix) ℕ) :
    ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  ((FW W).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- The class `φ ⊗ c` in `(W* ⊗ C)_{Γ(6)}`: the constant coefficient `φ` on the chain `c`. -/
abbrev insC (W : Rep.{0} ℚ principalSix) (φ : W →ₗ[ℚ] ℚ) {C : Rep.{0} ℚ principalSix} (c : C) : (FW W).obj C :=
  Rep.coinvariantsTensorMk (Wd W) C φ c

/-- The Kronecker pairing of a coefficient-`W` equivariant cochain with a coinvariant chain with coefficients in `W*`:
`⟨f, φ ⊗ c⟩ = φ(f c)`. -/
def evalBil (W : Rep.{0} ℚ principalSix) {C : Rep.{0} ℚ principalSix} (f : C ⟶ W) :
    (Wd W) →ₗ[ℚ] C →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun (φ : Module.Dual ℚ W) (c : C) => φ (f.hom c))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun φ c c' => by simp)
    (fun r φ c => by simp)

def evalChain (W : Rep.{0} ℚ principalSix) {C : Rep.{0} ℚ principalSix} (f : C ⟶ W) :
    (FW W).obj C ⟶ ModuleCat.of ℚ ℚ :=
  ModuleCat.ofHom (Representation.Coinvariants.lift _ (TensorProduct.lift (evalBil W f)) (by
      intro g
      apply TensorProduct.ext'
      intro φ c
      change evalBil W f ((Wd W).ρ g φ) (C.ρ g c) = evalBil W f φ c
      change (W.ρ.dual g φ) (f.hom (C.ρ g c)) = φ (f.hom c)
      rw [Representation.dual_apply, Rep.hom_comm_apply f g c]
      change φ (W.ρ g⁻¹ (W.ρ g (f.hom c))) = _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl))

theorem evalChain_mk (W : Rep.{0} ℚ principalSix) {C : Rep.{0} ℚ principalSix} (f : C ⟶ W) (φ : W →ₗ[ℚ] ℚ) (c : C) :
    (evalChain W f).hom (insC W φ c) = φ (f.hom c) := rfl

theorem map_insC (W : Rep.{0} ℚ principalSix) {C C' : Rep.{0} ℚ principalSix} (g : C ⟶ C') (φ : W →ₗ[ℚ] ℚ) (c : C) :
    ((FW W).map g).hom (insC W φ c) = insC W φ (g.hom c) := rfl

theorem evalChain_comp (W : Rep.{0} ℚ principalSix) {C C' : Rep.{0} ℚ principalSix} (g : C ⟶ C') (f : C' ⟶ W) :
    (FW W).map g ≫ evalChain W f = evalChain W (g ≫ f) := by
  apply Rep.coinvariantsTensor_hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

open Limits in
/-- Coinvariants with coefficients in `W*` preserve the short exact sequence of the pair `(X̄, ∂X̄)`: the relative chain groups are
projective, so the sequence splits in each degree. -/
theorem coinvSES_shortExact (W : Rep.{0} ℚ principalSix) :
    (upstairsRelativeSequence.map ((FW W).mapHomologicalComplex (ComplexShape.down ℕ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hT := upstairsRelativeSequence_shortExact.map_of_exact (eval (Rep.{0} ℚ principalSix) (ComplexShape.down ℕ) n)
  have : Projective (upstairsRelativeSequence.map (eval (Rep.{0} ℚ principalSix) (ComplexShape.down ℕ) n)).X₃ :=
    upstairsRelativeDegree_projective n
  have := hT.epi_g
  let s := Projective.factorThru (𝟙 _) (upstairsRelativeSequence.map (eval (Rep.{0} ℚ principalSix) (ComplexShape.down ℕ) n)).g
  have hs : s ≫ (upstairsRelativeSequence.map (eval (Rep.{0} ℚ principalSix) (ComplexShape.down ℕ) n)).g = 𝟙 _ :=
    Projective.factorThru_comp _ _
  let spl := ShortComplex.Splitting.ofExactOfSection _ hT.exact s hs hT.mono_f
  exact (spl.map (FW W)).shortExact

theorem evalChain_zero (W : Rep.{0} ℚ principalSix) {C : Rep.{0} ℚ principalSix} :
    evalChain W (0 : C ⟶ W) = 0 := by
  apply Rep.coinvariantsTensor_hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((0 : C ⟶ W).hom c) = 0
  change φ 0 = 0
  exact map_zero φ

theorem evalChain_add (W : Rep.{0} ℚ principalSix) {C : Rep.{0} ℚ principalSix} (f g : C ⟶ W) :
    evalChain W (f + g) = evalChain W f + evalChain W g := by
  apply Rep.coinvariantsTensor_hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((f + g).hom c) = φ (f.hom c) + φ (g.hom c)
  rw [← map_add]
  rfl

theorem evalChain_smul (W : Rep.{0} ℚ principalSix) {C : Rep.{0} ℚ principalSix} (r : ℚ) (f : C ⟶ W) :
    evalChain W (r • f) = r • evalChain W f := by
  apply Rep.coinvariantsTensor_hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  change φ ((r • f).hom c) = r • φ (f.hom c)
  rw [← map_smul]
  rfl

section Pairing

variable (W : Rep.{0} ℚ principalSix) (C : ChainComplex (Rep.{0} ℚ principalSix) ℕ) (n : ℕ)

/-- A cocycle of `Hom_Γ(C, W)` descends to a functional on the homology of the `W*`-coefficient coinvariant chains. -/
def cocycleEvalF (x : (homCochains C W).cycles n) : (CoC W C).homology n ⟶ ModuleCat.of ℚ ℚ :=
  ((CoC W C).sc n).descHomology ((CoC W C).iCycles n ≫ evalChain W (cocycleValue C W n x)) (by
    change ((CoC W C).sc n).toCycles ≫ ((CoC W C).sc n).iCycles ≫ _ = 0
    erw [← Category.assoc, ShortComplex.toCycles_i]
    change (CoC W C).d ((ComplexShape.down ℕ).prev n) n ≫ _ = 0
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    change (FW W).map (C.d (n + 1) n) ≫ evalChain W (cocycleValue C W n x) = 0
    rw [evalChain_comp, cocycleValue_boundary C W n x, evalChain_zero])

theorem cocycleEvalF_projection (x : (homCochains C W).cycles n) :
    (CoC W C).homologyπ n ≫ cocycleEvalF W C n x = (CoC W C).iCycles n ≫ evalChain W (cocycleValue C W n x) :=
  ((CoC W C).sc n).π_descHomology _ _

/-- The functional of a cocycle is linear in the cocycle. -/
def cocycleEvalFMap : (homCochains C W).cycles n ⟶ ModuleCat.of ℚ ((CoC W C).homology n ⟶ ModuleCat.of ℚ ℚ) :=
  ModuleCat.ofHom {
    toFun := cocycleEvalF W C n
    map_add' := fun x y => by
      apply (cancel_epi ((CoC W C).homologyπ n)).mp
      erw [Preadditive.comp_add, cocycleEvalF_projection W C n (x + y), cocycleEvalF_projection W C n x,
        cocycleEvalF_projection W C n y]
      dsimp [cocycleValue]
      erw [map_add, evalChain_add, Preadditive.comp_add]
    map_smul' := fun r x => by
      apply (cancel_epi ((CoC W C).homologyπ n)).mp
      erw [Linear.comp_smul, cocycleEvalF_projection W C n (r • x), cocycleEvalF_projection W C n x]
      dsimp [cocycleValue]
      erw [map_smul, evalChain_smul, Linear.comp_smul] }

theorem cocycleEvalFMap_boundary : ((homCochains C W).sc n).toCycles ≫ cocycleEvalFMap W C n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cocycleEvalF W C n (((homCochains C W).sc n).toCycles x) = 0
  apply (cancel_epi ((CoC W C).homologyπ n)).mp
  erw [cocycleEvalF_projection W C n (((homCochains C W).sc n).toCycles x), Limits.comp_zero]
  have h := congrArg (fun f => f x) (((homCochains C W).sc n).toCycles_i)
  change cocycleValue C W n (((homCochains C W).sc n).toCycles x) =
    C.d n ((ComplexShape.up ℕ).prev n) ≫ x at h
  have h2 := (CoC W C).iCycles_d n ((ComplexShape.up ℕ).prev n)
  erw [h, ← evalChain_comp, ← Category.assoc, h2, Limits.zero_comp]

/-- **The Kronecker pairing** of `H¹(Hom_Γ(C, W))` with the homology of the `W*`-coefficient coinvariant chains. -/
def homologyEvalF : (homCochains C W).homology n ⟶ ModuleCat.of ℚ ((CoC W C).homology n ⟶ ModuleCat.of ℚ ℚ) :=
  ((homCochains C W).sc n).descHomology (cocycleEvalFMap W C n) (cocycleEvalFMap_boundary W C n)

theorem homologyEvalF_apply (x : (homCochains C W).cycles n) (z : (CoC W C).cycles n) :
    (homologyEvalF W C n ((homCochains C W).homologyπ n x)).hom ((CoC W C).homologyπ n z) =
      (evalChain W (cocycleValue C W n x)).hom ((CoC W C).iCycles n z) := by
  have h := congrArg (fun f => f x) (((homCochains C W).sc n).π_descHomology (cocycleEvalFMap W C n) (cocycleEvalFMap_boundary W C n))
  change homologyEvalF W C n ((homCochains C W).homologyπ n x) = cocycleEvalF W C n x at h
  erw [h]
  exact congrArg (fun f => f.hom z) (cocycleEvalF_projection W C n x)

end Pairing

open TernaryPeriodPolynomials.Argument.Lemma33 in
/-- The cycle `φ ⊗ [flat]` of the equivariant quotient of the relative chains with coefficients in `W*`: the constant dual coefficient `φ`
on the universal flat. -/
def relCycleF (W : Rep.{0} ℚ principalSix) (φ : W →ₗ[ℚ] ℚ) : (CoC W upstairsRelativeChains).cycles 2 :=
  (CoC W upstairsRelativeChains).cyclesMk (insC W φ flatRelChain) 1
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)) (by
      change (((FW W).map (upstairsRelativeChains.d 2 1)).hom (insC W φ flatRelChain)) = 0
      rw [map_insC, flatRelChain_d]
      exact map_zero (Rep.coinvariantsTensorMk (Wd W) _ φ))

/-- **The relative local-coefficient class** `a_φ ∈ H₂(X̄_{Γ(6)}, ∂X̄_{Γ(6)}; 𝓜*)`: the constant dual coefficient `φ` on the universal flat,
then the equivariant quotient (`Γ(6)`-coinvariants of `W* ⊗ (relative chains)`). -/
def aPhi (W : Rep.{0} ℚ principalSix) (φ : W →ₗ[ℚ] ℚ) : (CoC W upstairsRelativeChains).homology 2 :=
  (CoC W upstairsRelativeChains).homologyπ 2 (relCycleF W φ)

open TernaryPeriodPolynomials.Argument.Lemma33 in
theorem hex_d : (boundaryChains.d 1 0).hom hexBoundaryChain = 0 := by
  have hinj : Function.Injective (upstairsBoundaryChainMap.f 0).hom := by
    have : Mono (upstairsBoundaryChainMap.f 0) := upstairsBoundaryDegree_mono 0
    exact (Rep.mono_iff_injective _).mp this
  apply hinj
  have h1 := congrArg (fun m => m.hom hexBoundaryChain) (upstairsBoundaryChainMap.comm 1 0)
  change ((equivariantChains principalSix (TopCat.of Glued)).d 1 0).hom ((upstairsBoundaryChainMap.f 1).hom hexBoundaryChain) =
    (upstairsBoundaryChainMap.f 0).hom ((boundaryChains.d 1 0).hom hexBoundaryChain) at h1
  rw [← h1, ← d_flatRep]
  have h2 := congrArg (fun m => m.hom flatRep) (HomologicalComplex.d_comp_d (equivariantChains principalSix (TopCat.of Glued)) 2 1 0)
  exact h2.trans (by rfl) |>.trans (map_zero _).symm

open TernaryPeriodPolynomials.Argument.Lemma33 in
/-- The cycle `φ ⊗ [∂ flat]` of the `W*`-coefficient boundary chains. -/
def bdCycleF (W : Rep.{0} ℚ principalSix) (φ : W →ₗ[ℚ] ℚ) : (CoC W boundaryChains).cycles 1 :=
  (CoC W boundaryChains).cyclesMk (insC W φ hexBoundaryChain) 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) (by
      change (((FW W).map (boundaryChains.d 1 0)).hom (insC W φ hexBoundaryChain)) = 0
      rw [map_insC, hex_d]
      exact map_zero (Rep.coinvariantsTensorMk (Wd W) _ φ))

open TernaryPeriodPolynomials.Argument.Lemma33 in
/-- **The boundary of `a_φ` is the constant coefficient `φ` on the coordinate apartment**: `∂a_φ = [φ ⊗ ∂(flat)]`. -/
theorem delta_aPhi (W : Rep.{0} ℚ principalSix) (φ : W →ₗ[ℚ] ℚ) :
    (coinvSES_shortExact W).δ 2 1 rfl (aPhi W φ) = (CoC W boundaryChains).homologyπ 1 (bdCycleF W φ) := by
  have h := (coinvSES_shortExact W).δ_apply 2 1 rfl (insC W φ flatRelChain) (by
      change (((FW W).map (upstairsRelativeChains.d 2 1)).hom (insC W φ flatRelChain)) = 0
      rw [map_insC, flatRelChain_d]
      exact map_zero (Rep.coinvariantsTensorMk (Wd W) _ φ))
    (insC W φ flatRep) rfl (insC W φ hexBoundaryChain)
    (by
      change insC W φ ((upstairsBoundaryChainMap.f 1).hom hexBoundaryChain) =
        insC W φ (((equivariantChains principalSix (TopCat.of Glued)).d 2 1).hom flatRep)
      rw [d_flatRep])
    0 ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
  exact h

open TernaryPeriodPolynomials.Argument.Lemma33 in
theorem delta_flatClass_mk :
    upstairsRelativeSequence_shortExact.δ 2 1 rfl flatClass =
      boundaryChains.homologyπ 1 (boundaryChains.cyclesMk hexBoundaryChain 0
        ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) hex_d) :=
  upstairsRelativeSequence_shortExact.δ_apply 2 1 rfl flatRelChain flatRelChain_d
    flatRep rfl hexBoundaryChain d_flatRep.symm 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))

open TernaryPeriodPolynomials.Argument.Lemma33 in
/-- **Lemma 3.3, bottom arrow with the dual local coefficient** (`⟨ω, ∂a_φ⟩ = φ(⟨ω, ∂a⟩)`): the Kronecker pairing of a boundary class
`ω ∈ H¹(∂X̄; 𝓜)` with the boundary of the relative local-coefficient class `a_φ ∈ H₂(X̄, ∂X̄; 𝓜*)` (constant dual coefficient `φ` on the flat,
equivariant quotient) is `φ` of the `W`-valued flat pairing. -/
theorem kronecker_aPhi (W : Rep.{0} ℚ principalSix) (φ : W →ₗ[ℚ] ℚ)
    (ω : (homCochains boundaryChains W).homology 1) :
    (homologyEvalF W boundaryChains 1 ω).hom ((coinvSES_shortExact W).δ 2 1 rfl (aPhi W φ)) =
      φ (flatBoundaryPairing W ω) := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective ((homCochains boundaryChains W).homologyπ 1)).mp inferInstance ω
  rw [delta_aPhi, homologyEvalF_apply]
  rw [flatBoundaryPairing_apply, delta_flatClass_mk, homologyEvaluation_apply]
  have e1 := (CoC W boundaryChains).i_cyclesMk (insC W φ hexBoundaryChain) 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) (by
      change (((FW W).map (boundaryChains.d 1 0)).hom (insC W φ hexBoundaryChain)) = 0
      rw [map_insC, hex_d]
      exact map_zero (Rep.coinvariantsTensorMk (Wd W) _ φ))
  have e2 := boundaryChains.i_cyclesMk hexBoundaryChain 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) hex_d
  change ((CoC W boundaryChains).iCycles 1).hom (bdCycleF W φ) = insC W φ hexBoundaryChain at e1
  change (boundaryChains.iCycles 1).hom (boundaryChains.cyclesMk hexBoundaryChain 0
        ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)) hex_d) = hexBoundaryChain at e2
  rw [e1, e2]
  rfl

open TernaryPeriodPolynomials.Argument.Lemma33.LevelG in
/-- The flat pairing of the neat restriction of a level-`G` class is the level-`G` bottom arrow. -/
theorem flatBoundaryPairing_restrBd (n : ℕ) (e : ℤ) (ω : (fullBoundaryCochains n e).homology 1) :
    flatBoundaryPairing (restrictedCoefficients n e) (homologyMap (restrBd n e) 1 ω) = fullBoundaryPairing n e ω := by
  have h := flatBoundaryPairing_PDG n e ((PDG n e).symm ω)
  rw [LinearEquiv.apply_symm_apply, PDG_symm_apply, PDboundary_resToBoundary] at h
  exact h

open TernaryPeriodPolynomials.Argument.Lemma33.LevelG in
/-- **`⟨ω, ∂a_φ⟩ = φ(⟨ω, ∂a⟩)` at level `G`**: for a level-`G` boundary class `ω ∈ H¹(∂X̄_G; M)` (its neat restriction is `G`-invariant, so
it pairs with the equivariant quotient class `a_φ`), the pairing with the boundary of the relative local-coefficient class is `φ` of the
level-`G` bottom arrow. -/
theorem kronecker_aPhi_G (n : ℕ) (e : ℤ) (φ : restrictedCoefficients n e →ₗ[ℚ] ℚ)
    (ω : (fullBoundaryCochains n e).homology 1) :
    (homologyEvalF (restrictedCoefficients n e) boundaryChains 1 (homologyMap (restrBd n e) 1 ω)).hom
        ((coinvSES_shortExact (restrictedCoefficients n e)).δ 2 1 rfl (aPhi (restrictedCoefficients n e) φ)) =
      φ (fullBoundaryPairing n e ω) := by
  rw [kronecker_aPhi, flatBoundaryPairing_restrBd]

open TernaryPeriodPolynomials.Argument.Lemma33.LevelG TernaryPeriodPolynomials.Argument.FiberModel in
/-- **The paper's `eq:apartment-boundary-evaluation` pairing, with induced coefficients**: for `λ ∈ V_n^*` and `φ_λ(F) = λ(F(ℓ))`, the
pairing of the `G`-level class `frob ω` of a `K`-level class `ω` with `∂a_{φ_λ}` is `λ` of the `K`-level pairing `⟨ω, ∂a⟩`. -/
theorem kronecker_aPhi_K (n : ℕ) (t : Fin 2)
    (lam : V n →ₗ[ℚ] ℚ) (ω : (cochainsK n t).homology 1) :
    (homologyEvalF (restrictedCoefficients n (expT t)) boundaryChains 1
        (homologyMap (restrBd n (expT t)) 1 ((frobH1 n t).hom ω))).hom
        ((coinvSES_shortExact (restrictedCoefficients n (expT t))).δ 2 1 rfl
          (aPhi (restrictedCoefficients n (expT t)) (lam ∘ₗ evaluation n))) =
      lam (fullBoundaryPairingK n t ω) := by
  rw [kronecker_aPhi_G, fullBoundaryPairingK_frob]
  rfl

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
