module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLLiteral
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenPairing

@[expose] public section


/-!
# The good plane's own dual system for even `n`

Formalized by Claude Sonnet 5.5.

For even `n` the bad line has the coefficients `Sym^{n+1}` (`ρ₂`, `binaryArithmeticRepresentation n`) and the good plane has the coefficients `Sym^{n+1} ⊗ det⁻¹` (`ρ₁`, `levelRep (n+1) (-1)`).
The comparison `E = planeComparison n : ρ₁ → ρ₂` is intertwining only after the cusp-exchanging involution `α` of `Γ₁'(3)`
(`α T = L⁻¹`, `α L = T⁻¹`): `E (ρ₁ (α γ) v) = ρ₂ γ (E v)`.  The pairing of a line class with a plane class therefore is a Poincare-Lefschetz pairing of `ρ₂` with the plane system
`ρ₁α := ρ₁ ∘ α` (the plane system seen through the identification of the plane cusps with the line cusps), via the invariant `ε`-odd pairing `B_P(v, w) = ⟨v, E w⟩`.
All statements are generic in `(ρ₁, ρ₂, E)` and specialized at the end.

* `alphaHom`, `alphaPull`: `α` as an automorphism of `Γ₁'(3)` and the induced map `α^* : H¹(Γ₁'(3), ρ₁) → H¹(Γ₁'(3), ρ₁ α)`, preserving parabolic classes (`alphaCocycles_parabolic`);
* `planeTwisted`: `(ρ₂, ρ₁α, B_P)` is a `TwistedPairing` (needs `E` bijective and `(ρ₂, ρ₂, B)` twisted); `GammaThree.setup (planeTwisted ..)` is its Poincare-Lefschetz setup
  (the true compact-support map, `PD`, `PDt`) for the plane's own dual system;
* `transportPar_pairing`: the library's transport `x ↦ -E (x ∘ α)` of plane classes to line classes satisfies `⟨x, T y⟩_{ρ₂} = -⟨x, α^* y⟩_{B_P}`: the sign is the orientation sign built into the transport,
  and `E` enters only through the invariant pairing `B_P`;
* `badGoodPairingEven_eq_neg_plane`: the specialization to the library's even bad-line / good-plane pairing.
-/

noncomputable section

open Matrix
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (alpha planeComparison planeComparison_intertwines)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even
  (alpha_mul alpha_alpha planeComparisonEquiv planeTransportPar badGoodPairingEven
    badGoodPairingEven_apply planeComparison_injective)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators (upper lower reflection)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.GammaOneThree (core coreT coreL)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.EvenPlane

/-- **`α` as an automorphism of `Γ₁'(3)`.** -/
def alphaHom : binaryArithmeticLevel →* binaryArithmeticLevel where
  toFun := alpha
  map_one' := by
    have h := alpha_mul (1 : binaryArithmeticLevel) 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  map_mul' := alpha_mul

theorem alphaHom_apply (γ : binaryArithmeticLevel) : alphaHom γ = alpha γ := rfl

section Pull

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ₀ : Representation ℂ binaryArithmeticLevel V)

/-- **The pullback of crossed homomorphisms along `α`**: `c ↦ c ∘ α`, a crossed homomorphism for `ρ₀ ∘ α`. -/
def alphaCocycles : crossedCocycles ρ₀ →ₗ[ℂ] crossedCocycles (ρ₀.comp alphaHom) where
  toFun c := ⟨fun γ => c.1 (alpha γ), by
    intro g h
    change c.1 (alpha (g * h)) = c.1 (alpha g) + ρ₀ (alpha g) (c.1 (alpha h))
    rw [alpha_mul]
    exact c.2 (alpha g) (alpha h)⟩
  map_add' c d := Subtype.ext rfl
  map_smul' r c := Subtype.ext rfl

/-- **`α^* : H¹(Γ₁'(3), ρ₀) → H¹(Γ₁'(3), ρ₀ ∘ α)`.** -/
def alphaPull : CrossedH1 ρ₀ →ₗ[ℂ] CrossedH1 (ρ₀.comp alphaHom) :=
  (crossedBoundaries ρ₀).mapQ (crossedBoundaries (ρ₀.comp alphaHom)) (alphaCocycles ρ₀) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩)

theorem alphaCocycles_apply (c : crossedCocycles ρ₀) (γ : binaryArithmeticLevel) :
    (alphaCocycles ρ₀ c).1 γ = c.1 (alpha γ) := rfl

/-- **`α^*` preserves parabolic crossed homomorphisms** (`α` exchanges the two cusps). -/
theorem alphaCocycles_parabolic {c : crossedCocycles ρ₀} (hc : c ∈ parabolicCrossed ρ₀) :
    alphaCocycles ρ₀ c ∈ parabolicCrossed (ρ₀.comp alphaHom) := by
  have h := IdentBad.parabolic_pullback ρ₀ (ρ₀.comp alphaHom) LinearMap.id
    (fun γ v => rfl) (-c) (Submodule.neg_mem _ hc) (alphaCocycles ρ₀ c) (fun γ => by
      change c.1 (alpha γ) = -LinearMap.id ((-c).1 (alpha γ))
      simp)
  exact h

/-- **`α^*` on parabolic classes.** -/
def alphaPullPar : parabolicCrossedH1 ρ₀ →ₗ[ℂ] parabolicCrossedH1 (ρ₀.comp alphaHom) :=
  (alphaPull ρ₀).restrict (by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp (show x ∈ (parabolicCrossed ρ₀).map
      (crossedBoundaries ρ₀).mkQ from hx)
    exact Submodule.mem_map_of_mem (alphaCocycles_parabolic ρ₀ he))

theorem alphaPullPar_mk {e : crossedCocycles ρ₀} (he : e ∈ parabolicCrossed ρ₀) :
    alphaPullPar ρ₀ ⟨(crossedBoundaries ρ₀).mkQ e, Submodule.mem_map_of_mem he⟩ =
      ⟨(crossedBoundaries (ρ₀.comp alphaHom)).mkQ (alphaCocycles ρ₀ e),
        Submodule.mem_map_of_mem (alphaCocycles_parabolic ρ₀ he)⟩ := Subtype.ext rfl

end Pull

section Abstract

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ binaryArithmeticLevel V₁} {ρ₂ : Representation ℂ binaryArithmeticLevel V₂}
  {E : V₁ →ₗ[ℂ] V₂} (hE : ∀ γ v, E (ρ₁ (alpha γ) v) = ρ₂ γ (E v))

/-- The transport `x ↦ -E (x ∘ α)` of crossed homomorphisms of the plane system to the line system. -/
abbrev tcoc (e : crossedCocycles ρ₁) : crossedCocycles ρ₂ :=
  LocalPairingCaseL0Even.transportCocycles ρ₁ ρ₂ alpha alpha_mul E hE e

include hE in
theorem tcoc_parabolic {e : crossedCocycles ρ₁} (he : e ∈ parabolicCrossed ρ₁) :
    tcoc hE e ∈ parabolicCrossed ρ₂ :=
  IdentBad.parabolic_pullback ρ₁ ρ₂ E hE e he _
    (fun γ => LocalPairingCaseL0Even.transportCocycles_apply _ _ alpha alpha_mul _ _ e γ)

/-- **The transport on parabolic classes** (generic version of the library's `planeTransportPar`). -/
def transportPar : parabolicCrossedH1 ρ₁ →ₗ[ℂ] parabolicCrossedH1 ρ₂ :=
  (LocalPairingCaseL0Even.transportH1 ρ₁ ρ₂ alpha alpha_mul E hE).restrict (by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp (show x ∈ (parabolicCrossed ρ₁).map
      (crossedBoundaries ρ₁).mkQ from hx)
    exact Submodule.mem_map_of_mem (tcoc_parabolic hE he))

theorem transportPar_mk {e : crossedCocycles ρ₁} (he : e ∈ parabolicCrossed ρ₁) :
    transportPar hE ⟨(crossedBoundaries ρ₁).mkQ e, Submodule.mem_map_of_mem he⟩ =
      ⟨(crossedBoundaries ρ₂).mkQ (tcoc hE e), Submodule.mem_map_of_mem (tcoc_parabolic hE he)⟩ :=
  Subtype.ext rfl

/-- The plane pairing `B_P(v, w) = B(v, E w)`. -/
def planePairing (B : V₂ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) : V₂ →ₗ[ℂ] V₁ →ₗ[ℂ] ℂ := B.compl₂ E

theorem planePairing_apply (B : V₂ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) (v : V₂) (w : V₁) :
    planePairing (E := E) B v w = B v (E w) := rfl

variable {B : V₂ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ}

include hE in
/-- **The line system and the cusp-exchanged plane system form a twisted pairing.** -/
theorem planeTwisted (hEinj : Function.Injective E) (hEsurj : Function.Surjective E)
    (P : TwistedPairing ρ₂ ρ₂ B) :
    TwistedPairing ρ₂ (ρ₁.comp alphaHom) (planePairing (E := E) B) where
  left v h := by
    refine P.left v (fun w => ?_)
    obtain ⟨w', rfl⟩ := hEsurj w
    exact h w'
  right w h := by
    have h0 : E w = 0 := P.right _ (fun v => h v)
    exact hEinj (by rw [h0, map_zero])
  special g v w := by
    rw [planePairing_apply, planePairing_apply]
    have e : E ((ρ₁.comp alphaHom) g.1 w) = ρ₂ g.1 (E w) := hE g.1 w
    rw [e]
    exact P.special g v _
  odd v w := by
    rw [planePairing_apply, planePairing_apply]
    have e : E ((ρ₁.comp alphaHom) reflection w) =
        ρ₂ reflection (E w) := hE _ w
    rw [e]
    exact P.odd v _

end Abstract

section Compare

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ binaryArithmeticLevel V₁} {ρ₂ : Representation ℂ binaryArithmeticLevel V₂}
  {E : V₁ →ₗ[ℂ] V₂} (hE : ∀ γ v, E (ρ₁ (alpha γ) v) = ρ₂ γ (E v))
  {B : V₂ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ}

include hE in
/-- **The cup formulas of the line pairing (against the transported plane cocycle) and of the plane pairing (against the pulled back plane cocycle) differ by the sign of the transport.** -/
theorem cupFormula_plane (z : crossedCocycles ρ₂) (e : crossedCocycles ρ₁) (v : V₂ × V₂ × V₂) :
    CocycleBridge.cupFormula B (ρ₂.comp core.subtype) coreT coreL⁻¹ (fun m => z.1 (core.subtype m))
        (fun m => (tcoc hE e).1 (core.subtype m)) v =
      -CocycleBridge.cupFormula (planePairing (E := E) B) ((ρ₁.comp alphaHom).comp core.subtype)
        coreT coreL⁻¹ (fun m => z.1 (core.subtype m))
        (fun m => (alphaCocycles ρ₁ e).1 (core.subtype m)) v := by
  have key : ∀ (g : binaryArithmeticLevel) (w : V₁), E (ρ₁ (alpha g) w) = ρ₂ g (E w) := hE
  simp only [CocycleBridge.cupFormula, planePairing_apply, LocalPairingCaseL0Even.transportCocycles_apply,
    MonoidHom.comp_apply, map_neg, alphaCocycles_apply, alphaHom_apply, key]
  ring

end Compare

section Final

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ binaryArithmeticLevel V₁} {ρ₂ : Representation ℂ binaryArithmeticLevel V₂}
  {E : V₁ →ₗ[ℂ] V₂} (hE : ∀ γ v, E (ρ₁ (alpha γ) v) = ρ₂ γ (E v))
  {B : V₂ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ}

include hE in
/-- **The transported plane pairing is minus the plane pairing of the pulled back classes**:
`⟨x, T y⟩_B = -⟨x, α^* y⟩_{B_P}` for parabolic classes `x` of the line system and `y` of the plane system. -/
theorem transportPar_pairing (hEinj : Function.Injective E) (hEsurj : Function.Surjective E)
    (P : TwistedPairing ρ₂ ρ₂ B) (x : parabolicCrossedH1 ρ₂) (y : parabolicCrossedH1 ρ₁) :
    parabolicPairing P x (transportPar hE y) =
      -parabolicPairing (planeTwisted hE hEinj hEsurj P) x (alphaPullPar ρ₁ y) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp (show x ∈ (parabolicCrossed ρ₂).map
    (crossedBoundaries ρ₂).mkQ from hx)
  obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp (show y ∈ (parabolicCrossed ρ₁).map
    (crossedBoundaries ρ₁).mkQ from hy)
  obtain ⟨hzc, v, hv⟩ := mem_parabolicCochains.mp (mem_parabolicSub.mp hz)
  have e1 := parabolicPairing_apply P z (tcoc hE e) hz (tcoc_parabolic hE he) hv
  have e2 := parabolicPairing_apply (planeTwisted hE hEinj hEsurj P) z (alphaCocycles ρ₁ e) hz
    (alphaCocycles_parabolic ρ₁ he) hv
  have hT := transportPar_mk hE he
  have hA := alphaPullPar_mk ρ₁ he
  exact (congrArg (parabolicPairing P _) hT).trans (e1.trans
    ((cupFormula_plane hE z e v).trans
      ((congrArg Neg.neg e2.symm).trans
        (congrArg (fun w => -parabolicPairing (planeTwisted hE hEinj hEsurj P) _ w) hA.symm))))

end Final

section Concrete

variable {n : ℕ}

/-- **The library's transport of plane classes is the generic transport** for `E = planeComparison n`. -/
theorem planeTransportPar_eq (heven : Even n) :
    planeTransportPar heven =
      transportPar (ρ₁ := levelRep (n + 1) (-1)) (ρ₂ := binaryArithmeticRepresentation n)
        (planeComparison_intertwines n heven) := rfl

/-- **The even bad-line / good-plane pairing of the library, in terms of the plane's own dual system.**  `badGoodPairingEven x y` is MINUS
the parabolic cup pairing of the line classes `x` (coefficients `Sym^{n+1}`) with the pulled back plane classes `α^* y` (coefficients
`(Sym^{n+1} ⊗ det⁻¹) ∘ α`) for the invariant `ε`-odd pairing `⟨v, E w⟩`; the comparison `E` enters only through this pairing. -/
theorem badGoodPairingEven_eq_neg_plane (heven : Even n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (y : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    badGoodPairingEven heven x y =
      -parabolicPairing
        (planeTwisted (planeComparison_intertwines n heven) (planeComparison_injective n)
          (planeComparisonEquiv n).surjective (twistedPairing_binaryArithmeticRepresentation n heven))
        x (alphaPullPar (levelRep (n + 1) (-1)) y) := by
  rw [badGoodPairingEven_apply, planeTransportPar_eq heven]
  exact transportPar_pairing (planeComparison_intertwines n heven) (planeComparison_injective n)
    (planeComparisonEquiv n).surjective (twistedPairing_binaryArithmeticRepresentation n heven) x y

end Concrete

section ImagePairing

variable {n : ℕ}

/-- **The even bad-line / good-plane pairing is minus the Lefschetz pairing of the images of compactly supported cohomology of the plane's own dual system.**
`planeSetup` is the Poincare-Lefschetz setup (true compact-support map `j`, `PD`, `PDt`) for the line system `Sym^{n+1}` and the cusp-exchanged plane system. -/
theorem badGoodPairingEven_eq_neg_imagePairing (heven : Even n)
    (x : parabolicCrossedH1 (binaryArithmeticRepresentation n))
    (y : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    badGoodPairingEven heven x y =
      -(GammaThree.setup (planeTwisted (planeComparison_intertwines n heven) (planeComparison_injective n)
          (planeComparisonEquiv n).surjective (twistedPairing_binaryArithmeticRepresentation n heven))).imagePairing
        ((GammaThree.toParabolic (planeTwisted (planeComparison_intertwines n heven)
          (planeComparison_injective n) (planeComparisonEquiv n).surjective
          (twistedPairing_binaryArithmeticRepresentation n heven))).symm x)
        ((GammaThree.toParabolic' (planeTwisted (planeComparison_intertwines n heven)
          (planeComparison_injective n) (planeComparisonEquiv n).surjective
          (twistedPairing_binaryArithmeticRepresentation n heven))).symm
          (alphaPullPar (levelRep (n + 1) (-1)) y)) := by
  have h := GammaThree.imagePairing_eq'
    (planeTwisted (planeComparison_intertwines n heven) (planeComparison_injective n)
      (planeComparisonEquiv n).surjective (twistedPairing_binaryArithmeticRepresentation n heven))
    ((GammaThree.toParabolic (planeTwisted (planeComparison_intertwines n heven)
      (planeComparison_injective n) (planeComparisonEquiv n).surjective
      (twistedPairing_binaryArithmeticRepresentation n heven))).symm x)
    ((GammaThree.toParabolic' (planeTwisted (planeComparison_intertwines n heven)
      (planeComparison_injective n) (planeComparisonEquiv n).surjective
      (twistedPairing_binaryArithmeticRepresentation n heven))).symm
      (alphaPullPar (levelRep (n + 1) (-1)) y))
  have e1 := (GammaThree.toParabolic (planeTwisted (planeComparison_intertwines n heven)
      (planeComparison_injective n) (planeComparisonEquiv n).surjective
      (twistedPairing_binaryArithmeticRepresentation n heven))).apply_symm_apply x
  have e2 := (GammaThree.toParabolic' (planeTwisted (planeComparison_intertwines n heven)
      (planeComparison_injective n) (planeComparisonEquiv n).surjective
      (twistedPairing_binaryArithmeticRepresentation n heven))).apply_symm_apply
      (alphaPullPar (levelRep (n + 1) (-1)) y)
  have e := congrArg₂ (fun a b => parabolicPairing (planeTwisted (planeComparison_intertwines n heven)
      (planeComparison_injective n) (planeComparisonEquiv n).surjective
      (twistedPairing_binaryArithmeticRepresentation n heven)) a b) e1.symm e2.symm
  exact (badGoodPairingEven_eq_neg_plane heven x y).trans
    (congrArg Neg.neg (e.trans h.symm))

end ImagePairing

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL.EvenPlane
