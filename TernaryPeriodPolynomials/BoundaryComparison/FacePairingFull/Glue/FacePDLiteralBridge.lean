module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Bridge
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ModelDual

@[expose] public section


/-!
# The good-line face coefficient systems computed from the literal contragredient `E*`

Formalized by Claude Sonnet 5.5.

The Kostant bridges of the library compute the Levi modules `Sym^{n+1} ⊗ det^e`, `Sym^{n+1} ⊗ det^{e'}` of the cohomology of the radical lattice from
cocycles of `E` and of the MODEL dual `E^φ = E ∘ dualInvolution`, paired by the apolar `dualPairing` (`LevelOneBridge`).  Here:

* generic transport: an equivariant linear map `L : W₁ → W₂` of dual coefficient systems acts on one-cochains by postcomposition (`comp1`) and commutes with
  `pull1`, `leviCocycle`, `cochainRep`, preserves `UCocycle`, `FiberHyp`, and moves the Kostant pairing: `kostant B σ f (L ∘ g) = kostant (B ∘ L) σ f g`;
* `thetaInv_equivariant`: for every character `χ`, `Θ⁻¹ : E* → E^φ` (the `ModelDual.thetaModelEquiv`) intertwines the contragredient with `E^φ`;
* `LiteralLevelOneBridge`: the same data as `LevelOneBridge`, for the LITERAL dual `E* = (rationalCoefficientComponent n χ).dual` on `Module.Dual ℂ E`,
  paired by the evaluation `E ⊗ E* → ℂ` (`evPairing`);
* `LevelOneBridge.toLiteral`: every level-one bridge of the model dual gives the literal bridge with the SAME modules `M`, `M'`, the SAME pairing `B₂`, the SAME constant
  `c` (`-(n+1)!` for the library's bridges), the same Levi embedding, the same coordinate `Φ` and the coordinate `Ψ ∘ (Θ⁻¹)_*`; the determinant characters are those of the model
  bridge (`levelOneBridgeTrivialLiteral`: `(e, e') = (0, -1)`; `levelOneBridgeOddLiteral`: `(-1, 0)`);
* `kostant_literal_eq`: the Kostant pairing of `E` with the literal `E*` is `-(n+1)!` times the apolar binary pairing of the coordinates.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.BoundaryDuality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.LiteralBridge

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (S T₀ L₁)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolic (LevelOneBridge)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (GL2Z toGL cocycleInclusion)

/-! ### Generic transport along an equivariant map of coefficients -/

section Generic

variable {G V W₁ W₂ : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁]
  [AddCommGroup W₂] [Module ℂ W₂] {ρ₁ : Representation ℂ G W₁} {ρ₂ : Representation ℂ G W₂}

/-- Postcomposition of a one-cochain with a linear map of coefficients. -/
def comp1 (L : W₁ →ₗ[ℂ] W₂) (f : (Fin 2 → G) → W₁) : (Fin 2 → G) → W₂ := fun x => L (f x)

/-- Postcomposition as a linear map of cochain spaces. -/
def comp1L (L : W₁ →ₗ[ℂ] W₂) : ((Fin 2 → G) → W₁) →ₗ[ℂ] ((Fin 2 → G) → W₂) where
  toFun := comp1 L
  map_add' f g := by
    funext x
    exact map_add L _ _
  map_smul' c f := by
    funext x
    exact map_smul L c _

variable (L : W₁ →ₗ[ℂ] W₂) (hL : ∀ g w, L (ρ₁ g w) = ρ₂ g (L w))
include hL

theorem pull1_comp (h : G) (f : (Fin 2 → G) → W₁) :
    pull1 ρ₂ h (comp1 L f) = comp1 L (pull1 ρ₁ h f) := by
  funext x
  exact (hL h⁻¹ _).symm

theorem cochainRep_comp (h : G) (f : (Fin 2 → G) → W₁) :
    cochainRep ρ₂ h (comp1 L f) = comp1 L (cochainRep ρ₁ h f) :=
  pull1_comp L hL h⁻¹ f

theorem leviCocycle_comp (ω : (Fin 2 → G) → W₁) (h : G) :
    leviCocycle ρ₂ (comp1 L ω) h = comp1 L (leviCocycle ρ₁ ω h) := by
  funext x
  change pull1 ρ₂ h (comp1 L ω) x - comp1 L ω x = L (pull1 ρ₁ h ω x - ω x)
  rw [pull1_comp L hL, map_sub]
  rfl

omit hL [Group G] in
theorem differentialOneRaw_comp (f : (Fin 2 → G) → W₁) (x : Fin 3 → G) :
    differentialOneRaw (comp1 L f) x = L (differentialOneRaw f x) := by
  unfold differentialOneRaw comp1
  rw [map_add, map_sub]

theorem uCocycle_comp {U : Subgroup G} {f : (Fin 2 → G) → W₁} (hf : UCocycle ρ₁ U f) :
    UCocycle ρ₂ U (comp1 L f) :=
  ⟨fun γ hγ a b => by
    change L (f ![γ * a, γ * b]) = ρ₂ γ (L (f ![a, b]))
    rw [hf.1 γ hγ a b, hL],
   fun x => by rw [differentialOneRaw_comp, hf.2 x, map_zero]⟩

omit hL [Group G] in
theorem kostant_comp (B : V →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ) (σ : Chains G 2) (f : (Fin 2 → G) → V)
    (g : (Fin 2 → G) → W₁) : kostant B σ f (comp1 L g) = kostant (B.compl₂ L) σ f g := rfl

end Generic

/-! ### The literal contragredient -/

section Literal

variable (n : ℕ) (χ : RankOneCharacter)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **`Θ⁻¹ : E* → E^φ` intertwines the contragredient with the model dual**, for every character. -/
theorem thetaInv_equivariant (g : RationalGL3) (ξ : Module.Dual ℂ (HomogeneousPoly n)) :
    (thetaModelEquiv n).symm ((rationalCoefficientComponent n χ).dual g ξ) =
      dualRep (dualityData n χ) g ((thetaModelEquiv n).symm ξ) := by
  apply (thetaModelEquiv n).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := thetaModel_equivariant n χ g ((thetaModelEquiv n).symm ξ)
  have e : thetaModel n ((thetaModelEquiv n).symm ξ) = ξ := (thetaModelEquiv n).apply_symm_apply ξ
  rw [e] at h
  exact h.symm

open TernaryPeriodPolynomials.Argument.EisensteinDual in
theorem theta_equivariant (g : RationalGL3) (w : HomogeneousPoly n) :
    thetaModelEquiv n (dualRep (dualityData n χ) g w) =
      (rationalCoefficientComponent n χ).dual g (thetaModelEquiv n w) :=
  thetaModel_equivariant n χ g w

/-- **The evaluation pairing `E ⊗ E* → ℂ`.** -/
def evPairing : HomogeneousPoly n →ₗ[ℂ] Module.Dual ℂ (HomogeneousPoly n) →ₗ[ℂ] ℂ :=
  (LinearMap.id : Module.Dual ℂ (HomogeneousPoly n) →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ).flip

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- The evaluation pairing, composed with `Θ`, is the apolar `dualPairing`, with scalar `1`. -/
theorem evPairing_compl (v w : HomogeneousPoly n) :
    evPairing n v (thetaModelEquiv n w) = dualPairing n v w := rfl

open TernaryPeriodPolynomials.Argument.EisensteinDual in
theorem evPairing_symm (v : HomogeneousPoly n) (ξ : Module.Dual ℂ (HomogeneousPoly n)) :
    dualPairing n v ((thetaModelEquiv n).symm ξ) = evPairing n v ξ := by
  rw [← evPairing_compl, LinearEquiv.apply_symm_apply]

open TernaryPeriodPolynomials.Argument.EisensteinDual in
theorem kostant_literal_comp' (σ : Chains RationalGL3 2) (f : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (g : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)) :
    kostant (evPairing n) σ f g =
      kostant (dualPairing n) σ f (comp1 (thetaModelEquiv n).symm.toLinearMap g) := by
  have h : cup11 (evPairing n) f g = cup11 (dualPairing n) f (comp1 (thetaModelEquiv n).symm.toLinearMap g) := by
    funext x
    exact (evPairing_symm n _ _).symm
  unfold kostant
  rw [h]

end Literal


/-! ### The literal level-one bridge -/

section Bridge

variable {n : ℕ} {χ : RankOneCharacter}

/-- The literal contragredient `E*` as a representation of `GL₃(ℚ)`. -/
abbrev litRep (n : ℕ) (χ : RankOneCharacter) : Representation ℂ RationalGL3 (Module.Dual ℂ (HomogeneousPoly n)) :=
  (rationalCoefficientComponent n χ).dual

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **The level-one bridge for the literal contragredient**: the data of `LevelOneBridge`, with the dual coefficients `E*` (the contragredient
of `E`, acting on `Module.Dual ℂ E`) in place of the model dual `E ∘ φ`, paired by the evaluation `E ⊗ E* → ℂ`. -/
structure LiteralLevelOneBridge (n : ℕ) (χ : RankOneCharacter) (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (θU : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n))
    (M M' : Rep.{0, 0, 0} ℂ GL2Z) (B₂ : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ)
    (x : groupCohomology.cocycles₁ M) (x' : groupCohomology.cocycles₁ M') (c : ℂ) where
  levi : GL2Z →* RationalGL3
  Φ : ((Fin 2 → RationalGL3) → HomogeneousPoly n) →ₗ[ℂ] M
  Ψ : ((Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)) →ₗ[ℂ] M'
  levi_S : levi (toGL ModularGroup.S) = S
  levi_T : levi (toGL ModularGroup.T) = T₀
  pairing : ∀ f g, UCocycle (rationalCoefficientComponent n χ) latL1.sub f →
    UCocycle (litRep n χ) latL1.sub g → kostant (evPairing n) latL1.σ f g = c * B₂ (Φ f) (Ψ g)
  alpha : ∀ γ, Φ (leviCocycle (rationalCoefficientComponent n χ) ωU (levi γ)⁻¹) = cocycleInclusion M x γ
  beta : ∀ γ, Ψ (leviCocycle (litRep n χ) θU (levi γ)⁻¹) = cocycleInclusion M' x' γ
  equivΦ : ∀ γ f, UCocycle (rationalCoefficientComponent n χ) latL1.sub f →
    Φ (cochainRep (rationalCoefficientComponent n χ) (levi γ) f) = M.ρ γ (Φ f)
  equivΨ : ∀ γ g, UCocycle (litRep n χ) latL1.sub g →
    Ψ (cochainRep (litRep n χ) (levi γ) g) = M'.ρ γ (Ψ g)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **Transport of a level-one bridge to the literal contragredient**: same modules, same pairing, same constant, same Levi embedding, same coordinate `Φ`
and the coordinate `Ψ ∘ (Θ⁻¹)_*`; the fiber datum `θ_U` becomes `Θ ∘ θ_U`. -/
def LevelOneBridge.toLiteral {ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    {M M' : Rep.{0, 0, 0} ℂ GL2Z} {B₂ : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ}
    {x : groupCohomology.cocycles₁ M} {x' : groupCohomology.cocycles₁ M'} {c : ℂ}
    (Br : LevelOneBridge (dualityData n χ) ωU θU M M' B₂ x x' c) :
    LiteralLevelOneBridge n χ ωU (comp1 (thetaModelEquiv n).toLinearMap θU) M M' B₂ x x' c where
  levi := Br.levi
  Φ := Br.Φ
  Ψ := Br.Ψ.comp (comp1L (thetaModelEquiv n).symm.toLinearMap)
  levi_S := Br.levi_S
  levi_T := Br.levi_T
  pairing f g hf hg := by
    rw [kostant_literal_comp' n latL1.σ f g]
    exact Br.pairing f _ hf (uCocycle_comp (thetaModelEquiv n).symm.toLinearMap
      (fun h w => thetaInv_equivariant n χ h w) hg)
  alpha := Br.alpha
  beta γ := by
    have h := Br.beta γ
    rw [← h]
    change Br.Ψ (comp1 (thetaModelEquiv n).symm.toLinearMap
      (leviCocycle (litRep n χ) (comp1 (thetaModelEquiv n).toLinearMap θU) (Br.levi γ)⁻¹)) = _
    rw [leviCocycle_comp (thetaModelEquiv n).toLinearMap (fun h w => theta_equivariant n χ h w)]
    have e : comp1 (thetaModelEquiv n).symm.toLinearMap
        (comp1 (thetaModelEquiv n).toLinearMap (leviCocycle (dualRep (dualityData n χ)) θU (Br.levi γ)⁻¹)) =
        leviCocycle (dualRep (dualityData n χ)) θU (Br.levi γ)⁻¹ := by
      funext y
      exact (thetaModelEquiv n).symm_apply_apply _
    rw [e]
  equivΦ := Br.equivΦ
  equivΨ γ g hg := by
    change Br.Ψ (comp1 (thetaModelEquiv n).symm.toLinearMap (cochainRep (litRep n χ) (Br.levi γ) g)) = _
    rw [← cochainRep_comp (thetaModelEquiv n).symm.toLinearMap (fun h w => thetaInv_equivariant n χ h w)]
    exact Br.equivΨ γ _ (uCocycle_comp (thetaModelEquiv n).symm.toLinearMap
      (fun h w => thetaInv_equivariant n χ h w) hg)

end Bridge


/-! ### The coordinates of the literal dual -/

section Coordinates

variable (n : ℕ) (χ : RankOneCharacter)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **The rotated identity-plane coordinate of a cocycle of the literal dual `E*`**: the model coordinate `Ψ` of `Θ⁻¹ ∘ g`. -/
def PsiLit (g : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)) : Binary.HomogeneousPoly (n + 1) :=
  PsiTotal n (comp1 (thetaModelEquiv n).symm.toLinearMap g)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- `Θ⁻¹ ∘ g` is a `U`-equivariant cocycle of the model dual when `g` is one of the contragredient. -/
theorem uCocycle_thetaInv {g : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)}
    (hg : UCocycle (litRep n χ) latL1.sub g) :
    UCocycle (dualRep (dualityData n χ)) latL1.sub (comp1 (thetaModelEquiv n).symm.toLinearMap g) :=
  uCocycle_comp (thetaModelEquiv n).symm.toLinearMap (fun h w => thetaInv_equivariant n χ h w) hg

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **Levi equivariance of the literal coordinate** (exact character): the Levi translate of a `U`-equivariant cocycle of the contragredient `E*` has the coordinate
`detSign χ (diag(γ^{-T}, 1)) • (γ ⋆_{n+2} Ψ g)`, as for the model dual. -/
theorem PsiLit_levi {g : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)}
    (hg : UCocycle (litRep n χ) latL1.sub g) (γ : GL2Z) :
    PsiLit n (cochainRep (litRep n χ) (leviHom γ) g) =
      Twisted.detSign χ (leviHom (invT γ)) •
        Binary.homogeneousAction (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
          (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) (PsiLit n g) := by
  unfold PsiLit
  rw [← cochainRep_comp (thetaModelEquiv n).symm.toLinearMap (fun h w => thetaInv_equivariant n χ h w)]
  exact Psi_levi n χ (uCocycle_thetaInv n χ hg) γ

/-- **The Kostant pairing of `E` with the literal `E*`** (evaluation pairing): `κ(f, g) = -(n+1)! · ⟨Φ f, Ψ g⟩`, with the same constant as for the model dual. -/
theorem kostant_literal_eq (positive : 0 < n) {f : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    {g : (Fin 2 → RationalGL3) → Module.Dual ℂ (HomogeneousPoly n)}
    (hf : UCocycle (rationalCoefficientComponent n χ) latL1.sub f)
    (hg : UCocycle (litRep n χ) latL1.sub g) :
    kostant (evPairing n) latL1.σ f g =
      (-((n + 1).factorial : ℂ)) * BinaryPairing.binaryPairing (n + 1) (PhiTotal n f) (PsiLit n g) := by
  rw [kostant_literal_comp' n latL1.σ f g]
  exact kostant_eq_binaryPairing n χ positive hf (uCocycle_thetaInv n χ hg)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **Transport of the fiber hypotheses** to the literal dual: the model-dual data `(η, θ_U)` become `(Θ ∘ η, Θ ∘ θ_U)`, the pairing becomes the evaluation. -/
theorem FiberHyp.toLiteral {Λ Λe U : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B Λ Λe U ζ η ω ωU θU) :
    FiberHyp (rationalCoefficientComponent n χ) (litRep n χ) (evPairing n) Λ Λe U ζ
      (fun x => thetaModelEquiv n (η x)) ω ωU (comp1 (thetaModelEquiv n).toLinearMap θU) where
  le := hF.le
  le_edge := hF.le_edge
  invariant g hg v w := by
    obtain ⟨w', rfl⟩ := (thetaModelEquiv n).surjective w
    rw [← theta_equivariant n χ g w']
    exact (hF.invariant g hg v w')
  zeta_eq := hF.zeta_eq
  zeta_cocycle := hF.zeta_cocycle
  eta_eq γ hγ a b c := by
    change thetaModelEquiv n (η ![γ * a, γ * b, γ * c]) = _
    rw [hF.eta_eq γ hγ a b c, theta_equivariant n χ]
  eta_cocycle x := by
    have h := hF.eta_cocycle x
    simp only [← map_sub, ← map_add]
    rw [h, map_zero]
  omega_eq := hF.omega_eq
  omega_d := hF.omega_d
  omegaU_eq := hF.omegaU_eq
  omegaU_d := hF.omegaU_d
  thetaU_eq γ hγ a b := by
    change thetaModelEquiv n (θU ![γ * a, γ * b]) = _
    rw [hF.thetaU_eq γ hγ a b, theta_equivariant n χ]
    rfl
  thetaU_d a b c := by
    rw [differentialOneRaw_comp, hF.thetaU_d a b c]
    rfl

end Coordinates


/-! ### The bridges of the library for the literal dual -/

section Instances

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **The level-one bridge at the good line for the LITERAL dual, trivial character, `n` odd**: `M = Sym^{n+1} ⊗ det^0`, `M' = Sym^{n+1} ⊗ det^{-1}`, constant `-(n+1)!`. -/
def levelOneBridgeTrivialLiteral (hn : Odd n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :=
  LevelOneBridge.toLiteral (levelOneBridgeTrivial hn hF)

open TernaryPeriodPolynomials.Argument.EisensteinDual in
/-- **The level-one bridge at the good line for the LITERAL dual, a character with `χ(-1_∞) = -1`**: `M = Sym^{n+1} ⊗ det^{-1}`, `M' = Sym^{n+1} ⊗ det^0`. -/
def levelOneBridgeOddLiteral (hn : Odd n) (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :=
  LevelOneBridge.toLiteral (levelOneBridgeOdd hn h hF)

end Instances

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.LiteralBridge
