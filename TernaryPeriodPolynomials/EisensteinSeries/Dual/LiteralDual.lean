module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ModelDual
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Maps
public import TernaryPeriodPolynomials.BoundaryComparison.FaceRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Perfect

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

/-!
# Transport of the target dual statements to the literal contragredient `E*`

Formalized by Claude Sonnet 5.5.

The targets `Targets/LemmaC2` and `Targets/FacePairing` encode `E*` as `E ∘ dualInvolution` and
pair by the apolar `dualPairing`.  Here the cohomological statements are transported along `thetaModelEquiv` (the ONLY comparison map used:
`w ↦ (v ↦ dualPairing v w)`, `ModelDual`) to statements for the literal contragredient `ρ^∨ = (rationalCoefficientComponent n triv).dual` on
`Module.Dual ℂ (HomogeneousPoly n)`, paired by evaluation `E* ⊗ E → ℂ`:

* `coeffCochains`, `coeffCocycles`, `coeffCocycles_boundaryMap`, `classOf_coeff`: an equivariant linear map of coefficients acts on homogeneous
  cochains/cocycles, commutes with the differentials and preserves cohomologous cocycles;
* `phiGen` (the pullback `c ↦ c ∘ φ` for any `ρ' = ρ ∘ φ`), `thetaCocycles`, `thetaXCocycles`: `Θ` on global and flag cocycles;
* `toFrozen`: the model cocycle `φ^*(Θ⁻¹ c'')` attached to a cocycle `c''` of `E*`;
* `lemma_C_2_literal`: Lemma C.2 for `c'' ∈ Z²(Γ, E*)`, from the `face_pairing_stokes`;
* `face_pairing_perfect_literal`: the perfect line face pairing `ar:eq:facepair` for classes of `E*` (inner = zero flag restrictions), from the `face_pairing_perfect`.

`Targets/PropC5` involves no dual coefficient system and needs no transport.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

/-! ### Coefficient change on homogeneous cochains and cocycles -/

section CoeffChange

variable {G : Type} [Group G] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (Γ : Subgroup G) (ρ1 : Representation ℂ G V) (ρ2 : Representation ℂ G W) (L : V →ₗ[ℂ] W)
  (hL : ∀ g v, L (ρ1 g v) = ρ2 g (L v))

/-- Applying an equivariant linear map of coefficients to homogeneous cochains. -/
def coeffCochains (k : ℕ) : cochains Γ ρ1 k →ₗ[ℂ] cochains Γ ρ2 k where
  toFun f := ⟨fun x => L (f.val x), fun γ x => by
    change L (f.val (fun i => γ.val * x i)) = ρ2 γ.val (L (f.val x))
    rw [f.property γ x, hL]⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact map_add L _ _
  map_smul' a f := by
    apply Subtype.ext
    funext x
    exact map_smul L a _

theorem coeffCochains_val (k : ℕ) (f : cochains Γ ρ1 k) (x : Fin (k + 1) → G) :
    (coeffCochains Γ ρ1 ρ2 L hL k f).val x = L (f.val x) := rfl

theorem coeffCochains_differentialOne (f : cochains Γ ρ1 1) :
    coeffCochains Γ ρ1 ρ2 L hL 2 (differentialOne Γ ρ1 f) =
      differentialOne Γ ρ2 (coeffCochains Γ ρ1 ρ2 L hL 1 f) := by
  apply Subtype.ext
  funext x
  change L (f.val ![x 1, x 2] - f.val ![x 0, x 2] + f.val ![x 0, x 1]) =
    L (f.val ![x 1, x 2]) - L (f.val ![x 0, x 2]) + L (f.val ![x 0, x 1])
  rw [map_add, map_sub]

/-- Applying an equivariant linear map of coefficients to degree-two cocycles. -/
def coeffCocycles : cocycles Γ ρ1 →ₗ[ℂ] cocycles Γ ρ2 where
  toFun c := ⟨coeffCochains Γ ρ1 ρ2 L hL 2 c.val, by
    have h := LinearMap.mem_ker.mp c.property
    apply LinearMap.mem_ker.mpr
    funext x
    have h' := congrFun h x
    change L (c.val.val ![x 1, x 2, x 3]) - L (c.val.val ![x 0, x 2, x 3]) +
        L (c.val.val ![x 0, x 1, x 3]) - L (c.val.val ![x 0, x 1, x 2]) = 0
    change c.val.val ![x 1, x 2, x 3] - c.val.val ![x 0, x 2, x 3] +
        c.val.val ![x 0, x 1, x 3] - c.val.val ![x 0, x 1, x 2] = 0 at h'
    rw [← map_sub, ← map_add, ← map_sub, h', map_zero]⟩
  map_add' a c := Subtype.ext (map_add (coeffCochains Γ ρ1 ρ2 L hL 2) a.val c.val)
  map_smul' a c := Subtype.ext (map_smul (coeffCochains Γ ρ1 ρ2 L hL 2) a c.val)

theorem coeffCocycles_val (c : cocycles Γ ρ1) (x : Fin 3 → G) :
    (coeffCocycles Γ ρ1 ρ2 L hL c).val.val x = L (c.val.val x) := rfl

theorem coeffCocycles_boundaryMap (f : cochains Γ ρ1 1) :
    coeffCocycles Γ ρ1 ρ2 L hL (boundaryMap Γ ρ1 f) = boundaryMap Γ ρ2 (coeffCochains Γ ρ1 ρ2 L hL 1 f) :=
  Subtype.ext (coeffCochains_differentialOne Γ ρ1 ρ2 L hL f)

end CoeffChange

/-! ### The inverse transport along `φ` and the model isomorphism on cocycles -/

section Phi

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The global cocycle `x ↦ c(φ x)` for any `ρ' = ρ ∘ φ` (`phiCocycle` is the case `ρ' = dualRep ρ`). -/
def phiGen (ρ ρ' : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ' g = ρ (dualInvolution g)) :
    cocycles rationalLevel ρ →ₗ[ℂ] cocycles rationalLevel ρ' where
  toFun c := ⟨⟨fun x => c.val.val (fun i => dualInvolution (x i)), by
    intro γ x
    have hlevel : dualInvolution γ.val ∈ rationalLevel :=
      dualInvolution_mem_rationalLevel γ.property
    have h := c.val.property ⟨dualInvolution γ.val, hlevel⟩ (fun i => dualInvolution (x i))
    have hv : (fun i => dualInvolution (γ.val * x i)) =
        fun i => dualInvolution γ.val * dualInvolution (x i) := by
      funext i
      exact map_mul dualInvolution _ _
    change c.val.val (fun i => dualInvolution (γ.val * x i)) =
      ρ' γ.val (c.val.val (fun i => dualInvolution (x i)))
    rw [hv, hρ γ.val]
    exact h⟩, by
    funext x
    have h := congrFun c.property (fun i => dualInvolution (x i))
    change c.val.val (fun i => dualInvolution ((![x 1, x 2, x 3] : Fin 3 → RationalGL3) i)) -
        c.val.val (fun i => dualInvolution ((![x 0, x 2, x 3] : Fin 3 → RationalGL3) i)) +
        c.val.val (fun i => dualInvolution ((![x 0, x 1, x 3] : Fin 3 → RationalGL3) i)) -
        c.val.val (fun i => dualInvolution ((![x 0, x 1, x 2] : Fin 3 → RationalGL3) i)) = 0
    rw [phi_vec3, phi_vec3, phi_vec3, phi_vec3]
    exact h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem phiGen_val (ρ ρ' : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ' g = ρ (dualInvolution g))
    (c : cocycles rationalLevel ρ) (x : Fin 3 → RationalGL3) :
    (phiGen ρ ρ' hρ c).val.val x = c.val.val (fun i => dualInvolution (x i)) := rfl

end Phi

section Theta

variable (n : ℕ)

theorem theta_intertwines (g : RationalGL3) (v : HomogeneousPoly n) :
    thetaModel n (dualRep (rationalCoefficientComponent n trivialCharacter) g v) =
      (rationalCoefficientComponent n trivialCharacter).dual g (thetaModel n v) :=
  thetaModel_equivariant n trivialCharacter g v

theorem thetaInv_intertwines (g : RationalGL3) (ξ : Module.Dual ℂ (HomogeneousPoly n)) :
    (thetaModelEquiv n).symm ((rationalCoefficientComponent n trivialCharacter).dual g ξ) =
      dualRep (rationalCoefficientComponent n trivialCharacter) g ((thetaModelEquiv n).symm ξ) := by
  apply (thetaModelEquiv n).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := theta_intertwines n g ((thetaModelEquiv n).symm ξ)
  have e : thetaModel n ((thetaModelEquiv n).symm ξ) = ξ := (thetaModelEquiv n).apply_symm_apply ξ
  rw [e] at h
  exact h.symm

/-- `Θ` on global cocycles: `E ∘ φ ⟶ E*`. -/
def thetaCocycles : cocycles rationalLevel (dualRep (rationalCoefficientComponent n trivialCharacter)) →ₗ[ℂ]
    cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual :=
  coeffCocycles rationalLevel _ _ (thetaModel n) (theta_intertwines n)

/-- `Θ⁻¹` on global cocycles: `E* ⟶ E ∘ φ`. -/
def thetaInvCocycles : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual →ₗ[ℂ]
    cocycles rationalLevel (dualRep (rationalCoefficientComponent n trivialCharacter)) :=
  coeffCocycles rationalLevel _ _ (thetaModelEquiv n).symm.toLinearMap (thetaInv_intertwines n)

end Theta

section C2

variable (n : ℕ)

/-- The literal-dual global cocycle `c''` of `E*` and the model cocycle `c' = φ^*(Θ⁻¹ c'')` of `E`. -/
def toFrozen (c'' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual) :
    cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter) :=
  phiGen (dualRep (rationalCoefficientComponent n trivialCharacter)) (rationalCoefficientComponent n trivialCharacter)
    (dualRep_dualRep_apply _) (thetaInvCocycles n c'')

theorem toFrozen_val (c'' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual)
    (x : Fin 3 → RationalGL3) :
    (toFrozen n c'').val.val (fun i => dualInvolution (x i)) = (thetaModelEquiv n).symm (c''.val.val x) := by
  change (thetaModelEquiv n).symm (c''.val.val (fun i => dualInvolution (dualInvolution (x i)))) = _
  simp only [dualInvolution_involutive]

theorem pairing_literal (u : HomogeneousPoly n) (ξ : Module.Dual ℂ (HomogeneousPoly n)) :
    dualPairing n u ((thetaModelEquiv n).symm ξ) = ξ u := by
  rw [← thetaModelEquiv_eval, LinearEquiv.apply_symm_apply]

theorem toFrozen_vec (c'' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual)
    (a b c : RationalGL3) :
    (toFrozen n c'').val.val ![dualInvolution a, dualInvolution b, dualInvolution c] =
      (thetaModelEquiv n).symm (c''.val.val ![a, b, c]) := by
  rw [← phi_vec3, toFrozen_val]

/-- **Lemma C.2 (Stokes) for the literal dual `E*`**, transported from the target `face_pairing_stokes` along `thetaModelEquiv`: the dual
global class is a cocycle `c''` of the contragredient representation, paired by evaluation `E* ⊗ E → ℂ`. -/
theorem lemma_C_2_literal
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (c'' : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter).dual)
    (w : EdgeCochains n trivialCharacter 1)
    (hw : ∀ x e, c.val.val x = differentialOneRaw w.val x e)
    (γP : (Fin 4 → RationalGL3) → Flags .plane → ℂ)
    (hγP : γP ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3)
    (hdγP : ∀ x P, differentialThreeRaw γP x P =
      (c''.val.val ![x 2, x 3, x 4]) (c.val.val ![x 0, x 1, x 2]))
    (γQ : (Fin 4 → RationalGL3) → Flags .line → ℂ)
    (hγQ : γQ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3)
    (hdγQ : ∀ x F, differentialThreeRaw γQ x F =
      (c''.val.val ![x 2, x 3, x 4]) (c.val.val ![x 0, x 1, x 2])) :
    BoundaryExact (fun x e =>
      ((c''.val.val ![x 1, x 2, x 3]) (w.val ![x 0, x 1] e) - γP x (endpoint .plane e)) -
      ((c''.val.val ![x 1, x 2, x 3]) (w.val ![x 0, x 1] e) - γQ x (endpoint .line e))) := by
  have h := face_pairing_stokes n c (toFrozen n c'') w hw γP hγP
    (fun x P => by rw [hdγP, toFrozen_vec, pairing_literal]) γQ hγQ
    (fun x F => by rw [hdγQ, toFrozen_vec, pairing_literal])
  simpa only [toFrozen_vec, pairing_literal] using h

end C2

/-! ### The face pairing for the literal dual -/

section FacePairing

variable (n : ℕ) (X : Type) [MulAction RationalGL3 X]

/-- Pointwise `Θ` on functions on a `GL₃(ℚ)`-set. -/
def thetaFun : (X → HomogeneousPoly n) →ₗ[ℂ] (X → Module.Dual ℂ (HomogeneousPoly n)) :=
  LinearMap.compLeft (thetaModel n) X

def thetaFunInv : (X → Module.Dual ℂ (HomogeneousPoly n)) →ₗ[ℂ] (X → HomogeneousPoly n) :=
  LinearMap.compLeft (thetaModelEquiv n).symm.toLinearMap X

theorem thetaFun_intertwines (g : RationalGL3) (f : X → HomogeneousPoly n) :
    thetaFun n X (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) X g f) =
      functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual X g (thetaFun n X f) := by
  funext x
  exact theta_intertwines n g _

theorem thetaFunInv_intertwines (g : RationalGL3) (f : X → Module.Dual ℂ (HomogeneousPoly n)) :
    thetaFunInv n X (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual X g f) =
      functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) X g (thetaFunInv n X f) := by
  funext x
  exact thetaInv_intertwines n g _

omit [MulAction RationalGL3 X] in
theorem thetaFunInv_thetaFun (f : X → HomogeneousPoly n) : thetaFunInv n X (thetaFun n X f) = f := by
  funext x
  exact (thetaModelEquiv n).symm_apply_apply (f x)

omit [MulAction RationalGL3 X] in
theorem thetaFun_thetaFunInv (f : X → Module.Dual ℂ (HomogeneousPoly n)) : thetaFun n X (thetaFunInv n X f) = f := by
  funext x
  exact (thetaModelEquiv n).apply_symm_apply (f x)

/-- `Θ` on cocycles with values in functions on `X`. -/
def thetaXCocycles : cocycles rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) X) →ₗ[ℂ]
    cocycles rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual X) :=
  coeffCocycles rationalLevel _ _ (thetaFun n X) (thetaFun_intertwines n X)

def thetaXInvCocycles : cocycles rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual X) →ₗ[ℂ]
    cocycles rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) X) :=
  coeffCocycles rationalLevel _ _ (thetaFunInv n X) (thetaFunInv_intertwines n X)

/-- `Θ` on one-cochains on `X`. -/
def thetaXCochains (k : ℕ) : cochains rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) X) k →ₗ[ℂ]
    cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n trivialCharacter).dual X) k :=
  coeffCochains rationalLevel _ _ (thetaFun n X) (thetaFun_intertwines n X) k

/-- Coefficient change preserves cohomologous cocycles. -/
theorem classOf_coeff {G : Type} [Group G] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Γ : Subgroup G) (ρ1 : Representation ℂ G V) (ρ2 : Representation ℂ G W) (L : V →ₗ[ℂ] W)
    (hL : ∀ g v, L (ρ1 g v) = ρ2 g (L v)) {z₁ z₂ : cocycles Γ ρ1}
    (h : classOf Γ ρ1 z₁ = classOf Γ ρ1 z₂) :
    classOf Γ ρ2 (coeffCocycles Γ ρ1 ρ2 L hL z₁) = classOf Γ ρ2 (coeffCocycles Γ ρ1 ρ2 L hL z₂) := by
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp h)
  apply (Submodule.Quotient.eq _).mpr
  refine LinearMap.mem_range.mpr ⟨coeffCochains Γ ρ1 ρ2 L hL 1 s, ?_⟩
  rw [← coeffCocycles_boundaryMap, hs, map_sub]

end FacePairing

section FacePairingLiteral

variable (n : ℕ)

theorem phi_vec3_inv (a b c : RationalGL3) :
    (fun i => dualInvolution ((![dualInvolution a, dualInvolution b, dualInvolution c] : Fin 3 → RationalGL3) i)) =
      ![a, b, c] := by
  funext i
  fin_cases i <;> simp [dualInvolution_involutive]

/-- **The perfect face pairing `ar:eq:facepair` for the literal dual `E*`**, transported from the target `face_pairing_perfect`
along `thetaModelEquiv` (same pairing: evaluation `E* ⊗ E → ℂ`; classes and cochains with coefficients pushed through `Θ`). -/
theorem face_pairing_perfect_literal :
    ∀ b : StratumH2 n trivialCharacter .line, InnerBoundary n trivialCharacter .line b → b ≠ 0 →
    ∃ ξ'' : StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .line,
      InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .line ξ'' ∧
      ∀ z : MaximalCycles n trivialCharacter .line,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b →
      ∀ w : EdgeCochains n trivialCharacter 1,
        (∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e) →
      ∀ y'' : cocycles rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line),
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) y'' = ξ'' →
      ∀ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
        γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
        (∀ x F, differentialThreeRaw γ x F =
          (y''.val.val ![x 2, x 3, x 4] F) (z.val.val ![x 0, x 1, x 2] F)) →
        ¬ BoundaryExact (fun x e =>
          (y''.val.val ![x 1, x 2, x 3] (endpoint .line e)) (w.val ![x 0, x 1] e) -
            γ x (endpoint .line e)) := by
  intro b hinner hb
  obtain ⟨ξ, hξ, key⟩ := face_pairing_perfect n b hinner hb
  obtain ⟨y0, hy0, u, hu⟩ := hξ
  let ρ := rationalCoefficientComponent n trivialCharacter
  refine ⟨classOf rationalLevel (flagRepresentation ρ.dual .line) (thetaXCocycles n (Flags .line) (toLineStar ρ y0)),
    ⟨thetaXCocycles n (Flags .line) (toLineStar ρ y0), rfl, thetaXCochains n Edges 1 (toEdgeStar ρ u), ?_⟩, ?_⟩
  · intro x e
    have h1 := edgeExact_transport ρ (dualRep ρ) (fun _ => rfl) dualFlag dualFlag_smul
      (endpoint .plane) (endpoint .line) (fun e => (endpoint_plane_dualEdge e).symm) y0 u hu x e
    have e1 : differentialOne rationalLevel (functionRepresentation ρ.dual Edges)
        (thetaXCochains n Edges 1 (toEdgeStar ρ u)) =
        thetaXCochains n Edges 2 (differentialOne rationalLevel (functionRepresentation (dualRep ρ) Edges)
          (toEdgeStar ρ u)) :=
      (coeffCochains_differentialOne rationalLevel _ _ _ _ _).symm
    rw [e1]
    exact congrArg (thetaModel n) h1
  · intro z hz w hw y'' hy'' γ hγ hdγ
    let y : MaximalCycles n trivialCharacter .plane :=
      fromLineStar ρ (thetaXInvCocycles n (Flags .line) y'')
    have hy_val : ∀ (a b c : RationalGL3) (F : Flags .line),
        y.val.val ![dualInvolution a, dualInvolution b, dualInvolution c] (dualFlag F) =
          (thetaModelEquiv n).symm (y''.val.val ![a, b, c] F) := by
      intro a b c F
      change (thetaXInvCocycles n (Flags .line) y'').val.val
          (fun i => dualInvolution ((![dualInvolution a, dualInvolution b, dualInvolution c] : Fin 3 → RationalGL3) i))
          (dualPlaneFlag (dualFlag F)) = _
      rw [phi_vec3_inv, dualPlaneFlag_dualFlag]
      rfl
    have hclass : classOf rationalLevel (flagRepresentation ρ .plane) y = ξ := by
      have h1 : classOf rationalLevel (flagRepresentation (dualRep ρ) .line)
          (thetaXInvCocycles n (Flags .line) y'') =
          classOf rationalLevel (flagRepresentation (dualRep ρ) .line) (toLineStar ρ y0) := by
        have h3 : classOf rationalLevel (flagRepresentation (dualRep ρ) .line)
            (thetaXInvCocycles n (Flags .line) y'') =
            classOf rationalLevel (flagRepresentation (dualRep ρ) .line)
              (thetaXInvCocycles n (Flags .line) (thetaXCocycles n (Flags .line) (toLineStar ρ y0))) :=
          classOf_coeff rationalLevel _ _ (thetaFunInv n (Flags .line))
            (thetaFunInv_intertwines n (Flags .line)) hy''
        have e2 : thetaXInvCocycles n (Flags .line) (thetaXCocycles n (Flags .line) (toLineStar ρ y0)) =
            toLineStar ρ y0 := by
          apply Subtype.ext
          apply Subtype.ext
          funext x F
          exact congrFun (thetaFunInv_thetaFun n (Flags .line) ((toLineStar ρ y0).val.val x)) F
        rw [e2] at h3
        exact h3
      have h4 := classOf_transport (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualPlaneFlag dualPlaneFlag_smul h1
      change classOf rationalLevel (flagRepresentation ρ .plane) (fromLineStar ρ (thetaXInvCocycles n (Flags .line) y'')) =
        classOf rationalLevel (flagRepresentation ρ .plane) (fromLineStar ρ (toLineStar ρ y0)) at h4
      rw [fromLineStar_toLineStar] at h4
      exact h4.trans hy0
    have hk := key z hz w hw y hclass γ hγ (fun x F => by rw [hdγ, hy_val, pairing_literal])
    have hfun : (fun (x : Fin 4 → RationalGL3) (e : Edges) =>
        (dualPairing n) (w.val ![x 0, x 1] e)
          (y.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]
            (dualFlag (endpoint .line e))) - γ x (endpoint .line e)) =
        fun x e => (y''.val.val ![x 1, x 2, x 3] (endpoint .line e)) (w.val ![x 0, x 1] e) -
          γ x (endpoint .line e) := by
      funext x e
      rw [hy_val, pairing_literal]
    rw [hfun] at hk
    exact hk

end FacePairingLiteral

end TernaryPeriodPolynomials.Argument.EisensteinDual
