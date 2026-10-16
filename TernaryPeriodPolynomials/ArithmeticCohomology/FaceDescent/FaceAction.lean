module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CanonicalTwist
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.PullbackComp
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceCharacters

@[expose] public section


/-!
# A group acting on a face of `Γ(N)` and on its cuspidal groups

Formalized by Claude Sonnet 5.5.

`FaceAction hN ext ρ G`: a group `G` (the finite covering group of the face) acts on the split-extension data `ℤ² → E → Γ(N)` by automorphisms `θ g` of `E` inducing `φ g` on the radical lattice and `α g` on the Levi `Γ(N)`, the latter being conjugation
by `A g ∈ GL₂(ℤ)` (determinant and reflection elements included), and on the coefficient module by `T g` with `T g (ρ e v) = ρ (θ g e) (T g v)`.
Its elements give the self-twists `FaceAction.twist g` of the `TwistEquiv` (the pullback along `g⁻¹`), whence the transports `leviAct g` of the Levi module `H¹(N, ρ)` and `cuspAct g` of the cuspidal group `𝒞(H¹(N, ρ))` (`cuspXi`),
and for the contragredient `cuspActDual g`.  `cuspRep`, `cuspRepDual` are representations of `G` (functoriality of the transports, `oneCocyclePullbackH1_comp`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPoly.RankTwoAugmentedFrames

/-- **A group acting on the face data** (extension, coefficient module, Levi `GL₂(ℤ)`-conjugation). -/
structure FaceAction {N : ℕ} (hN : 3 ≤ N) {E : Type} [Group E] (ext : GroupExtension RadicalLattice E (Gamma N)) (ρ : Rep ℂ E)
    (G : Type) [Group G] where
  θ : G →* MulAut E
  φ : G →* MulAut RadicalLattice
  α : G →* MulAut (Gamma N)
  A : G →* IntegralGL
  T : G → (ρ ≃ₗ[ℂ] ρ)
  T_one : ∀ v, T 1 v = v
  T_mul : ∀ g h v, T (g * h) v = T g (T h v)
  inl_comm : ∀ g r, θ g (ext.inl r) = ext.inl (φ g r)
  rightHom_comm : ∀ g e, ext.rightHom (θ g e) = α g (ext.rightHom e)
  hT : ∀ g e v, T g (ρ.ρ e v) = ρ.ρ (θ g e) (T g v)
  hA : ∀ g l, ((gammaEquiv hN (α g l) : gammaNGL N) : IntegralGL) = A g * (gammaEquiv hN l : gammaNGL N) * (A g)⁻¹

variable {N : ℕ} {hN : 3 ≤ N} {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)} {ρ : Rep ℂ E}
  {G : Type} [Group G] (F : FaceAction hN ext ρ G)

/-- The self-twist of the extension attached to `g` (pullback along `g⁻¹`). -/
def FaceAction.twist (g : G) : TwistEquiv ext ext where
  θ := (F.θ g)⁻¹
  φ := (F.φ g)⁻¹
  α := (F.α g)⁻¹
  inl_comm r := by
    show (F.θ g).symm (ext.inl r) = ext.inl ((F.φ g).symm r)
    rw [MulEquiv.symm_apply_eq, F.inl_comm, MulEquiv.apply_symm_apply]
  rightHom_comm e := by
    show ext.rightHom ((F.θ g).symm e) = (F.α g).symm (ext.rightHom e)
    rw [MulEquiv.eq_symm_apply, ← F.rightHom_comm, MulEquiv.apply_symm_apply]

theorem FaceAction.hTtw (g : G) (g' : E) (v : ρ) :
    F.T g (ρ.ρ ((F.twist g).θ g') v) = ρ.ρ g' (F.T g v) := by
  have := F.hT g ((F.θ g).symm g') v
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem FaceAction.hAtw (g : G) : GLConj hN (F.twist g).α (F.A g)⁻¹ := by
  intro l
  have h := F.hA g ((F.α g).symm l)
  rw [MulEquiv.apply_symm_apply] at h
  change ((gammaEquiv hN ((F.α g).symm l) : gammaNGL N) : IntegralGL) = (F.A g)⁻¹ * (gammaEquiv hN l : gammaNGL N) * ((F.A g)⁻¹)⁻¹
  rw [h]
  group

section Actions

variable (s : ext.Splitting)

/-- The transport of the Levi module `H¹(N, ρ)` by `g`. -/
def FaceAction.leviAct (g : G) : splitRadicalH1Representation s ρ →ₗ[ℂ] splitRadicalH1Representation s ρ :=
  TernaryPeriodPolynomials.Argument.FrameInvariance.leviMap (F.twist g) s s ρ ρ (F.T g) (F.hTtw g)

theorem FaceAction.leviAct_equiv (g : G) (l : Gamma N) (v : splitRadicalH1Representation s ρ) :
    F.leviAct s g ((splitRadicalH1Representation s ρ).ρ ((F.twist g).α l) v) =
      (splitRadicalH1Representation s ρ).ρ l (F.leviAct s g v) :=
  TernaryPeriodPolynomials.Argument.FrameInvariance.leviMap_equiv (F.twist g) s s ρ ρ (F.T g) (F.hTtw g) l v

theorem FaceAction.radXi_one (x : groupCohomology.H1 (Rep.res ext.inl ρ)) :
    radXi (F.twist 1) ρ ρ (F.T 1) (F.hTtw 1) x = x :=
  oneCocyclePullbackH1_of_id (A₁ := Rep.res ext.inl ρ) _ _ _ (fun r => by simp [FaceAction.twist]) (fun v => F.T_one v) x

theorem FaceAction.radXi_mul (g h : G) (x : groupCohomology.H1 (Rep.res ext.inl ρ)) :
    radXi (F.twist (g * h)) ρ ρ (F.T (g * h)) (F.hTtw (g * h)) x =
      radXi (F.twist g) ρ ρ (F.T g) (F.hTtw g) (radXi (F.twist h) ρ ρ (F.T h) (F.hTtw h) x) := by
  have hψ : ∀ r, (F.twist h).φ.toMonoidHom ((F.twist g).φ.toMonoidHom r) = (F.twist (g * h)).φ.toMonoidHom r := by
    intro r
    simp [FaceAction.twist, mul_inv_rev]
  have := oneCocyclePullbackH1_comp (A₁ := Rep.res ext.inl ρ) (A₂ := Rep.res ext.inl ρ) (A₃ := Rep.res ext.inl ρ)
    (F.twist h).φ.toMonoidHom (F.T h).toLinearMap (radInter (F.twist h) ρ ρ (F.T h) (F.hTtw h))
    (F.twist g).φ.toMonoidHom (F.T g).toLinearMap (radInter (F.twist g) ρ ρ (F.T g) (F.hTtw g))
    (F.twist (g * h)).φ.toMonoidHom (F.T (g * h)).toLinearMap (radInter (F.twist (g * h)) ρ ρ (F.T (g * h)) (F.hTtw (g * h)))
    hψ (fun v => (F.T_mul g h v).symm) x
  exact this.symm

theorem FaceAction.leviAct_one (v : splitRadicalH1Representation s ρ) : F.leviAct s 1 v = v := F.radXi_one v

theorem FaceAction.leviAct_mul (g h : G) (v : splitRadicalH1Representation s ρ) :
    F.leviAct s (g * h) v = F.leviAct s g (F.leviAct s h v) := F.radXi_mul g h v

/-- **The transport of the cuspidal group `𝒞(H¹(N, ρ))` by `g`** (`S5`'s `cuspXi` along the self-twist). -/
def FaceAction.cuspAct (g : G) : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ) →ₗ[ℂ]
    cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ) :=
  TernaryPeriodPolynomials.Argument.FrameInvariance.cuspXi hN (F.twist g).α (F.A g)⁻¹ (F.hAtw g) _ _ (F.leviAct s g) (F.leviAct_equiv s g)

theorem FaceAction.cuspAct_val (g : G) (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) :
    ((F.cuspAct s g x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) :
      groupCohomology.H1 (splitRadicalH1Representation s ρ)) =
      oneCocyclePullbackH1 (splitRadicalH1Representation s ρ) (splitRadicalH1Representation s ρ) (F.twist g).α.toMonoidHom
        (F.leviAct s g) (cuspInter (F.twist g).α _ _ (F.leviAct s g) (F.leviAct_equiv s g)) x.1 := rfl

theorem FaceAction.cuspAct_one (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) : F.cuspAct s 1 x = x := by
  apply Subtype.ext
  rw [FaceAction.cuspAct_val]
  exact oneCocyclePullbackH1_of_id _ _ _ (fun l => by simp [FaceAction.twist]) (F.leviAct_one s) x.1

theorem FaceAction.cuspAct_mul (g h : G) (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) :
    F.cuspAct s (g * h) x = F.cuspAct s g (F.cuspAct s h x) := by
  apply Subtype.ext
  rw [FaceAction.cuspAct_val, FaceAction.cuspAct_val, FaceAction.cuspAct_val]
  exact (oneCocyclePullbackH1_comp _ _ _ _ _ _ _ _ _ (fun l => by simp [FaceAction.twist, mul_inv_rev])
    (fun v => (F.leviAct_mul s g h v).symm) x.1).symm

/-- **The representation of the covering group on the cuspidal group `𝒞(H¹(N, ρ))`.** -/
def FaceAction.cuspRep : Representation ℂ G (cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) where
  toFun := F.cuspAct s
  map_one' := LinearMap.ext (F.cuspAct_one s)
  map_mul' g h := LinearMap.ext (F.cuspAct_mul s g h)

end Actions

section Dual

/-- The action on the contragredient coefficient module. -/
def FaceAction.dual : FaceAction hN ext (dualRepG ρ) G where
  θ := F.θ
  φ := F.φ
  α := F.α
  A := F.A
  T g := dualEquiv ρ ρ (F.T g)
  T_one φ := by
    apply LinearMap.ext
    intro v
    rw [dualEquiv_apply]
    show φ ((F.T 1).symm v) = φ v
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    exact (F.T_one v).symm
  T_mul g h φ := by
    apply LinearMap.ext
    intro v
    rw [dualEquiv_apply]
    show φ ((F.T (g * h)).symm v) = (dualEquiv ρ ρ (F.T g)) ((dualEquiv ρ ρ (F.T h)) φ) v
    rw [dualEquiv_apply, dualEquiv_apply]
    congr 1
    rw [LinearEquiv.symm_apply_eq, F.T_mul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  inl_comm := F.inl_comm
  rightHom_comm := F.rightHom_comm
  hT g e φ := by
    have := hTdual (F.twist g) ρ ρ (F.T g) (F.hTtw g) (F.θ g e) φ
    simp only [FaceAction.twist] at this
    rw [show ((F.θ g)⁻¹ : MulAut E) (F.θ g e) = e by simp] at this
    exact this
  hA := F.hA

end Dual

section Invariants

variable (s : ext.Splitting)

/-- The `G`-invariants of the cuspidal group. -/
def FaceAction.invariants : Submodule ℂ (cuspidalSubspace (Gamma N) (splitRadicalH1Representation s ρ)) where
  carrier := {x | ∀ g, F.cuspRep s g x = x}
  add_mem' ha hb g := by simp [map_add, ha g, hb g]
  zero_mem' g := by simp
  smul_mem' c x hx g := by simp [map_smul, hx g]

/-- The `G`-invariants of the cuspidal group of the contragredient. -/
def FaceAction.invariantsDual : Submodule ℂ (cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG ρ))) where
  carrier := {x | ∀ g, F.dual.cuspRep s g x = x}
  add_mem' ha hb g := by simp [map_add, ha g, hb g]
  zero_mem' g := by simp
  smul_mem' c x hx g := by simp [map_smul, hx g]

end Invariants

end TernaryPeriodPolynomials.Argument.FaceDescent
