module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneCanTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.InnerFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjNat
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineInvariance

@[expose] public section


/-!
# Step 1b for the plane faces: frame invariance of the canonical pairing of global classes

Formalized by Claude Sonnet 5.5.

`frameInvariancePlane : FrameInvariancePlane M n hM`: for global classes `c`, `c'` of `Γ(M)` with zero flag restrictions, `q ∈ planeBorel` and `γ ∈ Γ(M)`, the canonical pairing of the plane restrictions at the frame `q h γ` equals that at the frame `h`.
Proof: inner automorphisms of `Γ(M)` act trivially on `H²` (`res_h2Map_inner`), so the restriction at `q h γ` is the transport of the restriction at `h` along the twisted isomorphism `planeFrameEquiv`; `canAtP_transport` (using `cuspConjNat`) compares the pairings.
The orientation signs of the radical (Koszul, `det φ_q = d`) and of the modular curve (cup form, `det A = d`) cancel (`planeFrame_sign`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open CongruenceSubgroup

variable (M n : ℕ) [NeZero M] (hM : 3 ≤ M) (h q γ : SL(3, ℤ)) (hq : q ∈ planeBorel) (hγ : γ ∈ gammaN M)

/-- The coefficient comparison `ρ(γ⁻¹)` between the plane groups of the frames `h` and `q h γ`. -/
def planeT : faceRep M h n ≃ₗ[ℂ] faceRep M (q * h * γ) n := repEquiv (gammaNRepAll M n) ⟨γ, hγ⟩

theorem planeT_hT : ∀ (g : gammaNPAt M (q * h * γ)) (v : faceRep M h n),
    planeT M n h q γ hγ ((faceRep M h n).ρ ((planeFrameEquiv M hM h q γ hq).θ g) v) =
      (faceRep M (q * h * γ) n).ρ g (planeT M n h q γ hγ v) :=
  fun g v => ambRep_conj_apply n γ g.1 v

theorem planeClass_frame (c : groupCohomology.H2 (gammaNRepAll M n)) :
    h2X (planeFrameEquiv M hM h q γ hq) (faceRep M h n) (faceRep M (q * h * γ) n)
      (planeT M n h q γ hγ) (planeT_hT M n hM h q γ hq hγ) (rPlane M n h c) = rPlane M n (q * h * γ) c := by
  rw [h2X_eq_h2Map_plane M hM h q γ hq]
  exact res_h2Map_inner (gammaNRepAll M n) ⟨γ, hγ⟩ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (q * h * γ) hp))
    (planeFrameEquiv M hM h q γ hq).θ.toMonoidHom (fun _ => Subtype.ext rfl) c


theorem planeClassDual_frame (c' : groupCohomology.H2 (gammaNRepAllDual M n)) :
    h2X (planeFrameEquiv M hM h q γ hq) (dualRepG (faceRep M h n)) (dualRepG (faceRep M (q * h * γ) n))
      (dualEquiv (faceRep M h n) (faceRep M (q * h * γ) n) (planeT M n h q γ hγ))
      (planeFrame_hTdual M hM h q γ hq _ _ (planeT M n h q γ hγ) (planeT_hT M n hM h q γ hq hγ))
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M h hp)) (gammaNRepAllDual M n) c') =
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (q * h * γ) hp))
      (gammaNRepAllDual M n) c' := by
  have e := res_h2Map_inner (gammaNRepAllDual M n) ⟨γ, hγ⟩ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (q * h * γ) hp))
    (planeFrameEquiv M hM h q γ hq).θ.toMonoidHom (fun _ => Subtype.ext rfl) c'
  refine Eq.trans ?_ e
  rw [h2X_eq_h2Map_plane M hM h q γ hq]
  exact h2Map_congr rfl _ _ _ _ (LinearMap.ext fun φ => dualEquiv_repEquiv (gammaNRepAll M n) ⟨γ, hγ⟩ φ) _

/-- **Step 1b, planes (literal Stokes at `Γ(M)`).** -/
theorem frameInvariancePlane : FrameInvariancePlane M n hM := by
  intro c hz c' hz' h q γ hq hγ
  unfold canAtClassP
  have e1 : planeClass M (q * h * γ) n hM c hz = ⟨h2X (planeFrameEquiv M hM h q γ hq) (faceRep M h n)
      (faceRep M (q * h * γ) n) (planeT M n h q γ hγ) (planeT_hT M n hM h q γ hq hγ) (planeClass M h n hM c hz).1,
      planeMixed_transport M hM h q γ hq _ _ _ _ _ (planeClass M h n hM c hz).2⟩ :=
    Subtype.ext (planeClass_frame M n hM h q γ hq hγ c).symm
  have e2 : planeClassDual M (q * h * γ) n hM c' hz' = ⟨h2X (planeFrameEquiv M hM h q γ hq) (dualRepG (faceRep M h n))
      (dualRepG (faceRep M (q * h * γ) n)) (dualEquiv _ _ (planeT M n h q γ hγ))
      (planeFrame_hTdual M hM h q γ hq _ _ (planeT M n h q γ hγ) (planeT_hT M n hM h q γ hq hγ))
      (planeClassDual M h n hM c' hz').1,
      planeMixed_transport M hM h q γ hq _ _ _ _ _ (planeClassDual M h n hM c' hz').2⟩ :=
    Subtype.ext (planeClassDual_frame M n hM h q γ hq hγ c').symm
  rw [e1, e2]
  exact canAtP_transport M hM h q γ hq _ _ (planeT M n h q γ hγ) (planeT_hT M n hM h q γ hq hγ) (cuspConjNat M hM) _
    (planeClass M h n hM c hz).2 _ (planeClassDual M h n hM c' hz').2

end TernaryPeriodPolynomials.Argument.FrameInvariance
