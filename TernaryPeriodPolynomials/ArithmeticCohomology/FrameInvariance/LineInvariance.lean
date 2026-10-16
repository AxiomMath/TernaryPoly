module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineCanTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.InnerFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjNat

@[expose] public section


/-!
# Step 1b for the line faces: frame invariance of the canonical pairing of global classes

Formalized by Claude Sonnet 5.5.

`frameInvarianceLine : FrameInvarianceLine M n hM`: for global classes `c`, `c'` of `Γ(M)` with zero flag restrictions, `q ∈ lineBorel` and `γ ∈ Γ(M)`, the canonical pairing of the line restrictions at the frame `q h γ` equals that at the frame `h`.
Proof: inner automorphisms of `Γ(M)` act trivially on `H²` (`res_h2Map_inner`), so the restriction at `q h γ` is the transport of the restriction at `h` along the twisted isomorphism `lineFrameEquiv`; `canAt_transport` (using `cuspConjNat`) compares the pairings.
The orientation signs of the radical (Koszul, `det φ_q = a`) and of the modular curve (cup form, `det A = a`) cancel (`lineFrame_sign`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open CongruenceSubgroup

variable (M n : ℕ) [NeZero M] (hM : 3 ≤ M) (h q γ : SL(3, ℤ)) (hq : q ∈ lineBorel) (hγ : γ ∈ gammaN M)

/-- The coefficient comparison `ρ(γ⁻¹)` between the line groups of the frames `h` and `q h γ`. -/
def lineT : lineFaceRep M h n ≃ₗ[ℂ] lineFaceRep M (q * h * γ) n := repEquiv (gammaNRepAll M n) ⟨γ, hγ⟩

theorem ambRep_conj_apply (γ g : SL(3, ℤ)) (v : GeneralEisenstein.HomogeneousPoly n) :
    ambRep n γ⁻¹ (ambRep n (γ * g * γ⁻¹) v) = ambRep n g (ambRep n γ⁻¹ v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

theorem lineT_hT : ∀ (g : gammaNQAt M (q * h * γ)) (v : lineFaceRep M h n),
    lineT M n h q γ hγ ((lineFaceRep M h n).ρ ((lineFrameEquiv M hM h q γ hq).θ g) v) =
      (lineFaceRep M (q * h * γ) n).ρ g (lineT M n h q γ hγ v) :=
  fun g v => ambRep_conj_apply n γ g.1 v

theorem lineClass_frame (c : groupCohomology.H2 (gammaNRepAll M n)) :
    h2X (lineFrameEquiv M hM h q γ hq) (lineFaceRep M h n) (lineFaceRep M (q * h * γ) n)
      (lineT M n h q γ hγ) (lineT_hT M n hM h q γ hq hγ) (rLine M n h c) = rLine M n (q * h * γ) c := by
  rw [h2X_eq_h2Map M hM h q γ hq]
  exact res_h2Map_inner (gammaNRepAll M n) ⟨γ, hγ⟩ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M (q * h * γ) hp))
    (lineFrameEquiv M hM h q γ hq).θ.toMonoidHom (fun _ => Subtype.ext rfl) c


theorem dualEquiv_repEquiv {G : Type} [Group G] (A : Rep ℂ G) (g : G) (φ : Module.Dual ℂ A) :
    dualEquiv A A (repEquiv A g) φ = (dualRepG A).ρ g⁻¹ φ := by
  ext v
  rw [dualEquiv_apply, dualRepG_inv]
  simp only [inv_inv]
  rfl

theorem lineClassDual_frame (c' : groupCohomology.H2 (gammaNRepAllDual M n)) :
    h2X (lineFrameEquiv M hM h q γ hq) (dualRepG (lineFaceRep M h n)) (dualRepG (lineFaceRep M (q * h * γ) n))
      (dualEquiv (lineFaceRep M h n) (lineFaceRep M (q * h * γ) n) (lineT M n h q γ hγ))
      (lineFrame_hTdual M hM h q γ hq _ _ (lineT M n h q γ hγ) (lineT_hT M n hM h q γ hq hγ))
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M h hp)) (gammaNRepAllDual M n) c') =
    twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M (q * h * γ) hp))
      (gammaNRepAllDual M n) c' := by
  have e := res_h2Map_inner (gammaNRepAllDual M n) ⟨γ, hγ⟩ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M h hp))
    (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M (q * h * γ) hp))
    (lineFrameEquiv M hM h q γ hq).θ.toMonoidHom (fun _ => Subtype.ext rfl) c'
  refine Eq.trans ?_ e
  rw [h2X_eq_h2Map M hM h q γ hq]
  exact h2Map_congr rfl _ _ _ _ (LinearMap.ext fun φ => dualEquiv_repEquiv (gammaNRepAll M n) ⟨γ, hγ⟩ φ) _

/-- **Step 1b, lines (literal Stokes at `Γ(M)`).** -/
theorem frameInvarianceLine : FrameInvarianceLine M n hM := by
  intro c hz c' hz' h q γ hq hγ
  unfold canAtClass
  have e1 : lineClass M (q * h * γ) n hM c hz = ⟨h2X (lineFrameEquiv M hM h q γ hq) (lineFaceRep M h n)
      (lineFaceRep M (q * h * γ) n) (lineT M n h q γ hγ) (lineT_hT M n hM h q γ hq hγ) (lineClass M h n hM c hz).1,
      lineMixed_transport M hM h q γ hq _ _ _ _ _ (lineClass M h n hM c hz).2⟩ :=
    Subtype.ext (lineClass_frame M n hM h q γ hq hγ c).symm
  have e2 : lineClassDual M (q * h * γ) n hM c' hz' = ⟨h2X (lineFrameEquiv M hM h q γ hq) (dualRepG (lineFaceRep M h n))
      (dualRepG (lineFaceRep M (q * h * γ) n)) (dualEquiv _ _ (lineT M n h q γ hγ))
      (lineFrame_hTdual M hM h q γ hq _ _ (lineT M n h q γ hγ) (lineT_hT M n hM h q γ hq hγ))
      (lineClassDual M h n hM c' hz').1,
      lineMixed_transport M hM h q γ hq _ _ _ _ _ (lineClassDual M h n hM c' hz').2⟩ :=
    Subtype.ext (lineClassDual_frame M n hM h q γ hq hγ c').symm
  rw [e1, e2]
  exact canAt_transport M hM h q γ hq _ _ (lineT M n h q γ hγ) (lineT_hT M n hM h q γ hq hγ) (cuspConjNat M hM) _
    (lineClass M h n hM c hz).2 _ (lineClassDual M h n hM c' hz').2

end TernaryPeriodPolynomials.Argument.FrameInvariance
