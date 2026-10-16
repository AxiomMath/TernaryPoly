module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Cone.Factorisation

@[expose] public section


/-!
# The diagonal terms of the Stokes sum of the induced module, and the statements of Steps 1 and 2

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open MulAction

section Terms

variable (M n : ℕ) [NeZero M]

/-- A coset representative `u_O ∈ Γ(6)` of the orbit `O` of the line group `S_i` on `Γ(6)/Γ(M)`. -/
def uOLine (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) : ↥(gammaN 6) :=
  Quotient.out (Quotient.out o : ↥(gammaN 6) ⧸ Δ6 M)

/-- A coset representative `u_O ∈ Γ(6)` of the orbit `O` of the plane group `S_i` on `Γ(6)/Γ(M)`. -/
def uOPlane (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) : ↥(gammaN 6) :=
  Quotient.out (Quotient.out o : ↥(gammaN 6) ⧸ Δ6 M)

end Terms


section Terms2

variable {M n : ℕ} [NeZero M]

instance permFD : FiniteDimensional ℂ (↥(gammaN 6) ⧸ Δ6 M → GeneralEisenstein.HomogeneousPoly n) :=
  haveI : FiniteDimensional ℂ (GeneralEisenstein.HomogeneousPoly n) := TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.homogeneousPoly_finite n
  Module.Finite.pi

/-- The flag-vanishing hypothesis at level `M` for a class of `H²(Γ(M), ρM)`. -/
abbrev ZeroFlagsRep {V : Type} [AddCommGroup V] [Module ℂ V] (ρM : Representation ℂ ↥(gammaN M) V)
    (c : groupCohomology.H2 (Rep.of ρM)) : Prop :=
  ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (gammaNBAt_le_gammaN M g)) (Rep.of ρM) c = 0

/-- The mixed class `h2E e_O (res_i c_V)` of the line face `i`, for an induced class `c_V` of a class `c₀` of `H²(Γ(M), E_n)` with zero flag restrictions. -/
def lineTermX (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    lineMixedSub (permRep (rhoEn n) (Δ6 M)) i :=
  ⟨h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep (rhoEn n) (Δ6 M))))
      (eO (Δ6 M) (lineSub i) o) (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) i o k v)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep (rhoEn n) (Δ6 M))) cV),
    lineMixedSub_h2E _ i _ (fun k v => eO_line_equivariant (rhoEn n) (Δ6 M) i o k v) _
      (lineMixedSub_of_zeroFlags _ i cV (res_flag_ind_zero M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ hz cV hcV))⟩

/-- The mixed class `h2E e_Oᵀ (res_i c'_V)` of the line face `i` for the dual coefficients. -/
def lineTermY (c₀' : groupCohomology.H2 (gammaNRepAllDual M n)) (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀')
    (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    lineMixedSub (permRep (rhoEn n) (Δ6 M)).dual i :=
  ⟨h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual))
      (eO (Δ6 M) (lineSub i) o).dualMap
      (fun k v => lineHeD (permRep (rhoEn n) (Δ6 M)) i (eO (Δ6 M) (lineSub i) o) (eO_line_equivariant (rhoEn n) (Δ6 M) i o) k v)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
        (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd)),
    lineMixedSub_h2E_dual (permRep (rhoEn n) (Δ6 M)) i (eO (Δ6 M) (lineSub i) o) (eO_line_equivariant (rhoEn n) (Δ6 M) i o) _
      (lineMixedSub_of_zeroFlags (permRep (rhoEn n) (Δ6 M)).dual i _
        (fun g => res_h2Hom_zero _ (dualRepHom (rhoEn n) (Δ6 M)) cVd
          (res_flag_ind_zero M (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
            c₀' hz' cVd hcVd g)))⟩

/-- The mixed class `h2E e_O (res_i c_V)` of the plane face `i`. -/
def planeTermX (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀)
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    planeMixedSub (permRep (rhoEn n) (Δ6 M)) i :=
  ⟨h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep (rhoEn n) (Δ6 M))))
      (eO (Δ6 M) (planeSub i) o) (fun k v => eO_plane_equivariant (rhoEn n) (Δ6 M) i o k v)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep (rhoEn n) (Δ6 M))) cV),
    planeMixedSub_h2E _ i _ (fun k v => eO_plane_equivariant (rhoEn n) (Δ6 M) i o k v) _
      (planeMixedSub_of_zeroFlags _ i cV (res_flag_ind_zero M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀ hz cV hcV))⟩

/-- The mixed class `h2E e_Oᵀ (res_i c'_V)` of the plane face `i` for the dual coefficients. -/
def planeTermY (c₀' : groupCohomology.H2 (gammaNRepAllDual M n)) (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀')
    (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)) :
    planeMixedSub (permRep (rhoEn n) (Δ6 M)).dual i :=
  ⟨h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of (permRep (rhoEn n) (Δ6 M)).dual))
      (eO (Δ6 M) (planeSub i) o).dualMap
      (fun k v => planeHeD (permRep (rhoEn n) (Δ6 M)) i (eO (Δ6 M) (planeSub i) o) (eO_plane_equivariant (rhoEn n) (Δ6 M) i o) k v)
      (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
        (Rep.of (permRep (rhoEn n) (Δ6 M)).dual) (h2Hom (dualRepHom (rhoEn n) (Δ6 M)) cVd)),
    planeMixedSub_h2E_dual (permRep (rhoEn n) (Δ6 M)) i (eO (Δ6 M) (planeSub i) o) (eO_plane_equivariant (rhoEn n) (Δ6 M) i o) _
      (planeMixedSub_of_zeroFlags (permRep (rhoEn n) (Δ6 M)).dual i _
        (fun g => res_h2Hom_zero _ (dualRepHom (rhoEn n) (Δ6 M)) cVd
          (res_flag_ind_zero M (rhoEn n).dual (gammaNRepAll M n).ρ.dual (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl))
            c₀' hz' cVd hcVd g)))⟩

end Terms2

section Steps

variable (M n : ℕ) [NeZero M] (hM : 3 ≤ M)

/-- **Step 1b (frame change within a line face; uses S2's `cuspidal_pairing_gammaN_unique`).**  The canonical pairing of the line restrictions of global classes `c`, `c'` of `Γ(M)`
with zero flag restrictions does not depend on the conjugator within the face: for `q ∈ Q(ℚ) ∩ SL₃(ℤ)` and `γ ∈ Γ(M)` the pairing at the frame `q h γ` is the pairing at the frame `h`. -/
def FrameInvarianceLine : Prop :=
  ∀ (c : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c) (c' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c') (h q γ : SL(3, ℤ)), q ∈ lineBorel → γ ∈ gammaN M →
      canAtClass M (q * h * γ) n hM c hz c' hz' = canAtClass M h n hM c hz c' hz'

/-- **Step 1b for the plane faces.** -/
def FrameInvariancePlane : Prop :=
  ∀ (c : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c) (c' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c') (h q γ : SL(3, ℤ)), q ∈ planeBorel → γ ∈ gammaN M →
      canAtClassP M (q * h * γ) n hM c hz c' hz' = canAtClassP M h n hM c hz c' hz'

/-- **Step 1 (frame change)**: line and plane faces.  The bijection of Step 1a is `lineFaceOverEquiv`, `planeFaceOverEquiv` (proved). -/
def Step1 : Prop := FrameInvarianceLine M n hM ∧ FrameInvariancePlane M n hM

/-- **Step 2 (compatibility of the canonical pairing with finite-index induction, with the Mackey identification of the orbit components; lines).**  Let `c₀ ∈ H²(Γ(M), E_n)`, `c₀' ∈ H²(Γ(M), E_n^*)`
have zero flag restrictions and let `c_V`, `c'_V` be classes of the induced modules `Fun(Γ(6)/Γ(M), E_n)`, `Fun(Γ(6)/Γ(M), E_n^*)` whose Shapiro coordinates are the transports of `c₀`, `c₀'`.  For a line face `i`
of `Γ(6)` and an orbit `O` of its line group on `Γ(6)/Γ(M)` (with representative `u_O`), the level-6 canonical pairing `can6` (S2's `facePairingCan` on the Hochschild-Serre edges) of the orbit components
`h2E e_O (res_i c_V)`, `h2E e_Oᵀ (res_i c'_V)` equals the level-`M` canonical pairing, at the frame `h_i u_O`, of the restrictions of `c₀`, `c₀'`. -/
def OrbitIdentLine : Prop :=
  ∀ (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀')
    (i : LineFaces 6) (o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)),
      can6 (permRep (rhoEn n) (Δ6 M)) i (lineTermX c₀ hz cV hcV i o) (lineTermY c₀' hz' cVd hcVd i o) =
        canAtClass M (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀ hz c₀' hz'

/-- **Step 2 for the plane faces.** -/
def OrbitIdentPlane : Prop :=
  ∀ (c₀ : groupCohomology.H2 (gammaNRepAll M n)) (hz : ZeroFlags M n c₀) (c₀' : groupCohomology.H2 (gammaNRepAllDual M n))
    (hz' : ZeroFlagsRep (gammaNRepAll M n).ρ.dual c₀')
    (cV : groupCohomology.H2 (Rep.of (permRep (rhoEn n) (Δ6 M))))
    (cVd : groupCohomology.H2 (Rep.of (permRep (rhoEn n).dual (Δ6 M))))
    (hcV : PhiH (rhoEn n) (Δ6 M) cV = transportΔ M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl) c₀)
    (hcVd : PhiH (rhoEn n).dual (Δ6 M) cVd = transportΔ M (rhoEn n).dual (gammaNRepAll M n).ρ.dual
      (hρ_dual M (rhoEn n) (gammaNRepAll M n).ρ (fun _ => rfl)) c₀')
    (i : PlaneFaces 6) (o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)),
      can6P (permRep (rhoEn n) (Δ6 M)) i (planeTermX c₀ hz cV hcV i o) (planeTermY c₀' hz' cVd hcVd i o) =
        canAtClassP M (planeFaceRepr i * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) n hM c₀ hz c₀' hz'

/-- **Step 2**: line and plane faces. -/
def Step2 : Prop := OrbitIdentLine M n hM ∧ OrbitIdentPlane M n hM

end Steps

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
