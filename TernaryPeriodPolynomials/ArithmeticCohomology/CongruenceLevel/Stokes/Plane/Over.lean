module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MackeyTheta
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Bijection

@[expose] public section


/-!
# The plane data over a face of `Γ(M)`, and the homomorphism `μ : Stab_{S_j}(u'Δ) → Γ(M) ∩ j'.rep⁻¹ P j'.rep`

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3
open MulAction

section PlaneData

variable (M : ℕ) [NeZero M]

/-- The data exhibiting the plane face `i'` of `Γ(M)` over a pair `(i, O)`: a conjugator `(planeFaceRepr i') = q · (planeFaceRepr i) · u'` with `q ∈ P(ℚ) ∩ SL₃(ℤ)` and `u' ∈ Γ(6)` a representative of `O`. -/
structure PlaneOver (i' : PlaneFaces M) where
  i : PlaneFaces 6
  o : orbitRel.Quotient ↥(planeSub i) (↥(gammaN 6) ⧸ Δ6 M)
  q : SL(3, ℤ)
  u : ↥(gammaN 6)
  hq : q ∈ planeBorel
  hrep : (planeFaceRepr i') = q * (planeFaceRepr i) * (u : SL(3, ℤ))
  hu : (u : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o
  hface : planeFaceOver M i o = i'

omit [NeZero M] in
theorem exists_planeOver (h6 : 6 ∣ M) (i' : PlaneFaces M) : Nonempty (PlaneOver M i') := by
  obtain ⟨⟨i, o⟩, hio⟩ := (planeFaceOverEquiv M h6).surjective i'
  have hface : planeFaceOver M i o = i' := hio
  obtain ⟨q, hq, γ, hγ, hr⟩ := PlaneFaces_rel_rep M ((planeFaceRepr i) * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ)))
  have hr' : planeFaceRepr (planeFaceOver M i o) = q * ((planeFaceRepr i) * ((uOPlane M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hr
  rw [hface] at hr'
  refine ⟨⟨i, o, q, uOPlane M i o * ⟨γ, gammaN_mono h6 hγ⟩, hq, ?_, ?_, hface⟩⟩
  · rw [hr']; simp [mul_assoc]
  · have : (uOPlane M i o * ⟨γ, gammaN_mono h6 hγ⟩ : ↥(gammaN 6)) = uOPlane M i o * (⟨γ, gammaN_mono h6 hγ⟩ : ↥(gammaN 6)) := rfl
    rw [this, ← uOPlane_coset M i o]
    rw [QuotientGroup.eq]
    set g : ↥(gammaN 6) := ⟨γ, gammaN_mono h6 hγ⟩ with hg
    have e : (uOPlane M i o * g)⁻¹ * uOPlane M i o = g⁻¹ := by group
    rw [e]
    exact (Δ6 M).inv_mem (show g ∈ Δ6 M from hγ)

end PlaneData

section PlaneMu

variable {M : ℕ} [NeZero M] {i' : PlaneFaces M} (D : PlaneOver M i')

/-- The matrix of an element of the stabilizer. -/
abbrev PlaneOver.sval (s : StabS (Δ6 M) (planeSub D.i) D.u) : SL(3, ℤ) := (((s : ↥(planeSub D.i)) : ↥(gammaN 6)) : SL(3, ℤ))

omit [NeZero M] in
theorem PlaneOver.conj_mem_gammaN (s : StabS (Δ6 M) (planeSub D.i) D.u) :
    (D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ)) ∈ gammaN M := by
  have h1 := (mem_stabilizer_quot_iff (Δ6 M) (planeSub D.i) D.u (s : ↥(planeSub D.i))).mp s.2
  exact h1

omit [NeZero M] in
theorem PlaneOver.mem_Q (s : StabS (Δ6 M) (planeSub D.i) D.u) :
    (D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ)) ∈ gammaNPAt M (planeFaceRepr i') := by
  have hS : (planeFaceRepr D.i) * D.sval s * (planeFaceRepr D.i)⁻¹ ∈ gammaNP 6 := (s : ↥(planeSub D.i)).2
  have hX : (planeFaceRepr D.i) * D.sval s * (planeFaceRepr D.i)⁻¹ ∈ gammaNP M := by
    refine ⟨?_, hS.2⟩
    have := (gammaN_normal M).conj_mem _ (D.conj_mem_gammaN s) ((planeFaceRepr D.i) * (D.u : SL(3, ℤ)))
    have e : (planeFaceRepr D.i) * (D.u : SL(3, ℤ)) * ((D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ))) *
        ((planeFaceRepr D.i) * (D.u : SL(3, ℤ)))⁻¹ = (planeFaceRepr D.i) * D.sval s * (planeFaceRepr D.i)⁻¹ := by group
    rw [e] at this
    exact this
  have := conj_mem_gammaNP M D.hq hX
  show (planeFaceRepr i') * ((D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ))) * (planeFaceRepr i')⁻¹ ∈ gammaNP M
  have e : (planeFaceRepr i') * ((D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ))) * (planeFaceRepr i')⁻¹ =
      D.q * ((planeFaceRepr D.i) * D.sval s * (planeFaceRepr D.i)⁻¹) * D.q⁻¹ := by rw [D.hrep]; group
  rw [e]; exact this

/-- **The homomorphism `μ : Stab_{S_i}(u'Δ) → Γ(M) ∩ (planeFaceRepr i')⁻¹ Q (planeFaceRepr i')`**, `s ↦ u'⁻¹ s u'`. -/
def PlaneOver.mu : StabS (Δ6 M) (planeSub D.i) D.u →* ↥(gammaNPAt M (planeFaceRepr i')) where
  toFun s := ⟨(D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ)), D.mem_Q s⟩
  map_one' := by apply Subtype.ext; simp [PlaneOver.sval]
  map_mul' a b := by apply Subtype.ext; simp [PlaneOver.sval, mul_assoc]

end PlaneMu

section PlaneTheta

variable {M : ℕ} [NeZero M] {i' : PlaneFaces M} (D : PlaneOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

/-- The coefficient module of the line group `Γ_{Q'}` obtained from `ρM`. -/
abbrev planeW (i' : PlaneFaces M) (ρM : Representation ℂ ↥(gammaN M) E) : Rep ℂ ↥(gammaNPAt M (planeFaceRepr i')) :=
  Rep.res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN M (planeFaceRepr i') hp)) (Rep.of ρM)

omit [NeZero M] in
include hρ in
theorem PlaneOver.hTgen (s : StabS (Δ6 M) (planeSub D.i) D.u) (w : E) :
    ρ (D.u : ↥(gammaN 6)) ((planeW i' ρM).ρ (D.mu s) w) = ρ (((s : ↥(planeSub D.i)) : ↥(gammaN 6))) (ρ (D.u : ↥(gammaN 6)) w) := by
  have e : (planeW i' ρM).ρ (D.mu s) w = ρ (D.u⁻¹ * ((s : ↥(planeSub D.i)) : ↥(gammaN 6)) * D.u) w := by
    have := hρ ⟨(D.u⁻¹ * ((s : ↥(planeSub D.i)) : ↥(gammaN 6)) * D.u : ↥(gammaN 6)),
      (mem_stabilizer_quot_iff (Δ6 M) (planeSub D.i) D.u (s : ↥(planeSub D.i))).mp s.2⟩
    exact congrArg (fun f => f w) this
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- **The transport `Θ`** of the line classes of `Γ(M)` at `i'` with coefficients `ρM` to the `e_O`-component of the induced module `Fun(Γ(6)/Γ(M), E)`. -/
def PlaneOver.thetaGen : groupCohomology.H2 (planeW i' ρM) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res (planeSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)))) :=
  Theta ρ (Δ6 M) (planeSub D.i) D.u (planeW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)

end PlaneTheta

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
