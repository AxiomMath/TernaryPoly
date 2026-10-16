module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Corr
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Bijection

@[expose] public section


/-!
# The line data over a face of `Γ(M)`, and the homomorphism `μ : Stab_{S_i}(u'Δ) → Γ(M) ∩ i'.rep⁻¹ Q i'.rep`

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

section LineData

variable (M : ℕ) [NeZero M]

/-- The data exhibiting the line face `i'` of `Γ(M)` over a pair `(i, O)`: a conjugator `i'.rep = q · i.rep · u'` with `q ∈ Q(ℚ) ∩ SL₃(ℤ)` and `u' ∈ Γ(6)` a representative of `O`. -/
structure LineOver (i' : LineFaces M) where
  i : LineFaces 6
  o : orbitRel.Quotient ↥(lineSub i) (↥(gammaN 6) ⧸ Δ6 M)
  q : SL(3, ℤ)
  u : ↥(gammaN 6)
  hq : q ∈ lineBorel
  hrep : i'.rep = q * i.rep * (u : SL(3, ℤ))
  hu : (u : ↥(gammaN 6) ⧸ Δ6 M) = Quotient.out o
  hface : lineFaceOver M i o = i'

omit [NeZero M] in
theorem exists_lineOver (h6 : 6 ∣ M) (i' : LineFaces M) : Nonempty (LineOver M i') := by
  obtain ⟨⟨i, o⟩, hio⟩ := (lineFaceOverEquiv M h6).surjective i'
  have hface : lineFaceOver M i o = i' := hio
  obtain ⟨q, hq, γ, hγ, hr⟩ := LineFaces.rel_rep (N := M) (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ)))
  have hr' : (lineFaceOver M i o).rep = q * (i.rep * ((uOLine M i o : ↥(gammaN 6)) : SL(3, ℤ))) * γ := hr
  rw [hface] at hr'
  refine ⟨⟨i, o, q, uOLine M i o * ⟨γ, gammaN_mono h6 hγ⟩, hq, ?_, ?_, hface⟩⟩
  · rw [hr']; simp [mul_assoc]
  · have : (uOLine M i o * ⟨γ, gammaN_mono h6 hγ⟩ : ↥(gammaN 6)) = uOLine M i o * (⟨γ, gammaN_mono h6 hγ⟩ : ↥(gammaN 6)) := rfl
    rw [this, ← uOLine_coset M i o]
    rw [QuotientGroup.eq]
    set g : ↥(gammaN 6) := ⟨γ, gammaN_mono h6 hγ⟩ with hg
    have e : (uOLine M i o * g)⁻¹ * uOLine M i o = g⁻¹ := by group
    rw [e]
    exact (Δ6 M).inv_mem (show g ∈ Δ6 M from hγ)

end LineData

section LineMu

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i')

/-- The matrix of an element of the stabilizer. -/
abbrev LineOver.sval (s : StabS (Δ6 M) (lineSub D.i) D.u) : SL(3, ℤ) := (((s : ↥(lineSub D.i)) : ↥(gammaN 6)) : SL(3, ℤ))

omit [NeZero M] in
theorem LineOver.conj_mem_gammaN (s : StabS (Δ6 M) (lineSub D.i) D.u) :
    (D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ)) ∈ gammaN M := by
  have h1 := (mem_stabilizer_quot_iff (Δ6 M) (lineSub D.i) D.u (s : ↥(lineSub D.i))).mp s.2
  exact h1

omit [NeZero M] in
theorem LineOver.mem_Q (s : StabS (Δ6 M) (lineSub D.i) D.u) :
    (D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ)) ∈ gammaNQAt M i'.rep := by
  have hS : D.i.rep * D.sval s * D.i.rep⁻¹ ∈ gammaNQ 6 := (s : ↥(lineSub D.i)).2
  have hX : D.i.rep * D.sval s * D.i.rep⁻¹ ∈ gammaNQ M := by
    refine ⟨?_, hS.2⟩
    have := (gammaN_normal M).conj_mem _ (D.conj_mem_gammaN s) (D.i.rep * (D.u : SL(3, ℤ)))
    have e : D.i.rep * (D.u : SL(3, ℤ)) * ((D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ))) *
        (D.i.rep * (D.u : SL(3, ℤ)))⁻¹ = D.i.rep * D.sval s * D.i.rep⁻¹ := by group
    rw [e] at this
    exact this
  have := conj_mem_gammaNQ M D.hq hX
  show i'.rep * ((D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ))) * i'.rep⁻¹ ∈ gammaNQ M
  have e : i'.rep * ((D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ))) * i'.rep⁻¹ =
      D.q * (D.i.rep * D.sval s * D.i.rep⁻¹) * D.q⁻¹ := by rw [D.hrep]; group
  rw [e]; exact this

/-- **The homomorphism `μ : Stab_{S_i}(u'Δ) → Γ(M) ∩ i'.rep⁻¹ Q i'.rep`**, `s ↦ u'⁻¹ s u'`. -/
def LineOver.mu : StabS (Δ6 M) (lineSub D.i) D.u →* ↥(gammaNQAt M i'.rep) where
  toFun s := ⟨(D.u : SL(3, ℤ))⁻¹ * D.sval s * (D.u : SL(3, ℤ)), D.mem_Q s⟩
  map_one' := by apply Subtype.ext; simp [LineOver.sval]
  map_mul' a b := by apply Subtype.ext; simp [LineOver.sval, mul_assoc]

end LineMu

section LineTheta

variable {M : ℕ} [NeZero M] {i' : LineFaces M} (D : LineOver M i') {E : Type} [AddCommGroup E] [Module ℂ E]
  (ρ : Representation ℂ ↥(gammaN 6) E) (ρM : Representation ℂ ↥(gammaN M) E) (hρ : ∀ x : ↥(Δ6 M), ρM (eΔ M x) = ρ x.1)

/-- The coefficient module of the line group `Γ_{Q'}` obtained from `ρM`. -/
abbrev lineW (i' : LineFaces M) (ρM : Representation ℂ ↥(gammaN M) E) : Rep ℂ ↥(gammaNQAt M i'.rep) :=
  Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN M i'.rep hp)) (Rep.of ρM)

omit [NeZero M] in
include hρ in
theorem LineOver.hTgen (s : StabS (Δ6 M) (lineSub D.i) D.u) (w : E) :
    ρ (D.u : ↥(gammaN 6)) ((lineW i' ρM).ρ (D.mu s) w) = ρ (((s : ↥(lineSub D.i)) : ↥(gammaN 6))) (ρ (D.u : ↥(gammaN 6)) w) := by
  have e : (lineW i' ρM).ρ (D.mu s) w = ρ (D.u⁻¹ * ((s : ↥(lineSub D.i)) : ↥(gammaN 6)) * D.u) w := by
    have := hρ ⟨(D.u⁻¹ * ((s : ↥(lineSub D.i)) : ↥(gammaN 6)) * D.u : ↥(gammaN 6)),
      (mem_stabilizer_quot_iff (Δ6 M) (lineSub D.i) D.u (s : ↥(lineSub D.i))).mp s.2⟩
    exact congrArg (fun f => f w) this
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- **The transport `Θ`** of the line classes of `Γ(M)` at `i'` with coefficients `ρM` to the `e_O`-component of the induced module `Fun(Γ(6)/Γ(M), E)`. -/
def LineOver.thetaGen : groupCohomology.H2 (lineW i' ρM) →ₗ[ℂ]
    groupCohomology.H2 (Rep.res (lineSub D.i).subtype (Rep.of (permRep ρ (Δ6 M)))) :=
  Theta ρ (Δ6 M) (lineSub D.i) D.u (lineW i' ρM) D.mu (ρ (D.u : ↥(gammaN 6))) (D.hTgen ρ ρM hρ)

end LineTheta

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
