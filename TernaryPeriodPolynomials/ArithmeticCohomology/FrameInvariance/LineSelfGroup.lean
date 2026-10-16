module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineSelfTwist

@[expose] public section


/-!
# The big stabilizer of a line face acting on its extension data

Formalized by Claude Sonnet 5.5.

For the line cusp `h⁻¹ Q h` let `G = bigLineStabAt h = {f ∈ SL₃(ℤ) | h f h⁻¹ ∈ Q(ℚ) ∩ SL₃(ℤ)}` (`lineBorel`).  The self-twists `lineSelfTwist` are homomorphic in `f`:
`lineGθ` (conjugation by `f`), `lineGφ` (radical map `r ↦ a r B⁻¹`), `lineGα` (Levi conjugation), `lineGA` (the Levi block `B = botRight (h f h⁻¹) ∈ GL₂(ℤ)`), and `lineGT` (the action `ρ̃ f` on a coefficient module of `SL₃(ℤ)`).
`gammaNQAt N h` is a normal subgroup of finite index of `G` (`N ≥ 3`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

/-- The big stabilizer of the line cusp `h⁻¹ Q h`: the `f` with `h f h⁻¹ ∈ Q(ℚ) ∩ SL₃(ℤ)`. -/
def bigLineStabAt (h : SL(3, ℤ)) : Subgroup SL(3, ℤ) := lineBorel.comap (MulAut.conj h).toMonoidHom

theorem mem_bigLineStabAt {h f : SL(3, ℤ)} : f ∈ bigLineStabAt h ↔ h * f * h⁻¹ ∈ lineBorel := Iff.rfl

/-- Membership in the big stabilizer, in the unfolded form used by the self-twists. -/
theorem bigLine_mem {h : SL(3, ℤ)} (f : bigLineStabAt h) : h * f.1 * h⁻¹ ∈ lineBorel := f.2

section Hom

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ))

/-- The self-twist of the line face at `h` attached to an element of the big stabilizer. -/
def lineX (f : bigLineStabAt h) : TwistEquiv (lineFaceExt N h) (lineFaceExt N h) :=
  lineSelfTwist (h := h) (f := f.1) N hN (bigLine_mem f)

theorem lineX_θ_val (f : bigLineStabAt h) (p : gammaNQAt N h) :
    (((lineX N hN h f).θ p : gammaNQAt N h) : SL(3, ℤ)) = f.1 * p.1 * f.1⁻¹ :=
  lineSelfTwist_θ_val (h := h) (f := f.1) N hN (bigLine_mem f) p

theorem lineX_θ_mul (f₁ f₂ : bigLineStabAt h) (p : gammaNQAt N h) :
    (lineX N hN h (f₁ * f₂)).θ p = (lineX N hN h f₁).θ ((lineX N hN h f₂).θ p) := by
  apply Subtype.ext
  rw [lineX_θ_val, lineX_θ_val, lineX_θ_val, Subgroup.coe_mul]
  group

/-- `f ↦ (conjugation by f)` as a homomorphism into the automorphisms of the line group. -/
def lineGθ : bigLineStabAt h →* MulAut (gammaNQAt N h) :=
  MonoidHom.mk' (fun f => (lineX N hN h f).θ) (fun a b => MulEquiv.ext fun p => lineX_θ_mul N hN h a b p)

/-- `f ↦` the radical map of the self-twist. -/
def lineGφ : bigLineStabAt h →* MulAut RadicalLattice :=
  MonoidHom.mk' (fun f => (lineX N hN h f).φ) (fun a b => by
    refine MulEquiv.ext fun r => ?_
    apply (lineFaceExt N h).inl_injective
    show (lineFaceExt N h).inl ((lineX N hN h (a * b)).φ r) =
      (lineFaceExt N h).inl ((lineX N hN h a).φ ((lineX N hN h b).φ r))
    rw [← (lineX N hN h (a * b)).inl_comm, lineX_θ_mul, (lineX N hN h b).inl_comm,
      (lineX N hN h a).inl_comm])

/-- `f ↦` the Levi map of the self-twist. -/
def lineGα : bigLineStabAt h →* MulAut (Gamma N) :=
  MonoidHom.mk' (fun f => (lineX N hN h f).α) (fun a b => by
    refine MulEquiv.ext fun l => ?_
    obtain ⟨e, rfl⟩ := (lineFaceExt N h).rightHom_surjective l
    show (lineX N hN h (a * b)).α ((lineFaceExt N h).rightHom e) =
      (lineX N hN h a).α ((lineX N hN h b).α ((lineFaceExt N h).rightHom e))
    rw [← (lineX N hN h (a * b)).rightHom_comm, lineX_θ_mul, (lineX N hN h a).rightHom_comm,
      (lineX N hN h b).rightHom_comm])

theorem lineSelfA_mul (h : SL(3, ℤ)) (a b : bigLineStabAt h) :
    lineSelfA (h := h) (f := (a * b).1) (bigLine_mem (a * b)) = lineSelfA (h := h) (f := a.1) (bigLine_mem a) * lineSelfA (h := h) (f := b.1) (bigLine_mem b) := by
  apply Units.ext
  have hab : h * (a * b : bigLineStabAt h).1 * h⁻¹ = (h * a.1 * h⁻¹) * (h * b.1 * h⁻¹) := by
    rw [Subgroup.coe_mul]; group
  rw [Units.val_mul, lineSelfA_val, lineSelfA_val, lineSelfA_val, hab, botRight_mul (bigLine_mem a)]

/-- `f ↦` the Levi block `botRight (h f h⁻¹) ∈ GL₂(ℤ)`. -/
def lineGA (h : SL(3, ℤ)) : bigLineStabAt h →* IntegralGL :=
  MonoidHom.mk' (fun f => lineSelfA (h := h) (f := f.1) (bigLine_mem f)) (fun a b => lineSelfA_mul h a b)

theorem lineGA_val (f : bigLineStabAt h) :
    ((lineGA h f : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = botRight (h * f.1 * h⁻¹) :=
  lineSelfA_val (h := h) (f := f.1) (bigLine_mem f)

theorem lineGθ_val (f : bigLineStabAt h) (p : gammaNQAt N h) :
    ((lineGθ N hN h f p : gammaNQAt N h) : SL(3, ℤ)) = f.1 * p.1 * f.1⁻¹ :=
  lineX_θ_val N hN h f p

theorem lineG_inl_comm (f : bigLineStabAt h) (r : RadicalLattice) :
    lineGθ N hN h f ((lineFaceExt N h).inl r) = (lineFaceExt N h).inl (lineGφ N hN h f r) :=
  (lineX N hN h f).inl_comm r

theorem lineG_rightHom_comm (f : bigLineStabAt h) (e : gammaNQAt N h) :
    (lineFaceExt N h).rightHom (lineGθ N hN h f e) = lineGα N hN h f ((lineFaceExt N h).rightHom e) :=
  (lineX N hN h f).rightHom_comm e

/-- **The Levi map is conjugation by the Levi block.** -/
theorem lineG_hA (f : bigLineStabAt h) (l : Gamma N) :
    ((gammaEquiv hN (lineGα N hN h f l) : gammaNGL N) : IntegralGL) =
      lineGA h f * (gammaEquiv hN l : gammaNGL N) * (lineGA h f)⁻¹ :=
  lineSelfTwist_glConj (h := h) (f := f.1) N hN (bigLine_mem f) l

/-- **The determinant of the radical map is the determinant of the Levi block.** -/
theorem lineGφ_radDet (f : bigLineStabAt h) :
    radDet (lineGφ N hN h f).toMonoidHom = (lineGA h f).val.det :=
  lineSelfTwist_radDet (h := h) (f := f.1) N hN (bigLine_mem f)

theorem lineGφ_inv_radDet (f : bigLineStabAt h) :
    radDet ((lineGφ N hN h f)⁻¹).toMonoidHom = (lineGA h f).val.det := by
  change radDet (lineSelfTwist (h := h) (f := f.1) N hN (bigLine_mem f)).φ.symm.toMonoidHom =
    (lineSelfA (h := h) (f := f.1) (bigLine_mem f)).val.det
  rw [lineSelfTwist_φ, radDet_phiQ_symm, lineSelfA, AG_det]

theorem lineGφ_inv_radDet_inv (f : bigLineStabAt h) :
    radDet ((lineGφ N hN h f)⁻¹).toMonoidHom = ((lineGA h f)⁻¹).val.det := by
  rw [lineGφ_inv_radDet, det_inv_eq_det]

end Hom

section Coefficients

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ SL(3, ℤ) V)

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ))

/-- The coefficient module of the line group `gammaNQAt N h` restricted from `SL₃(ℤ)`. -/
abbrev lineGRep : Rep ℂ (gammaNQAt N h) := Rep.res (gammaNQAt N h).subtype (Rep.of ρ)

theorem lineGT_hT (f : bigLineStabAt h) (e : gammaNQAt N h) (v : V) :
    coeffEquiv ρ f.1 ((lineGRep ρ N h).ρ e v) = (lineGRep ρ N h).ρ (lineGθ N hN h f e) (coeffEquiv ρ f.1 v) := by
  change ρ f.1 (ρ e.1 v) = ρ ((lineGθ N hN h f e : gammaNQAt N h) : SL(3, ℤ)) (ρ f.1 v)
  rw [lineGθ_val, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

end Coefficients

section Index

variable (N : ℕ) (h : SL(3, ℤ))

theorem gammaNQAt_le_big : gammaNQAt N h ≤ bigLineStabAt h :=
  fun _ hp => mem_lineBorel_of_mem_lineStab hp.2

theorem gammaNQAt_big_normal : ((gammaNQAt N h).subgroupOf (bigLineStabAt h)).Normal := by
  constructor
  intro n hn g
  have hn' : h * n.1 * h⁻¹ ∈ gammaNQ N := hn
  have e : h * (g.1 * n.1 * g.1⁻¹) * h⁻¹ = (h * g.1 * h⁻¹) * (h * n.1 * h⁻¹) * (h * g.1 * h⁻¹)⁻¹ := by
    group
  change h * ((g * n * g⁻¹ : bigLineStabAt h).1) * h⁻¹ ∈ gammaNQ N
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact conj_mem_gammaNQ N g.2 hn'

theorem gammaNQ_eq_inf (hN : 3 ≤ N) : gammaNQ N = gammaN N ⊓ lineBorel := by
  ext γ
  constructor
  · intro hγ; exact ⟨hγ.1, mem_lineBorel_of_mem_lineStab hγ.2⟩
  · intro hγ; exact ⟨hγ.1, mem_lineStab_of_gammaN hN hγ.1 hγ.2.1 hγ.2.2⟩

theorem gammaNQAt_big_relIndex_ne_zero [NeZero N] (hN : 3 ≤ N) :
    (gammaNQAt N h).relIndex (bigLineStabAt h) ≠ 0 := by
  have h1 : (gammaNQ N).relIndex lineBorel ≠ 0 := by
    rw [gammaNQ_eq_inf N hN, Subgroup.inf_relIndex_right]
    have : (gammaN N).IsFiniteRelIndex lineBorel := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  exact Subgroup.relIndex_comap_ne_zero (MulAut.conj h).toMonoidHom h1

theorem gammaNQAt_big_finiteIndex [NeZero N] (hN : 3 ≤ N) :
    ((gammaNQAt N h).subgroupOf (bigLineStabAt h)).FiniteIndex :=
  ⟨gammaNQAt_big_relIndex_ne_zero N h hN⟩

end Index

end TernaryPeriodPolynomials.Argument.FrameInvariance
