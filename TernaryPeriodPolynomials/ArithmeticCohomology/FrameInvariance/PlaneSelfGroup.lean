module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneSelfTwist

@[expose] public section


/-!
# The big stabilizer of a plane face acting on its extension data

Formalized by Claude Sonnet 5.5.

The plane analogue of `LineSelfGroup`: `bigPlaneStabAt h = {f | h f h⁻¹ ∈ planeBorel}` acts on the extension `faceExt N h` through the homomorphisms `planeGθ`, `planeGφ`, `planeGα`, `planeGA` (Levi block `topLeft (h f h⁻¹)`), and on a coefficient module through `coeffEquiv`.
`gammaNPAt N h` is a normal subgroup of finite index of the big stabilizer (`N ≥ 3`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
open CongruenceSubgroup TernaryPoly.RankTwoAugmentedFrames

/-- The big stabilizer of the plane cusp `h⁻¹ P h`: the `f` with `h f h⁻¹ ∈ P(ℚ) ∩ SL₃(ℤ)`. -/
def bigPlaneStabAt (h : SL(3, ℤ)) : Subgroup SL(3, ℤ) := planeBorel.comap (MulAut.conj h).toMonoidHom

theorem mem_bigPlaneStabAt {h f : SL(3, ℤ)} : f ∈ bigPlaneStabAt h ↔ h * f * h⁻¹ ∈ planeBorel := Iff.rfl

/-- Membership in the big stabilizer, in the unfolded form used by the self-twists. -/
theorem bigPlane_mem {h : SL(3, ℤ)} (f : bigPlaneStabAt h) : h * f.1 * h⁻¹ ∈ planeBorel := f.2

section Hom

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ))

/-- The self-twist of the plane face at `h` attached to an element of the big stabilizer. -/
def planeX (f : bigPlaneStabAt h) : TwistEquiv (faceExt N h) (faceExt N h) :=
  planeSelfTwist (h := h) (f := f.1) N hN (bigPlane_mem f)

theorem planeX_θ_val (f : bigPlaneStabAt h) (p : gammaNPAt N h) :
    (((planeX N hN h f).θ p : gammaNPAt N h) : SL(3, ℤ)) = f.1 * p.1 * f.1⁻¹ :=
  planeSelfTwist_θ_val (h := h) (f := f.1) N hN (bigPlane_mem f) p

theorem planeX_θ_mul (f₁ f₂ : bigPlaneStabAt h) (p : gammaNPAt N h) :
    (planeX N hN h (f₁ * f₂)).θ p = (planeX N hN h f₁).θ ((planeX N hN h f₂).θ p) := by
  apply Subtype.ext
  rw [planeX_θ_val, planeX_θ_val, planeX_θ_val, Subgroup.coe_mul]
  group

/-- `f ↦ (conjugation by f)` as a homomorphism into the automorphisms of the plane group. -/
def planeGθ : bigPlaneStabAt h →* MulAut (gammaNPAt N h) :=
  MonoidHom.mk' (fun f => (planeX N hN h f).θ) (fun a b => MulEquiv.ext fun p => planeX_θ_mul N hN h a b p)

/-- `f ↦` the radical map of the self-twist. -/
def planeGφ : bigPlaneStabAt h →* MulAut RadicalLattice :=
  MonoidHom.mk' (fun f => (planeX N hN h f).φ) (fun a b => by
    refine MulEquiv.ext fun r => ?_
    apply (faceExt N h).inl_injective
    show (faceExt N h).inl ((planeX N hN h (a * b)).φ r) =
      (faceExt N h).inl ((planeX N hN h a).φ ((planeX N hN h b).φ r))
    rw [← (planeX N hN h (a * b)).inl_comm, planeX_θ_mul, (planeX N hN h b).inl_comm,
      (planeX N hN h a).inl_comm])

/-- `f ↦` the Levi map of the self-twist. -/
def planeGα : bigPlaneStabAt h →* MulAut (Gamma N) :=
  MonoidHom.mk' (fun f => (planeX N hN h f).α) (fun a b => by
    refine MulEquiv.ext fun l => ?_
    obtain ⟨e, rfl⟩ := (faceExt N h).rightHom_surjective l
    show (planeX N hN h (a * b)).α ((faceExt N h).rightHom e) =
      (planeX N hN h a).α ((planeX N hN h b).α ((faceExt N h).rightHom e))
    rw [← (planeX N hN h (a * b)).rightHom_comm, planeX_θ_mul, (planeX N hN h a).rightHom_comm,
      (planeX N hN h b).rightHom_comm])

theorem planeSelfA_mul (h : SL(3, ℤ)) (a b : bigPlaneStabAt h) :
    planeSelfA (h := h) (f := (a * b).1) (bigPlane_mem (a * b)) = planeSelfA (h := h) (f := a.1) (bigPlane_mem a) * planeSelfA (h := h) (f := b.1) (bigPlane_mem b) := by
  apply Units.ext
  have hab : h * (a * b : bigPlaneStabAt h).1 * h⁻¹ = (h * a.1 * h⁻¹) * (h * b.1 * h⁻¹) := by
    rw [Subgroup.coe_mul]; group
  rw [Units.val_mul, planeSelfA_val, planeSelfA_val, planeSelfA_val, hab, topLeft_mul_of_mem (bigPlane_mem b) (planeBorel_row _ (bigPlane_mem b))]

/-- `f ↦` the Levi block `topLeft (h f h⁻¹) ∈ GL₂(ℤ)`. -/
def planeGA (h : SL(3, ℤ)) : bigPlaneStabAt h →* IntegralGL :=
  MonoidHom.mk' (fun f => planeSelfA (h := h) (f := f.1) (bigPlane_mem f)) (fun a b => planeSelfA_mul h a b)

theorem planeGA_val (f : bigPlaneStabAt h) :
    ((planeGA h f : IntegralGL) : Matrix (Fin 2) (Fin 2) ℤ) = topLeft (h * f.1 * h⁻¹) :=
  planeSelfA_val (h := h) (f := f.1) (bigPlane_mem f)

theorem planeGθ_val (f : bigPlaneStabAt h) (p : gammaNPAt N h) :
    ((planeGθ N hN h f p : gammaNPAt N h) : SL(3, ℤ)) = f.1 * p.1 * f.1⁻¹ :=
  planeX_θ_val N hN h f p

theorem planeG_inl_comm (f : bigPlaneStabAt h) (r : RadicalLattice) :
    planeGθ N hN h f ((faceExt N h).inl r) = (faceExt N h).inl (planeGφ N hN h f r) :=
  (planeX N hN h f).inl_comm r

theorem planeG_rightHom_comm (f : bigPlaneStabAt h) (e : gammaNPAt N h) :
    (faceExt N h).rightHom (planeGθ N hN h f e) = planeGα N hN h f ((faceExt N h).rightHom e) :=
  (planeX N hN h f).rightHom_comm e

/-- **The Levi map is conjugation by the Levi block.** -/
theorem planeG_hA (f : bigPlaneStabAt h) (l : Gamma N) :
    ((gammaEquiv hN (planeGα N hN h f l) : gammaNGL N) : IntegralGL) =
      planeGA h f * (gammaEquiv hN l : gammaNGL N) * (planeGA h f)⁻¹ :=
  planeSelfTwist_glConj (h := h) (f := f.1) N hN (bigPlane_mem f) l

/-- **The determinant of the radical map is the determinant of the Levi block.** -/
theorem planeGφ_radDet (f : bigPlaneStabAt h) :
    radDet (planeGφ N hN h f).toMonoidHom = (planeGA h f).val.det :=
  planeSelfTwist_radDet (h := h) (f := f.1) N hN (bigPlane_mem f)

theorem planeGφ_inv_radDet (f : bigPlaneStabAt h) :
    radDet ((planeGφ N hN h f)⁻¹).toMonoidHom = (planeGA h f).val.det := by
  change radDet (planeSelfTwist (h := h) (f := f.1) N hN (bigPlane_mem f)).φ.symm.toMonoidHom =
    (planeSelfA (h := h) (f := f.1) (bigPlane_mem f)).val.det
  rw [planeSelfTwist_φ, radDet_phiPQ_symm, planeSelfA, AGP_det]

theorem planeGφ_inv_radDet_inv (f : bigPlaneStabAt h) :
    radDet ((planeGφ N hN h f)⁻¹).toMonoidHom = ((planeGA h f)⁻¹).val.det := by
  rw [planeGφ_inv_radDet, det_inv_eq_det]

end Hom

section Coefficients

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ SL(3, ℤ) V)
  (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ))

/-- The coefficient module of the plane group `gammaNPAt N h` restricted from `SL₃(ℤ)`. -/
abbrev planeGRep : Rep ℂ (gammaNPAt N h) := Rep.res (gammaNPAt N h).subtype (Rep.of ρ)

theorem planeGT_hT (f : bigPlaneStabAt h) (e : gammaNPAt N h) (v : V) :
    coeffEquiv ρ f.1 ((planeGRep ρ N h).ρ e v) =
      (planeGRep ρ N h).ρ (planeGθ N hN h f e) (coeffEquiv ρ f.1 v) := by
  change ρ f.1 (ρ e.1 v) = ρ ((planeGθ N hN h f e : gammaNPAt N h) : SL(3, ℤ)) (ρ f.1 v)
  rw [planeGθ_val, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

end Coefficients

section Index

variable (N : ℕ) (h : SL(3, ℤ))

theorem gammaNPAt_le_big : gammaNPAt N h ≤ bigPlaneStabAt h :=
  fun _ hp => mem_planeBorel_of_mem_planeStab hp.2

theorem gammaNPAt_big_normal : ((gammaNPAt N h).subgroupOf (bigPlaneStabAt h)).Normal := by
  constructor
  intro n hn g
  have hn' : h * n.1 * h⁻¹ ∈ gammaNP N := hn
  have e : h * (g.1 * n.1 * g.1⁻¹) * h⁻¹ = (h * g.1 * h⁻¹) * (h * n.1 * h⁻¹) * (h * g.1 * h⁻¹)⁻¹ := by
    group
  change h * ((g * n * g⁻¹ : bigPlaneStabAt h).1) * h⁻¹ ∈ gammaNP N
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact conj_mem_gammaNP N g.2 hn'

theorem gammaNP_eq_inf (hN : 3 ≤ N) : gammaNP N = gammaN N ⊓ planeBorel := by
  ext γ
  constructor
  · intro hγ; exact ⟨hγ.1, mem_planeBorel_of_mem_planeStab hγ.2⟩
  · intro hγ; exact ⟨hγ.1, mem_planeStab_of_gammaN hN hγ.1 hγ.2.1 hγ.2.2⟩

theorem gammaNPAt_big_relIndex_ne_zero [NeZero N] (hN : 3 ≤ N) :
    (gammaNPAt N h).relIndex (bigPlaneStabAt h) ≠ 0 := by
  have h1 : (gammaNP N).relIndex planeBorel ≠ 0 := by
    rw [gammaNP_eq_inf N hN, Subgroup.inf_relIndex_right]
    have : (gammaN N).IsFiniteRelIndex planeBorel := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  exact Subgroup.relIndex_comap_ne_zero (MulAut.conj h).toMonoidHom h1

theorem gammaNPAt_big_finiteIndex [NeZero N] (hN : 3 ≤ N) :
    ((gammaNPAt N h).subgroupOf (bigPlaneStabAt h)).FiniteIndex :=
  ⟨gammaNPAt_big_relIndex_ne_zero N h hN⟩

end Index

end TernaryPeriodPolynomials.Argument.FrameInvariance
