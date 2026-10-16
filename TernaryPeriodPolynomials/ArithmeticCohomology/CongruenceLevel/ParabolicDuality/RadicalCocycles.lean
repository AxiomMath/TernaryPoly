module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalAlt
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDRadical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.Lattice

@[expose] public section


/-!
# The cocycles of the radical lattice `ℤ²` and the Koszul pairing on `H¹`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

Every pair of generator values satisfying the Koszul relation is realised by a crossed homomorphism of `ℤ²`
(`exists_cocycle_of_gen`, via the affine group `V ⋊ ℤ²`), crossed homomorphisms are determined by their generator values
(`cocycle_ext_gen`), and the Koszul (cup-product) pairing `PhiC` of two cocycles descends to a perfect pairing of
`groupCohomology.H1` of the radical lattice (`exists_radPairing`), for finite-dimensional invariantly and perfectly paired
coefficients.  The cocycle-level pairing is the alternation `altForm` of `RadicalAlt`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.SphericalDetection.Helpers (RadicalLattice radicalLatticeFirst radicalLatticeSecond radicalLattice_generated)
open scoped Classical

section Aff

/-- The affine group `V ⋊ ℤ²` of a representation of the radical lattice (cocycles are homomorphic sections). -/
structure Aff {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RadicalLattice V) where
  val : V
  grp : RadicalLattice

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ RadicalLattice V}

instance : Group (Aff ρ) where
  mul x y := ⟨x.val + ρ x.grp y.val, x.grp * y.grp⟩
  one := ⟨0, 1⟩
  inv x := ⟨-(ρ x.grp⁻¹ x.val), x.grp⁻¹⟩
  mul_assoc x y z := by
    change (⟨(x.val + ρ x.grp y.val) + ρ (x.grp * y.grp) z.val, (x.grp * y.grp) * z.grp⟩ : Aff ρ) =
      ⟨x.val + ρ x.grp (y.val + ρ y.grp z.val), x.grp * (y.grp * z.grp)⟩
    simp only [map_mul, Module.End.mul_apply, map_add, add_assoc, mul_assoc]
  one_mul x := by
    change (⟨0 + ρ 1 x.val, 1 * x.grp⟩ : Aff ρ) = x
    simp
  mul_one x := by
    change (⟨x.val + ρ x.grp 0, x.grp * 1⟩ : Aff ρ) = x
    simp
  inv_mul_cancel x := by
    change (⟨-(ρ x.grp⁻¹ x.val) + ρ x.grp⁻¹ x.val, x.grp⁻¹ * x.grp⟩ : Aff ρ) = ⟨0, 1⟩
    simp

theorem Aff.mul_def (x y : Aff ρ) : x * y = ⟨x.val + ρ x.grp y.val, x.grp * y.grp⟩ := rfl

/-- The projection `V ⋊ ℤ² → ℤ²`. -/
def Aff.proj : Aff ρ →* RadicalLattice where
  toFun x := x.grp
  map_one' := rfl
  map_mul' _ _ := rfl

end Aff

section Gen

/-- The generators of the radical lattice. -/
abbrev rl1 : RadicalLattice := radicalLatticeFirst
abbrev rl2 : RadicalLattice := radicalLatticeSecond

theorem rl_decomp (r : RadicalLattice) : r = rl1 ^ r.toAdd.1 * rl2 ^ r.toAdd.2 := by
  apply Multiplicative.toAdd.injective
  simp [rl1, rl2, radicalLatticeFirst, radicalLatticeSecond]

/-- A crossed homomorphism of the radical lattice vanishing on both generators vanishes. -/
theorem cocycle_eq_zero_of_gen (A : Rep ℂ RadicalLattice) {c : RadicalLattice → A}
    (hc : ∀ x y, c (x * y) = A.ρ x (c y) + c x) (h1 : c rl1 = 0) (h2 : c rl2 = 0) : c = 0 := by
  have h0 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    have h2' : c 1 + 0 = c 1 + c 1 := by rw [add_zero]; exact this.trans (add_comm _ _)
    exact (add_left_cancel h2').symm
  let K : Subgroup RadicalLattice :=
    { carrier := {g | c g = 0}
      one_mem' := h0
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) = 0
        rw [hc, show c a = 0 from ha, show c b = 0 from hb, map_zero, add_zero]
      inv_mem' := fun {a} ha => by
        show c a⁻¹ = 0
        have h := hc a a⁻¹
        rw [mul_inv_cancel, h0, show c a = 0 from ha, add_zero] at h
        have h3 := congrArg (A.ρ a⁻¹) h
        rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
        exact h3.symm }
  funext r
  rw [rl_decomp r]
  have m1 : rl1 ∈ K := h1
  have m2 : rl2 ∈ K := h2
  exact K.mul_mem (K.zpow_mem m1 _) (K.zpow_mem m2 _)

theorem cocycle_ext_gen (A : Rep ℂ RadicalLattice) (c d : groupCohomology.cocycles₁ A) (h1 : c.1 rl1 = d.1 rl1)
    (h2 : c.1 rl2 = d.1 rl2) : c = d := by
  have hc := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
  have hd := (groupCohomology.mem_cocycles₁_iff d.1).1 d.2
  have : (fun r => c.1 r - d.1 r) = 0 := by
    apply cocycle_eq_zero_of_gen A (c := fun r => c.1 r - d.1 r)
    · intro x y
      simp only [hc, hd, map_sub]; abel
    · simp [h1]
    · simp [h2]
  apply Subtype.ext
  funext r
  exact sub_eq_zero.mp (congrFun this r)

end Gen

section Exist

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ RadicalLattice V}

/-- The commuting generators `(p₁, s₁)`, `(p₂, s₂)` of the affine group. -/
def affGen (p : V) (s : RadicalLattice) : Aff ρ := ⟨p, s⟩

theorem affGen_comm (p₁ p₂ : V) (h : ρ rl1 p₂ + p₁ = ρ rl2 p₁ + p₂) : Commute (affGen (ρ := ρ) p₁ rl1) (affGen p₂ rl2) := by
  show affGen p₁ rl1 * affGen p₂ rl2 = affGen p₂ rl2 * affGen p₁ rl1
  change (⟨p₁ + ρ rl1 p₂, rl1 * rl2⟩ : Aff ρ) = ⟨p₂ + ρ rl2 p₁, rl2 * rl1⟩
  rw [mul_comm rl1 rl2, add_comm p₁, h, add_comm]

theorem Aff.proj_zpow (x : Aff ρ) (k : ℤ) : (x ^ k).grp = x.grp ^ k := by
  have := map_zpow (Aff.proj (ρ := ρ)) x k
  exact this

/-- **Every pair of generator values satisfying the Koszul relation is the generator values of a crossed homomorphism.** -/
theorem exists_cocycle_of_gen (A : Rep ℂ RadicalLattice) (p₁ p₂ : A) (h : A.ρ rl1 p₂ + p₁ = A.ρ rl2 p₁ + p₂) :
    ∃ c : groupCohomology.cocycles₁ A, c.1 rl1 = p₁ ∧ c.1 rl2 = p₂ := by
  let g₁ : Aff A.ρ := affGen p₁ rl1
  let g₂ : Aff A.ρ := affGen p₂ rl2
  have hcomm : Commute g₁ g₂ := affGen_comm p₁ p₂ h
  let ψ : RadicalLattice → Aff A.ρ := fun r => g₁ ^ r.toAdd.1 * g₂ ^ r.toAdd.2
  have hψ : ∀ r r', ψ (r * r') = ψ r * ψ r' := by
    intro r r'
    simp only [ψ, toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add]
    have hc' : Commute (g₁ ^ r'.toAdd.1) (g₂ ^ r.toAdd.2) := (hcomm.zpow_zpow _ _)
    calc g₁ ^ r.toAdd.1 * g₁ ^ r'.toAdd.1 * (g₂ ^ r.toAdd.2 * g₂ ^ r'.toAdd.2)
        = g₁ ^ r.toAdd.1 * (g₁ ^ r'.toAdd.1 * g₂ ^ r.toAdd.2) * g₂ ^ r'.toAdd.2 := by group
      _ = g₁ ^ r.toAdd.1 * (g₂ ^ r.toAdd.2 * g₁ ^ r'.toAdd.1) * g₂ ^ r'.toAdd.2 := by rw [hc'.eq]
      _ = g₁ ^ r.toAdd.1 * g₂ ^ r.toAdd.2 * (g₁ ^ r'.toAdd.1 * g₂ ^ r'.toAdd.2) := by group
  have hgrp : ∀ r, (ψ r).grp = r := by
    intro r
    simp only [ψ]
    change (g₁ ^ r.toAdd.1).grp * (g₂ ^ r.toAdd.2).grp = r
    rw [Aff.proj_zpow, Aff.proj_zpow]
    exact (rl_decomp r).symm
  refine ⟨⟨fun r => (ψ r).val, ?_⟩, ?_, ?_⟩
  · rw [groupCohomology.mem_cocycles₁_iff]
    intro x y
    have := hψ x y
    have e1 := congrArg Aff.val this
    change (ψ (x * y)).val = (ψ x).val + A.ρ (ψ x).grp (ψ y).val at e1
    rw [hgrp] at e1
    rw [e1, add_comm]
  · have : ψ rl1 = g₁ := by
      simp [ψ, rl1, radicalLatticeFirst]
    show (ψ rl1).val = p₁
    rw [this]
    rfl
  · have : ψ rl2 = g₂ := by
      simp [ψ, rl2, radicalLatticeSecond]
    show (ψ rl2).val = p₂
    rw [this]
    rfl

end Exist

section Pairing

variable (A A' : Rep ℂ RadicalLattice) (e : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ)

/-- The Koszul pairing of two crossed homomorphisms of the radical lattice: `a(s₁, s₂)` of their cup product. -/
def PhiC : groupCohomology.cocycles₁ A →ₗ[ℂ] groupCohomology.cocycles₁ A' →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun c c' => altForm A'.ρ e c.1 c'.1 rl1 rl2)
    (fun c d c' => by
      have h1 : (c + d).1 rl1 = c.1 rl1 + d.1 rl1 := rfl
      have h2 : (c + d).1 rl2 = c.1 rl2 + d.1 rl2 := rfl
      simp only [altForm, h1, h2, map_add, LinearMap.add_apply]; ring)
    (fun a c c' => by
      have h1 : (a • c).1 rl1 = a • c.1 rl1 := rfl
      have h2 : (a • c).1 rl2 = a • c.1 rl2 := rfl
      simp only [altForm, h1, h2, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun c c' d => by
      have h1 : (c' + d).1 rl1 = c'.1 rl1 + d.1 rl1 := rfl
      have h2 : (c' + d).1 rl2 = c'.1 rl2 + d.1 rl2 := rfl
      simp only [altForm, h1, h2, map_add]; ring)
    (fun a c c' => by
      have h1 : (a • c').1 rl1 = a • c'.1 rl1 := rfl
      have h2 : (a • c').1 rl2 = a • c'.1 rl2 := rfl
      simp only [altForm, h1, h2, map_smul, smul_eq_mul]; ring)

theorem PhiC_apply (c : groupCohomology.cocycles₁ A) (c' : groupCohomology.cocycles₁ A') :
    PhiC A A' e c c' = e (c.1 rl1) (A'.ρ rl1 (c'.1 rl2)) - e (c.1 rl2) (A'.ρ rl2 (c'.1 rl1)) := rfl

variable {A A' e}

theorem PhiC_boundary_left (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b) (v : A) (c' : groupCohomology.cocycles₁ A')
    (c : groupCohomology.cocycles₁ A) (hc : ∀ g, c.1 g = A.ρ g v - v) : PhiC A A' e c c' = 0 := by
  have hc' := (groupCohomology.mem_cocycles₁_iff c'.1).1 c'.2
  have key : A'.ρ rl1 (c'.1 rl2) + c'.1 rl1 = A'.ρ rl2 (c'.1 rl1) + c'.1 rl2 := by
    rw [← hc' rl1 rl2, ← hc' rl2 rl1, mul_comm]
  have h1 := he rl1 v (c'.1 rl2)
  have h2 := he rl2 v (c'.1 rl1)
  have h3 := congrArg (e v) key
  rw [PhiC_apply, hc rl1, hc rl2]
  simp only [map_sub, LinearMap.sub_apply, map_add] at h3 ⊢
  linear_combination h1 - h2 - h3

theorem PhiC_boundary_right (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b) (w : A') (c : groupCohomology.cocycles₁ A)
    (c' : groupCohomology.cocycles₁ A') (hc' : ∀ g, c'.1 g = A'.ρ g w - w) : PhiC A A' e c c' = 0 := by
  have hc := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
  have key : A.ρ rl1 (c.1 rl2) + c.1 rl1 = A.ρ rl2 (c.1 rl1) + c.1 rl2 := by
    rw [← hc rl1 rl2, ← hc rl2 rl1, mul_comm]
  have comm : A'.ρ rl1 (A'.ρ rl2 w) = A'.ρ rl2 (A'.ρ rl1 w) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have h1 := he rl1 (c.1 rl2) (A'.ρ rl2 w)
  have h2 := he rl2 (c.1 rl1) (A'.ρ rl1 w)
  have h3 := congrArg (fun a => e a (A'.ρ rl1 (A'.ρ rl2 w))) key
  simp only [map_add, LinearMap.add_apply] at h3
  rw [PhiC_apply, hc' rl1, hc' rl2]
  simp only [map_sub]
  rw [comm] at h3 ⊢
  rw [comm] at h1
  linear_combination h3 - h1 + h2

end Pairing

section Radical

open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

variable {A A' : Rep ℂ RadicalLattice} {e : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ}

theorem H1π_eq_zero_iff_gen (c : groupCohomology.cocycles₁ A) :
    groupCohomology.H1π A c = 0 ↔ ∃ v : A, ∀ g, c.1 g = A.ρ g v - v := by
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun g => ?_⟩
    have := congrFun hu g
    simp only [groupCohomology.d₀₁_hom_apply] at this
    exact this.symm
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    funext g
    simp only [groupCohomology.d₀₁_hom_apply]
    exact (hu g).symm

/-- The Koszul data of the radical lattice acting on an invariantly paired `A, A'`. -/
def radKData (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b)
    (hl : ∀ a, (∀ b, e a b = 0) → a = 0) (hr : ∀ b, (∀ a, e a b = 0) → b = 0) : Koszul.KData A A' :=
  koszulOfRep A.ρ A'.ρ rl1 rl2 (mul_comm _ _) e (he rl1) (he rl2) hl hr

theorem PhiC_eq_Phi (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b)
    (hl : ∀ a, (∀ b, e a b = 0) → a = 0) (hr : ∀ b, (∀ a, e a b = 0) → b = 0)
    (c : groupCohomology.cocycles₁ A) (c' : groupCohomology.cocycles₁ A') :
    PhiC A A' e c c' = (radKData he hl hr).Phi (c.1 rl1, c.1 rl2) (c'.1 rl1, c'.1 rl2) := rfl

theorem d1'_eq_zero_of_cocycle (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b)
    (hl : ∀ a, (∀ b, e a b = 0) → a = 0) (hr : ∀ b, (∀ a, e a b = 0) → b = 0)
    (c' : groupCohomology.cocycles₁ A') :
    (radKData he hl hr).d1' (c'.1 rl1, c'.1 rl2) = 0 := by
  have hc' := (groupCohomology.mem_cocycles₁_iff c'.1).1 c'.2
  have key : A'.ρ rl1 (c'.1 rl2) + c'.1 rl1 = A'.ρ rl2 (c'.1 rl1) + c'.1 rl2 := by
    rw [← hc' rl1 rl2, ← hc' rl2 rl1, mul_comm]
  show (A'.ρ rl2 (c'.1 rl1) - c'.1 rl1) - (A'.ρ rl1 (c'.1 rl2) - c'.1 rl2) = 0
  linear_combination (norm := abel) -key

theorem d1_eq_zero_of_cocycle (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b)
    (hl : ∀ a, (∀ b, e a b = 0) → a = 0) (hr : ∀ b, (∀ a, e a b = 0) → b = 0)
    (c : groupCohomology.cocycles₁ A) :
    (radKData he hl hr).d1 (c.1 rl1, c.1 rl2) = 0 := by
  have hc := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
  have key : A.ρ rl1 (c.1 rl2) + c.1 rl1 = A.ρ rl2 (c.1 rl1) + c.1 rl2 := by
    rw [← hc rl1 rl2, ← hc rl2 rl1, mul_comm]
  show (A.ρ rl2 (c.1 rl1) - c.1 rl1) - (A.ρ rl1 (c.1 rl2) - c.1 rl2) = 0
  linear_combination (norm := abel) -key

/-- **The Koszul pairing on `H¹(ℤ², A) × H¹(ℤ², A')`**, perfect when `A, A'` are finite-dimensional, invariantly
and perfectly paired. -/
theorem exists_radPairing (he : ∀ g a b, e (A.ρ g a) (A'.ρ g b) = e a b)
    (hl : ∀ a, (∀ b, e a b = 0) → a = 0) (hr : ∀ b, (∀ a, e a b = 0) → b = 0)
    [FiniteDimensional ℂ A] [FiniteDimensional ℂ A'] :
    ∃ B : groupCohomology.H1 A →ₗ[ℂ] groupCohomology.H1 A' →ₗ[ℂ] ℂ,
      (∀ c c', B (groupCohomology.H1π A c) (groupCohomology.H1π A' c') = PhiC A A' e c c') ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  have h1 : Function.Surjective (groupCohomology.H1π A).hom := by
    intro x
    induction x using groupCohomology.H1_induction_on with
    | h c => exact ⟨c, rfl⟩
  have h2 : Function.Surjective (groupCohomology.H1π A').hom := by
    intro x
    induction x using groupCohomology.H1_induction_on with
    | h c => exact ⟨c, rfl⟩
  have hL : ∀ c : groupCohomology.cocycles₁ A, (groupCohomology.H1π A).hom c = 0 → ∀ c', PhiC A A' e c c' = 0 := by
    intro c hc c'
    obtain ⟨v, hv⟩ := (H1π_eq_zero_iff_gen c).1 hc
    exact PhiC_boundary_left he v c' c hv
  have hR : ∀ c' : groupCohomology.cocycles₁ A', (groupCohomology.H1π A').hom c' = 0 → ∀ c, PhiC A A' e c c' = 0 := by
    intro c' hc' c
    obtain ⟨v, hv⟩ := (H1π_eq_zero_iff_gen c').1 hc'
    exact PhiC_boundary_right he v c c' hv
  obtain ⟨B, hB⟩ := exists_descent (PhiC A A' e) (groupCohomology.H1π A).hom (groupCohomology.H1π A').hom h1 h2 hL hR
  refine ⟨B, hB, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := h1 x
    change groupCohomology.H1π A c = 0
    rw [H1π_eq_zero_iff_gen]
    obtain ⟨x0, hx0⟩ := Koszul.KData.left_annihilator (radKData he hl hr) (c.1 rl1, c.1 rl2) (fun q hq => by
      obtain ⟨c', hc'1, hc'2⟩ := exists_cocycle_of_gen A' q.1 q.2 (by
        have : (A'.ρ rl2 q.1 - q.1) - (A'.ρ rl1 q.2 - q.2) = 0 := hq
        linear_combination (norm := abel) -this)
      have := hx (groupCohomology.H1π A' c')
      rw [hB, PhiC_eq_Phi he hl hr, hc'1, hc'2] at this
      exact this)
    refine ⟨x0, fun g => ?_⟩
    have hcoc : (⟨fun g => A.ρ g x0 - x0, by
        rw [groupCohomology.mem_cocycles₁_iff]
        intro a b
        simp [map_mul]⟩ : groupCohomology.cocycles₁ A) = c := by
      apply cocycle_ext_gen
      · exact (congrArg Prod.fst hx0).symm
      · exact (congrArg Prod.snd hx0).symm
    exact (congrFun (congrArg Subtype.val hcoc) g).symm
  · intro y hy
    obtain ⟨c', rfl⟩ := h2 y
    change groupCohomology.H1π A' c' = 0
    rw [H1π_eq_zero_iff_gen]
    obtain ⟨y0, hy0⟩ := Koszul.KData.right_annihilator (radKData he hl hr) (c'.1 rl1, c'.1 rl2) (fun p hp => by
      obtain ⟨c, hc1, hc2⟩ := exists_cocycle_of_gen A p.1 p.2 (by
        have : (A.ρ rl2 p.1 - p.1) - (A.ρ rl1 p.2 - p.2) = 0 := hp
        linear_combination (norm := abel) -this)
      have := hy (groupCohomology.H1π A c)
      rw [hB, PhiC_eq_Phi he hl hr, hc1, hc2] at this
      exact this)
    refine ⟨y0, fun g => ?_⟩
    have hcoc : (⟨fun g => A'.ρ g y0 - y0, by
        rw [groupCohomology.mem_cocycles₁_iff]
        intro a b
        simp [map_mul]⟩ : groupCohomology.cocycles₁ A') = c' := by
      apply cocycle_ext_gen
      · exact (congrArg Prod.fst hy0).symm
      · exact (congrArg Prod.snd hy0).symm
    exact (congrFun (congrArg Subtype.val hcoc) g).symm

end Radical


end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
