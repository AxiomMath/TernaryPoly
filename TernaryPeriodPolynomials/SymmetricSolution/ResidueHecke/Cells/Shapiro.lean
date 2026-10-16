module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Levi

@[expose] public section


/-!
# Lemma B.1: Shapiro's lemma in the Hom model (finite-support image)

Formalized by Claude Sonnet 5.5.
Paper: Lemma B.1
(`lem:literal-residue-comparison`), the Shapiro isomorphism
`H₃(P_H, 𝓡_{n,H} ⊗ det) ≅ H₃(G, 𝓡_n ⊗ det)`.

The residue module is the induced module `𝓡_n = ⨁_H 𝓡_{n,H}` of the `P_H`-module `𝓡_{n,H₀}`,
`H₀ = {a = 0}`: the element `x ∈ G` moves the summand `H₀` to `H₀ x⁻¹`, and `ν x = H₀ x` depends only
on the coset `P_H x`.  Frobenius reciprocity `Sh : Hom_G(St, 𝓡_n) → Hom_{P_H}(St, 𝓡_{n,H₀})`
(`F ↦ component_{H₀} ∘ F`) is injective, and since `⨁` is the induced and not the coinduced module
its image consists exactly of the maps `φ` of *finite support*: for every `c ∈ St`
only finitely many hyperplanes `H = ν x` have `φ(x c) ≠ 0`.

This file defines the inverse `invShapiro` (`F(c) = ∑ᶠ_H ρ(x_H⁻¹) lof_{H₀} φ(x_H c)`, `ν x_H = H`)
and the linear equivalence `shapiroEquiv : ResidueHom n (-1) ≃ₗ[ℚ] StabHomFin n`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open scoped Matrix
open TernaryPoly TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryResidueSupport (rowAction rowAction_mul rowAction_one axis normalOfRow
  normalOfRow_eq_iff rowAction_normalOfRow axis_primitive exists_primitive_row)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPoly.OrdinaryFullAction TernaryPoly.OrdinaryFullCoefficient

/-- The residue representation of `G = GL₃(ℤ)` (exponent `-1`). -/
abbrev rho (n : ℕ) (g : IntegralGL) : Residues n →ₗ[ℚ] Residues n :=
  integralResidueAction n (-1) g

/-- The action of `g ∈ G` on the Steinberg module. -/
abbrev cyc (g : IntegralGL) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] OrdinaryIncidenceChains.Cycles :=
  cycleAction (integral g)

/-- The hyperplane `H₀ x`; it depends only on the coset `P_H x`. -/
def nu (x : IntegralGL) : Normal := rowAction x (axis 0)

theorem nu_one : nu 1 = axis 0 := rowAction_one _

theorem nu_left_PH {s : IntegralGL} (hs : s ∈ PH) (x : IntegralGL) : nu (s * x) = nu x := by
  have hs' : rowAction s (axis 0) = axis 0 := hs
  unfold nu
  rw [rowAction_mul, hs']

theorem nu_eq {x y : IntegralGL} (h : nu x = nu y) : ∃ s ∈ PH, y = s * x := by
  refine ⟨y * x⁻¹, ?_, by group⟩
  change rowAction (y * x⁻¹) (axis 0) = axis 0
  rw [rowAction_mul]
  have h' : rowAction y (axis 0) = rowAction x (axis 0) := h.symm
  rw [h', ← rowAction_mul, mul_inv_cancel, rowAction_one]

theorem nu_surj (L : Normal) : ∃ x : IntegralGL, nu x = L := by
  obtain ⟨v, hv, rfl⟩ := exists_primitive_row L
  let M := PrimitiveBasisExtension.primitiveCompletion v hv
  have hdet : (M.val)ᵀ.det = 1 := by
    rw [Matrix.det_transpose]; exact PrimitiveBasisExtension.primitiveCompletion_det v hv
  let x : IntegralGL := Matrix.nonsingInvUnit (M.val)ᵀ (by rw [hdet]; exact isUnit_one)
  refine ⟨x, ?_⟩
  unfold nu
  change rowAction x (normalOfRow (Pi.single 0 1) (axis_primitive 0)) = _
  rw [rowAction_normalOfRow]
  apply (normalOfRow_eq_iff _ _).mpr
  left
  funext j
  have hcol := congrFun (PrimitiveBasisExtension.primitiveCompletion_first_column v hv) j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply, x, M] at hcol ⊢
  exact hcol

theorem rho_mul (n : ℕ) (g h : IntegralGL) (r : Residues n) :
    rho n (g * h) r = rho n g (rho n h r) := by
  change integralResidueAction n (-1) (g * h) r = _
  rw [map_mul]; rfl

theorem rho_one (n : ℕ) (r : Residues n) : rho n 1 r = r := by
  change integralResidueAction n (-1) 1 r = _
  rw [map_one]; rfl

theorem rho_inv_rho (n : ℕ) (g : IntegralGL) (r : Residues n) : rho n g⁻¹ (rho n g r) = r := by
  rw [← rho_mul, inv_mul_cancel, rho_one]

theorem rho_rho_inv (n : ℕ) (g : IntegralGL) (r : Residues n) : rho n g (rho n g⁻¹ r) = r := by
  rw [← rho_mul, mul_inv_cancel, rho_one]

theorem cyc_mul (g h : IntegralGL) (c : OrdinaryIncidenceChains.Cycles) :
    cyc (g * h) c = cyc g (cyc h c) := by
  change cycleAction (integral (g * h)) c = _
  rw [map_mul, map_mul]; rfl

/-- For `s ∈ P_H` the action on the `H₀`-summand stays in the `H₀`-summand. -/
theorem rho_PH_lof (n : ℕ) {s : IntegralGL} (hs : s ∈ PH)
    (a : ResidueFiber n (axis 0)) :
    rho n s (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) a) =
      DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (fiberAction n s a) := by
  apply DFinsupp.ext
  intro H
  by_cases h : H = axis 0
  · subst h
    simp [fiberAction]
  · have hs' : s⁻¹ ∈ PH := PH.inv_mem hs
    have h2 : rowAction s⁻¹ (axis 0) = axis 0 := hs'
    have h3 : H ≠ rowAction s⁻¹ (axis 0) := by rw [h2]; exact h
    rw [action_lof_component_zero n (-1) s (axis 0) H a h3]
    exact (DirectSum.of_eq_of_ne _ _ _ h).symm

/-- The summand attached to `x ∈ G`: `ρ(x⁻¹)` of the `H₀`-summand element `φ(x c)`; it is supported
at the hyperplane `ν x`. -/
def term (n : ℕ) (φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0))
    (c : OrdinaryIncidenceChains.Cycles) (x : IntegralGL) : Residues n :=
  rho n x⁻¹ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (φ (cyc x c)))

theorem term_left_PH (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) {s : IntegralGL} (hs : s ∈ PH) (c : OrdinaryIncidenceChains.Cycles)
    (x : IntegralGL) : term n φ c (s * x) = term n φ c x := by
  unfold term
  have h1 : φ (cyc (s * x) c) = fiberAction n s (φ (cyc x c)) := by
    rw [cyc_mul]; exact hφ s hs _
  rw [h1, ← rho_PH_lof n hs, mul_inv_rev, rho_mul, rho_inv_rho]

theorem term_nu (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (c : OrdinaryIncidenceChains.Cycles) {x y : IntegralGL}
    (h : nu x = nu y) : term n φ c x = term n φ c y := by
  obtain ⟨s, hs, rfl⟩ := nu_eq h
  exact (term_left_PH n hφ hs c x).symm

/-- The component of the inverse Shapiro sum at the hyperplane `H`: `term` at any `x` with `ν x = H`. -/
def tau (n : ℕ) (φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0))
    (c : OrdinaryIncidenceChains.Cycles) (H : Normal) : Residues n :=
  term n φ c (Classical.choose (nu_surj H))

theorem tau_eq (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (c : OrdinaryIncidenceChains.Cycles) {x : IntegralGL} {H : Normal}
    (hx : nu x = H) : tau n φ c H = term n φ c x :=
  term_nu n hφ c ((Classical.choose_spec (nu_surj H)).trans hx.symm)

theorem term_ne_zero_iff (n : ℕ) (φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0))
    (c : OrdinaryIncidenceChains.Cycles) (x : IntegralGL) :
    term n φ c x ≠ 0 ↔ φ (cyc x c) ≠ 0 := by
  unfold term
  constructor
  · intro h h0
    apply h
    rw [h0, map_zero, map_zero]
  · intro h h0
    apply h
    have h1 := congrArg (rho n x) h0
    rw [rho_rho_inv, map_zero] at h1
    exact DirectSum.of_injective (axis 0) (h1.trans (map_zero _).symm)

/-- **Finite support**: for every cycle `c` only finitely many hyperplanes `ν x` have `φ(x c) ≠ 0`. -/
def HasFiniteSupport (n : ℕ)
    (φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)) : Prop :=
  ∀ c : OrdinaryIncidenceChains.Cycles,
    {H : Normal | ∃ x : IntegralGL, nu x = H ∧ φ (cyc x c) ≠ 0}.Finite

theorem tau_support (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (c : OrdinaryIncidenceChains.Cycles) :
    Function.support (tau n φ c) =
      {H : Normal | ∃ x : IntegralGL, nu x = H ∧ φ (cyc x c) ≠ 0} := by
  ext H
  obtain ⟨x, hx⟩ := nu_surj H
  simp only [Function.mem_support, Set.mem_ofPred_eq]
  rw [tau_eq n hφ c hx, term_ne_zero_iff]
  constructor
  · intro h; exact ⟨x, hx, h⟩
  · rintro ⟨y, hy, h⟩
    have : φ (cyc x c) ≠ 0 := by
      obtain ⟨s, hs, rfl⟩ := nu_eq (hx.trans hy.symm)
      intro h0
      apply h
      rw [cyc_mul, hφ s hs, h0, map_zero]
    exact this

theorem tau_add (n : ℕ) (φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0))
    (c c' : OrdinaryIncidenceChains.Cycles) (H : Normal) :
    tau n φ (c + c') H = tau n φ c H + tau n φ c' H := by
  simp [tau, term, map_add]

theorem tau_smul (n : ℕ) (φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0))
    (a : ℚ) (c : OrdinaryIncidenceChains.Cycles) (H : Normal) :
    tau n φ (a • c) H = a • tau n φ c H := by
  simp [tau, term, map_smul]

/-- The inverse of Frobenius reciprocity on a finite-support `φ`: `c ↦ ∑ᶠ_H τ(c, H)`. -/
def invSh (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (hfin : HasFiniteSupport n φ) :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] Residues n where
  toFun c := ∑ᶠ H, tau n φ c H
  map_add' c c' := by
    have h1 : (Function.support (tau n φ c)).Finite := by rw [tau_support n hφ]; exact hfin c
    have h2 : (Function.support (tau n φ c')).Finite := by rw [tau_support n hφ]; exact hfin c'
    simp only [tau_add]
    exact finsum_add_distrib h1 h2
  map_smul' a c := by
    have h1 : (Function.support (tau n φ c)).Finite := by rw [tau_support n hφ]; exact hfin c
    simp only [tau_smul, RingHom.id_apply]
    exact (smul_finsum' a h1).symm

theorem rho_tau (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (y : IntegralGL) (c : OrdinaryIncidenceChains.Cycles) (H : Normal) :
    rho n y (tau n φ c H) = tau n φ (cyc y c) (rowAction y⁻¹ H) := by
  obtain ⟨x, hx⟩ := nu_surj H
  have hx' : nu (x * y⁻¹) = rowAction y⁻¹ H := by
    unfold nu at hx ⊢
    rw [rowAction_mul, hx]
  rw [tau_eq n hφ c hx, tau_eq n hφ _ hx']
  unfold term
  rw [← cyc_mul, mul_assoc, inv_mul_cancel, mul_one, mul_inv_rev, inv_inv, rho_mul]

/-- The reindexing `H ↦ H y⁻¹` of the hyperplanes. -/
def rowActionEquiv (y : IntegralGL) : Normal ≃ Normal where
  toFun := rowAction y⁻¹
  invFun := rowAction y
  left_inv H := by rw [← rowAction_mul, inv_mul_cancel, rowAction_one]
  right_inv H := by rw [← rowAction_mul, mul_inv_cancel, rowAction_one]

theorem invSh_equivariant (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (hfin : HasFiniteSupport n φ) (y : IntegralGL)
    (c : OrdinaryIncidenceChains.Cycles) :
    invSh n hφ hfin (cyc y c) = rho n y (invSh n hφ hfin c) := by
  change ∑ᶠ H, tau n φ (cyc y c) H = rho n y (∑ᶠ H, tau n φ c H)
  have h1 : (Function.support (tau n φ c)).Finite := by rw [tau_support n hφ]; exact hfin c
  have h2 : rho n y (∑ᶠ H, tau n φ c H) = ∑ᶠ H, rho n y (tau n φ c H) :=
    (rho n y).toAddMonoidHom.map_finsum h1
  rw [h2]
  simp only [rho_tau n hφ]
  exact (finsum_comp_equiv (rowActionEquiv y) (f := tau n φ (cyc y c))).symm

/-- The residue functional attached to a finite-support `P_H`-equivariant map. -/
def invShapiro (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (hfin : HasFiniteSupport n φ) : ResidueHom n (-1) :=
  ⟨invSh n hφ hfin, fun g c => invSh_equivariant n hφ hfin g c⟩

theorem Sh_invShapiro (n : ℕ) {φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)}
    (hφ : φ ∈ StabHom n) (hfin : HasFiniteSupport n φ) :
    (Sh n (invShapiro n hφ hfin)).val = φ := by
  apply LinearMap.ext
  intro c
  change component n (axis 0) (∑ᶠ H, tau n φ c H) = φ c
  have h1 : (Function.support (tau n φ c)).Finite := by rw [tau_support n hφ]; exact hfin c
  have h2 : component n (axis 0) (∑ᶠ H, tau n φ c H) =
      ∑ᶠ H, component n (axis 0) (tau n φ c H) :=
    (component n (axis 0)).toAddMonoidHom.map_finsum h1
  rw [h2, finsum_eq_single _ (axis 0)]
  · rw [tau_eq n hφ c nu_one]
    unfold term
    simp only [inv_one, rho_one, cyc]
    rw [map_one]
    simp
  · intro H hH
    obtain ⟨x, hx⟩ := nu_surj H
    rw [tau_eq n hφ c hx]
    unfold term
    change (rho n x⁻¹ (DirectSum.lof ℚ Normal (ResidueFiber n) (axis 0) (φ (cyc x c)))) (axis 0) = 0
    apply action_lof_component_zero n (-1) x⁻¹ (axis 0) (axis 0) _
    rw [inv_inv]
    intro h
    apply hH
    rw [← hx]
    exact h.symm

theorem Sh_finiteSupport (n : ℕ) (F : ResidueHom n (-1)) : HasFiniteSupport n (Sh n F).val := by
  classical
  intro c
  refine (DFinsupp.support (F.val c)).finite_toSet.subset ?_
  rintro H ⟨x, rfl, hx⟩
  by_contra hne
  apply hx
  have h0 : (F.val c) (rowAction x (axis 0)) = 0 := by
    by_contra h
    exact hne (by rw [Finset.mem_coe, DFinsupp.mem_support_iff]; exact h)
  have := component_action_zero_of n (-1) x (axis 0) (F.val c) h0
  change component n (axis 0) (F.val (cyc x c)) = 0
  rw [show F.val (cyc x c) = rho n x (F.val c) from F.property x c]
  exact this

/-- `Hom_{P_H}(St, 𝓡_{n,H})` restricted to the finite-support maps: the image of Frobenius
reciprocity. -/
def StabHomFin (n : ℕ) :
    Submodule ℚ (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0)) where
  carrier := {φ | φ ∈ StabHom n ∧ HasFiniteSupport n φ}
  zero_mem' := ⟨zero_mem _, fun c => by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro H ⟨x, _, hx⟩
    exact hx (by simp)⟩
  add_mem' := by
    rintro φ ψ ⟨hφ, fφ⟩ ⟨hψ, fψ⟩
    refine ⟨add_mem hφ hψ, fun c => ?_⟩
    refine ((fφ c).union (fψ c)).subset ?_
    rintro H ⟨x, rfl, hx⟩
    by_cases h : φ (cyc x c) = 0
    · right
      exact ⟨x, rfl, fun h' => hx (by simp [h, h'])⟩
    · left
      exact ⟨x, rfl, h⟩
  smul_mem' := by
    rintro a φ ⟨hφ, fφ⟩
    refine ⟨Submodule.smul_mem _ a hφ, fun c => ?_⟩
    refine (fφ c).subset ?_
    rintro H ⟨x, rfl, hx⟩
    exact ⟨x, rfl, fun h => hx (by simp [h])⟩

/-- Frobenius reciprocity with values in the finite-support maps. -/
def ShFin (n : ℕ) : ResidueHom n (-1) →ₗ[ℚ] StabHomFin n where
  toFun F := ⟨(Sh n F).val, (Sh n F).2, Sh_finiteSupport n F⟩
  map_add' F G := by
    apply Subtype.ext
    change (Sh n (F + G)).val = (Sh n F).val + (Sh n G).val
    rw [map_add]
    rfl
  map_smul' a F := by
    apply Subtype.ext
    change (Sh n (a • F)).val = a • (Sh n F).val
    rw [map_smul]
    rfl

/-- **Shapiro's lemma in the Hom model.**  Frobenius reciprocity
`Hom_G(St, 𝓡_n ⊗ det⁻¹) → Hom_{P_H}(St, 𝓡_{n,H})` is an isomorphism onto the finite-support maps. -/
def shapiroEquiv (n : ℕ) : ResidueHom n (-1) ≃ₗ[ℚ] StabHomFin n :=
  LinearEquiv.ofBijective (ShFin n) ⟨fun F G h => Sh_injective n (by
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h'),
    fun φ => ⟨invShapiro n φ.2.1 φ.2.2, Subtype.ext (Sh_invShapiro n φ.2.1 φ.2.2)⟩⟩

theorem shapiroEquiv_apply (n : ℕ) (F : ResidueHom n (-1)) :
    ((shapiroEquiv n F : StabHomFin n) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResidueFiber n (axis 0))
      = (Sh n F).val := rfl

/-- `κ` is injective on the finite-support maps (the image of Frobenius reciprocity). -/
theorem kappa_injective_on_fin (n : ℕ) (φ ψ : StabHomFin n)
    (h : kappa n ⟨φ.1, φ.2.1⟩ = kappa n ⟨ψ.1, ψ.2.1⟩) : φ = ψ := by
  obtain ⟨F, rfl⟩ := (shapiroEquiv n).surjective φ
  obtain ⟨G, rfl⟩ := (shapiroEquiv n).surjective ψ
  have h1 : (⟨((shapiroEquiv n F : StabHomFin n) : _), (shapiroEquiv n F).2.1⟩ : StabHom n) = Sh n F :=
    Subtype.ext rfl
  have h2 : (⟨((shapiroEquiv n G : StabHomFin n) : _), (shapiroEquiv n G).2.1⟩ : StabHom n) = Sh n G :=
    Subtype.ext rfl
  rw [h1, h2, kappa_Sh, kappa_Sh] at h
  rw [OrdinaryResidueSymbol.toBinaryHom_injective n h]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
