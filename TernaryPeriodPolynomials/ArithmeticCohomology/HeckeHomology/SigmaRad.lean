module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaEntries
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.RadicalTransfer

@[expose] public section


/-!
# The radical data of the `σ`-correspondence: `μ = diag(p, 1)`, the index `p`, and the determinant `p`

Formalized by Claude Sonnet 5.5.
Paper: "the radical quotient has `p` elements,
represented by `(0,b)` ... Thus `e_t = p`".

For `S = P_H ∩ σ⁻¹ S_p σ`, the group `S ∩ U ≤ U ≅ ℤ²` is `{u | p ∣ u₀}` of index `p`, the map `f₁ = ν` sends `(u₀, u₁) ↦ (u₀/p, u₁)`
and `μ = diag(p, 1)` satisfies `μ ∘ ν = incl`.  Hence the hypotheses `hμ`, `hω`, `hne` of `hsFarey_corr` hold for `ω(μ) = p = [U : S ∩ U]`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.HochschildSerre

variable {p : ℕ} [Fact p.Prime]

/-- `f₁` maps `S ∩ U` into `U`. -/
theorem f1_mem_U (h : ↥(Psig p)) (hh : (h : PH) ∈ AppendixBResidue.U) : f1 (p := p) h ∈ AppendixBResidue.U := by
  have hp : (p : ℤ) ≠ 0 := p_ne_zero_int
  have hpi : pi (h : PH) = 1 := hh.1
  have hlam : lamHom (h : PH) = 1 := hh.2
  have e00 : h.1.1.val 0 0 = 1 := by
    have : ((lamHom (h : PH) : ℤˣ) : ℤ) = 1 := by rw [hlam]; rfl
    exact this
  have e11 : h.1.1.val 1 1 = 1 := by
    have := congrArg (fun m : GL2Z => m.val 0 0) hpi
    simpa [pi_val, blockMat] using this
  have e12 : h.1.1.val 1 2 = 0 := by
    have := congrArg (fun m : GL2Z => m.val 0 1) hpi
    simpa [pi_val, blockMat] using this
  have e21 : h.1.1.val 2 1 = 0 := by
    have := congrArg (fun m : GL2Z => m.val 1 0) hpi
    simpa [pi_val, blockMat] using this
  have e22 : h.1.1.val 2 2 = 1 := by
    have := congrArg (fun m : GL2Z => m.val 1 1) hpi
    simpa [pi_val, blockMat] using this
  have a00 : ((f1 (p := p) h : PH) : IntegralGL).val 0 0 = 1 := by rw [f1_val_00, e00]
  have a11 : ((f1 (p := p) h : PH) : IntegralGL).val 1 1 = 1 := by rw [f1_val_11, e11]
  have a12 : ((f1 (p := p) h : PH) : IntegralGL).val 1 2 = 0 := by
    have := f1_val_12 h
    rw [e12] at this
    exact (mul_eq_zero.mp this).resolve_right hp
  have a21 : ((f1 (p := p) h : PH) : IntegralGL).val 2 1 = 0 := by rw [f1_val_21, e21]; simp
  have a22 : ((f1 (p := p) h : PH) : IntegralGL).val 2 2 = 1 := by rw [f1_val_22, e22]
  rw [mem_U]
  refine ⟨?_, ?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pi_val, blockMat, a11, a12, a21, a22]
  · apply Units.ext
    exact a00

section Mu

open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

theorem eU_symm_apply (u : AppendixBResidue.U) :
    AppendixBResidue.eU.symm u = Multiplicative.ofAdd (uvec u.1) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  symm
  show radPH (Multiplicative.ofAdd (uvec u.1)) = u.1
  apply PH_ext
  · rw [lam_radPH]; exact u.2.2.symm
  · rw [pi_radPH]; exact u.2.1.symm
  · rw [uvec_radPH]; rfl

/-- The dilation `(u₀, u₁) ↦ (p u₀, u₁)` of `ℤ²`. -/
def dilA (p : ℕ) : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun v := ![(p : ℤ) * v 0, v 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp [mul_add]

def dilM (p : ℕ) : Multiplicative (Fin 2 → ℤ) →* Multiplicative (Fin 2 → ℤ) :=
  AddMonoidHom.toMultiplicative (dilA p)

/-- The rational inverse `μ = diag(p, 1)` of the radical part of `f₁`, as an endomorphism of `U`. -/
def muRad (p : ℕ) : AppendixBResidue.U →* AppendixBResidue.U :=
  AppendixBResidue.eU.toMonoidHom.comp ((dilM p).comp AppendixBResidue.eU.symm.toMonoidHom)

theorem toAdd_dilM (p : ℕ) (v : Multiplicative (Fin 2 → ℤ)) :
    Multiplicative.toAdd (dilM p v) = ![(p : ℤ) * Multiplicative.toAdd v 0, Multiplicative.toAdd v 1] := rfl

omit [Fact p.Prime] in
theorem muPsi_muRad (v : Multiplicative (Fin 2 → ℤ)) :
    muPsi AppendixBResidue.eU (muRad p) v = dilM p v := by
  simp [muPsi, muRad]

omit [Fact p.Prime] in
theorem omega_muRad :
    (omegaZ (muPsi AppendixBResidue.eU (muRad p) HochschildSerre.e1)
      (muPsi AppendixBResidue.eU (muRad p) HochschildSerre.e2) : ℚ) = (p : ℚ) := by
  rw [muPsi_muRad, muPsi_muRad]
  have : (omegaZ (dilM p HochschildSerre.e1) (dilM p HochschildSerre.e2) : ℤ) = p := by
    simp [omegaZ, dilM, dilA, HochschildSerre.e1, HochschildSerre.e2]
  exact_mod_cast this

theorem muRad_nuU (hfU : ∀ s : ↥(Psig p), (s : PH) ∈ AppendixBResidue.U → f1 (p := p) s ∈ AppendixBResidue.U)
    (n : U1 AppendixBResidue.U (Psig p)) :
    muRad p (nuU AppendixBResidue.U (Psig p) (f1 (p := p)) hfU n) = (n : AppendixBResidue.U) := by
  apply AppendixBResidue.eU.symm.injective
  have h1 : AppendixBResidue.eU.symm (muRad p (nuU AppendixBResidue.U (Psig p) (f1 (p := p)) hfU n)) =
      dilM p (AppendixBResidue.eU.symm (nuU AppendixBResidue.U (Psig p) (f1 (p := p)) hfU n)) := by
    simp [muRad]
  rw [h1, eU_symm_apply, eU_symm_apply]
  have h10 := f1_val_10 (p := p) (incl1 AppendixBResidue.U (Psig p) n)
  have h20 := f1_val_20 (p := p) (incl1 AppendixBResidue.U (Psig p) n)
  apply Multiplicative.toAdd.injective
  rw [toAdd_dilM, toAdd_ofAdd, toAdd_ofAdd]
  funext i
  fin_cases i
  · show (p : ℤ) * ((f1 (p := p) (incl1 AppendixBResidue.U (Psig p) n) : PH) : IntegralGL).val 1 0 =
      ((n : AppendixBResidue.U) : PH).1.val 1 0
    rw [mul_comm]
    exact h10
  · show ((f1 (p := p) (incl1 AppendixBResidue.U (Psig p) n) : PH) : IntegralGL).val 2 0 =
      ((n : AppendixBResidue.U) : PH).1.val 2 0
    exact h20

end Mu

section Count

/-- `u ↦ u₀ mod p`, a homomorphism `U → ℤ/p`. -/
def u0A (p : ℕ) : (Fin 2 → ℤ) →+ ZMod p :=
  (Int.castAddHom (ZMod p)).comp (Pi.evalAddMonoidHom (fun _ : Fin 2 => ℤ) 0)

def u0mod (p : ℕ) : AppendixBResidue.U →* Multiplicative (ZMod p) :=
  (AddMonoidHom.toMultiplicative (u0A p)).comp AppendixBResidue.eU.symm.toMonoidHom

theorem U1_eq_ker : U1 AppendixBResidue.U (Psig p) = (u0mod p).ker := by
  ext u
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  change ((u : AppendixBResidue.U) : PH) ∈ Sx PH (primeDatum p).S sigma ↔ _
  rw [mem_Sx_sigma_iff]
  have h12 : ((u : AppendixBResidue.U) : PH).1.val 1 2 = 0 := by
    have := congrArg (fun m : GL2Z => m.val 0 1) u.2.1
    simpa [pi_val, blockMat] using this
  have h0 : u0mod p u = Multiplicative.ofAdd (((uvec ((u : AppendixBResidue.U) : PH) 0 : ℤ) : ZMod p)) := by
    simp [u0mod, u0A, eU_symm_apply]
  rw [h0, h12]
  constructor
  · rintro ⟨h, -⟩
    exact (ofAdd_eq_one).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  · intro h
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (ofAdd_eq_one.mp h), dvd_zero _⟩

theorem u0mod_surjective : Function.Surjective (u0mod p) := by
  intro t
  refine ⟨AppendixBResidue.eU (Multiplicative.ofAdd ![((Multiplicative.toAdd t).val : ℤ), 0]), ?_⟩
  simp [u0mod, u0A]

theorem card_RC_U1 : Fintype.card (RC (U1 AppendixBResidue.U (Psig p))) = p := by
  rw [← Nat.card_eq_fintype_card]
  have e : Nat.card (RC (U1 AppendixBResidue.U (Psig p))) = (U1 AppendixBResidue.U (Psig p)).index :=
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)
  rw [e, U1_eq_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (u0mod_surjective (p := p)),
    Subgroup.card_top]
  simp

end Count

end TernaryPeriodPolynomials.Argument.HeckeHomology
