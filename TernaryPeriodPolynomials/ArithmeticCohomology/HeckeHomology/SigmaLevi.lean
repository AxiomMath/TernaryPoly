module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.SigmaRad
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke

@[expose] public section


/-!
# The Levi part of the `σ`-correspondence is the binary Hecke correspondence

Formalized by Claude Sonnet 5.5.
Paper: "the second family has binary block
`C_∞ = diag(p, 1)`"; the correspondence acts on the residue fibre through the binary block, so on `H₁(GL₂(ℤ), -)` it is the binary
Hecke operator `T₂(p)` of `diag(1/p, 1)`.

* `pi_f1_val`: the Levi block of `f₁(h)` is `(d₀₀, d₀₁/p; p d₁₀, d₁₁)`, the matrix `cjMat p` of the binary datum;
* `G0_mem_iff`: the image `Γ₀` of `P_H ∩ σ⁻¹ S_p σ` in `P_H / U` is the preimage of `{k | p ∣ k₀₁}` under `pibar`;
* `pibar_chi`: the map induced by `f₁` on `Γ₀` lifts the binary Hecke map `(binDatum p).f`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPoly.OrdinaryResidueParabolic TernaryPeriodPolynomials.Argument.FareyTree

variable {p : ℕ} [Fact p.Prime]

theorem pi_f1_val (s : ↥(Psig p)) :
    (pi (f1 (p := p) s)).val = cjMat p (pi s.1).val := by
  have hp : (p : ℤ) ≠ 0 := p_ne_zero_int
  ext i j
  fin_cases i <;> fin_cases j
  · change ((f1 (p := p) s : PH) : IntegralGL).val 1 1 = s.1.1.val 1 1
    rw [f1_val_11]
  · change ((f1 (p := p) s : PH) : IntegralGL).val 1 2 = s.1.1.val 1 2 / p
    have := f1_val_12 s
    rw [← this, Int.mul_ediv_cancel _ hp]
  · change ((f1 (p := p) s : PH) : IntegralGL).val 2 1 = p * s.1.1.val 2 1
    rw [f1_val_21]
  · change ((f1 (p := p) s : PH) : IntegralGL).val 2 2 = s.1.1.val 2 2
    rw [f1_val_22]

theorem pibar_piS (s : ↥(Psig p)) :
    pibar ((piS AppendixBResidue.U (Psig p) s : G0 AppendixBResidue.U (Psig p)) : PH ⧸ AppendixBResidue.U) = pi s.1 := rfl

theorem pibar_chi (hfU : ∀ s : ↥(Psig p), (s : PH) ∈ AppendixBResidue.U → f1 (p := p) s ∈ AppendixBResidue.U)
    (hGamma : ∀ q, q ∈ G0 AppendixBResidue.U (Psig p) ↔ pibar q ∈ (binDatum p).S)
    (g : G0 AppendixBResidue.U (Psig p)) :
    pibar (chi AppendixBResidue.U (Psig p) (f1 (p := p)) hfU g) = (binDatum p).f ⟨pibar g, (hGamma g).mp g.2⟩ := by
  obtain ⟨s, rfl⟩ := piS_surjective AppendixBResidue.U (Psig p) g
  rw [chi_piS, pibar_mk]
  apply Units.ext
  rw [binDatum_f_val]
  exact pi_f1_val s


section Gamma

open AppendixBResidue in
/-- `rad(-λ u) · g`: the element of `g U` with vanishing radical column. -/
def adjPH (g : PH) : PH :=
  radPH (Multiplicative.ofAdd (fun i => -((lamHom g : ℤˣ) : ℤ) * uvec g i)) * g

theorem adjPH_val_10 (g : PH) : (adjPH g).1.val 1 0 = 0 := by
  have hl := lam_cases g
  have e : (adjPH g).1.val 1 0 =
      (-((lamHom g : ℤˣ) : ℤ) * uvec g 0) * g.1.val 0 0 + g.1.val 1 0 := by
    change ((radPH (Multiplicative.ofAdd (fun i => -((lamHom g : ℤˣ) : ℤ) * uvec g i))).1 * g.1).val 1 0 = _
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, radPH_val]
  rw [e]
  have h00 : g.1.val 0 0 = ((lamHom g : ℤˣ) : ℤ) := rfl
  have h10 : g.1.val 1 0 = uvec g 0 := rfl
  rw [h00, h10]
  rcases hl with h | h <;> rw [h] <;> ring

theorem adjPH_pi (g : PH) : pi (adjPH g) = pi g := by
  simp [adjPH, map_mul, pi_radPH]

theorem mk_adjPH (g : PH) : (QuotientGroup.mk (adjPH g) : PH ⧸ AppendixBResidue.U) = QuotientGroup.mk g := by
  unfold adjPH
  rw [QuotientGroup.mk_mul]
  have : (QuotientGroup.mk (radPH (Multiplicative.ofAdd (fun i => -((lamHom g : ℤˣ) : ℤ) * uvec g i))) :
      PH ⧸ AppendixBResidue.U) = 1 := (QuotientGroup.eq_one_iff _).mpr (radPH_mem_U _)
  rw [this, one_mul]

/-- **`Γ₀` is the preimage of the binary Hecke subgroup.** -/
theorem G0_mem_iff (q : PH ⧸ AppendixBResidue.U) :
    q ∈ G0 AppendixBResidue.U (Psig p) ↔ pibar q ∈ (binDatum p).S := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [mem_G0, show (binDatum p).S = commSubgroup binIota (C1 p) from rfl, mem_commSubgroup_C1, pibar_mk]
    constructor
    · rintro ⟨s, hs, hsg⟩
      have h1 : pi s = pi g := by
        have := congrArg pibar hsg
        simpa [pibar_mk] using this
      obtain ⟨_, h12⟩ := (mem_Sx_sigma_iff (p := p) s).mp hs
      have : (pi g).val 0 1 = s.1.val 1 2 := by rw [← h1]; rfl
      rw [this]; exact h12
    · intro hdvd
      refine ⟨adjPH g, ?_, mk_adjPH g⟩
      rw [mem_Sx_sigma_iff]
      refine ⟨by rw [adjPH_val_10]; exact dvd_zero _, ?_⟩
      have : (adjPH g).1.val 1 2 = (pi g).val 0 1 := by rw [← adjPH_pi g]; rfl
      rw [this]; exact hdvd

end Gamma

section Coeff

/-- The rational binary module of binary forms of degree `d` (trivial determinant twist). -/
def binMod (d : ℕ) : Rep.{0} ℚ GL2 := Rep.of (BinaryModularSymbolCoefficients.homogeneousAction d 0)

theorem binMod_res (d : ℕ) : Rep.res binIota (binMod d) = Dplain d := rfl

theorem binMod_apply (d : ℕ) (C : GL2) (w : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    (binMod d).ρ C w = homogeneousBinarySubstitute d (C⁻¹).val w := by
  apply Subtype.ext
  change BinaryModularSymbolCoefficients.action 0 C w.val = _
  rw [BinaryModularSymbolCoefficients.action_apply]
  simp [BinaryModularSymbolCoefficients.determinantCharacter]
  rfl

theorem fiberLin_c1 (n : ℕ) (a : (FibRep n).V) :
    fiberLin n ((c1 p n).hom a) = (p : ℚ) • (binMod (n + 1)).ρ (C1 p) (fiberLin n a) := by
  have hp := p_ne_zero_rat p
  change fiberLin n (fibreMap n (C1 p) a) = _
  rw [fiberLin_fibreMap, binMod_apply]
  have hdet : (C1 p).val.det = (p : ℚ)⁻¹ := by
    simp [C1, Matrix.det_fin_two]
  rw [hdet, inv_inv]
  rfl

end Coeff

end TernaryPeriodPolynomials.Argument.HeckeHomology
