module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Assembly

@[expose] public section


/-!
# Conventions of `eq:Hecke-formula`: the dictionary between the paper's right modules and the left modules used here

Formalized by Claude Sonnet 5.5.
Paper: `eq:Hecke-formula`, Appendix `app:Hecke-coordinate`
(`D_d = ℚ[b,c]_d` "with the right substitution action", the fibre action `q ↦ det(C) q(C(b,c))`, "right homology acts
on `H₂(U, ℚ)` by inverse conjugation"), and "The Hecke transfer" (the matrices `(b c p)`, `(a p 0)`, `diag(p,1,1)`
"classify index-`p` column lattices").

**Dictionary.**  The paper's modules are right modules (`q · C = q(C(b,c))`, residue fibre `q ↦ det(C) q(C(b,c))`).  A right
module `M` becomes the left module `ρ(g) m = m · g⁻¹` used throughout this development:

* `binMod_right_action`: `(binMod d).ρ (C⁻¹) q = q(C(b,c))` (right substitution), `binMod d = homogeneousAction d 0`;
* `fibre_right_action`: the fibre coefficient map of the `P_H`-correspondences, `fibreMap n`, satisfies
  `fiberLin (fibreMap n C⁻¹ a) = det(C) · (fiberLin a)(C(b,c))`, i.e. the paper's `q ↦ det(C) q(C(b,c))`, for every
  rational `C ∈ GL₂(ℚ)`; thus `R_n ⊗ det` (right) is `integralResidueAction n (-1)` (left).
* For a right module the Hecke operator of `Γ g Γ` on coinvariants `M_Γ` is `[m] ↦ ∑_{hΓ ⊂ ΓgΓ} [m · h]` (sum over LEFT cosets, i.e.
  column lattices, which are the cosets classified by the paper's matrices).  With `ρ(h) = (· h⁻¹)` this is
  `[m] ↦ ∑_{Γ y ⊂ Γ g⁻¹ Γ} [ρ(y) m]` (right cosets of the inverse double coset): the homology Hecke operator `heckeOp D M` of the
  datum of `g⁻¹`.  Hence the paper's `T₃(p,1)` (double coset of `diag(1,1,p)`, equivalently `diag(p,1,1)`) is `heckeOp (primeDatum p)`
  (the datum of `diag(p,1,1)⁻¹`), and the paper's `T₂(p)` (`ΓdiagΓ(1,p)`, matrices `C_c = (1 0; c p)`, `C_∞ = diag(p,1)`) is
  `heckeOp (binDatum p)` (the datum of `diag(1/p, 1)`), with no extra scalar.
* Consistently, the radical computations use the inverses: `S ∩ U = {u | λ⁻¹ C u ∈ ℤ²}` for the datum of `g⁻¹` is the paper's
  `U_t = ℤ² ∩ (C/λ)ℤ²`, whence `e_t = [ℤ²:U_t]` is `p` for the `λ = 1` families (`card_RC_U1`) and `1` for `diag(p,1,1)` (where
  `f₃ : u ↦ pu` contributes `λ² = p²`, `kappaLit_f3`).

**If instead one reads `T₂(p)` as the left-module operator `T_*(diag(1,p))`** (sum over right cosets `Γ diag(1,p) x` acting by
`ρ(y)`), then `hecke2_usual`: `T₂ = p^d T_*(diag(1,p))` (`d = n+1`), so the identity of `hecke_formula_literal` would read
`p^{d+1}` instead of `p` in front of that operator.  This is recorded, not absorbed: the proved statement is the one for the
right-module reading above.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open CategoryTheory TernaryPoly TernaryPoly.OrdinaryResidueParabolic TernaryPeriodPolynomials.Argument.FareyTree
open TernaryPeriodPolynomials.Argument.GroupHomology MvPolynomial TernaryPeriodPolynomials.Argument.AppendixBResidue

theorem bind₁_smul_homogeneous (c : ℚ) (n : ℕ) (q : MvPolynomial (Fin 2) ℚ) (hq : q.IsHomogeneous n) :
    bind₁ (fun i : Fin 2 => C c * X i) q = C (c ^ n) * q := by
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := hq (mem_support_iff.mp hm)
  have hs : ∑ i ∈ m.support, m i = n := by
    rw [← hd]
    simp [Finsupp.weight_apply, Finsupp.sum]
  have hP : ∏ x ∈ m.support, (C (c ^ m x) : MvPolynomial (Fin 2) ℚ) = C (c ^ n) := by
    rw [← map_prod, Finset.prod_pow_eq_pow_sum, hs]
  rw [bind₁_monomial, monomial_eq]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, hP]
  rw [Finsupp.prod]
  ring

variable (p : ℕ) [Fact p.Prime]

/-- `diag(1, p) ∈ GL₂(ℚ)`. -/
def Cp : GL2 :=
  ⟨!![1, 0; 0, (p : ℚ)], !![1, 0; 0, (p : ℚ)⁻¹],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp]⟩

/-- The central scalar `p⁻¹ · I ∈ GL₂(ℚ)`. -/
def zS : GL2 :=
  ⟨!![(p : ℚ)⁻¹, 0; 0, (p : ℚ)⁻¹], !![(p : ℚ), 0; 0, (p : ℚ)],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp],
    by
      have hp := p_ne_zero_rat p
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp]⟩

theorem zS_central (a : GL2) : zS p * a = a * zS p := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zS, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem C1_eq : C1 p = zS p * Cp p := by
  have hp := p_ne_zero_rat p
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C1, zS, Cp, Matrix.mul_apply, Fin.sum_univ_two, hp]

/-- The scalar `p⁻¹ I` acts on binary forms of degree `d` (trivial determinant twist) by `p^d`. -/
theorem binMod_zS (d : ℕ) (w : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    (binMod d).ρ (zS p) w = (p : ℚ) ^ d • w := by
  rw [binMod_apply]
  apply Subtype.ext
  have hw : w.1.IsHomogeneous d := (mem_homogeneousSubmodule d w.1).mp w.2
  have e := bind₁_smul_homogeneous (p : ℚ) d w.1 hw
  change binarySubstitute ((zS p)⁻¹).val w.1 = _
  have : binarySubstitute ((zS p)⁻¹).val = bind₁ (fun i : Fin 2 => C (p : ℚ) * X i) := by
    unfold binarySubstitute
    congr 1
    funext i
    fin_cases i <;> simp [zS, Fin.sum_univ_two]
  rw [this, e]
  simp [Algebra.smul_def]

theorem hf_Cp (s : ↥(binDatum p).S) : binIota ((binDatum p).f s) = Cp p * binIota s.1 * (Cp p)⁻¹ := by
  have key : ∀ a : GL2, C1 p * a * (C1 p)⁻¹ = Cp p * a * (Cp p)⁻¹ := by
    intro a
    rw [C1_eq]
    have hc : ∀ x : GL2, zS p * x = x * zS p := zS_central p
    calc zS p * Cp p * a * (zS p * Cp p)⁻¹
        = zS p * (Cp p * a * (Cp p)⁻¹) * (zS p)⁻¹ := by group
      _ = (Cp p * a * (Cp p)⁻¹) * zS p * (zS p)⁻¹ := by rw [hc]
      _ = Cp p * a * (Cp p)⁻¹ := by group
  rw [(binDatum p).hf s]
  exact key _

section Scalar

variable {H G : Type} [Group H] [Group G] (f : H →* G) {A : Rep.{0} ℚ H} {B : Rep.{0} ℚ G}

theorem chainsMap_smul' (r : ℚ) (c : A ⟶ Rep.res f B) :
    groupHomology.chainsMap f (r • c) = r • groupHomology.chainsMap f c := by
  ext i x a
  simp [Rep.smul_hom]

theorem map_smul'' (r : ℚ) (c : A ⟶ Rep.res f B) (n : ℕ) :
    groupHomology.map f (r • c) n = r • groupHomology.map f c n := by
  unfold groupHomology.map
  rw [chainsMap_smul']
  exact homologyMap_smul' _ _ _

end Scalar

/-- The transport `m ↦ g' m` as a morphism `Res_S M → Res_f M`, for any `g'` conjugating `ι ∘ j` into `ι ∘ f`. -/
def corrMapG {Γ Ĝ : Type} [Group Γ] [Group Ĝ] {ι : Γ →* Ĝ} {g : Ĝ} (D : HeckeDatum ι g) (g' : Ĝ)
    (hf' : ∀ s : D.S, ι (D.f s) = g' * ι s * g'⁻¹) (M : Rep.{0} ℚ Ĝ) :
    Rep.res D.S.subtype (Rep.res ι M) ⟶ Rep.res D.f (Rep.res ι M) :=
  Rep.ofHom ⟨M.ρ g', fun s => by
    ext a
    change M.ρ g' (M.ρ (ι s.1) a) = M.ρ (ι (D.f s)) (M.ρ g' a)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hf' s]
    congr 1
    group⟩

/-- The Hecke operator of the datum `D` with the transport element `g'` in place of `g`. -/
def heckeOpG {Γ Ĝ : Type} [Group Γ] [Group Ĝ] {ι : Γ →* Ĝ} {g : Ĝ} (D : HeckeDatum ι g) (g' : Ĝ)
    (hf' : ∀ s : D.S, ι (D.f s) = g' * ι s * g'⁻¹) (M : Rep.{0} ℚ Ĝ) (n : ℕ) :
    groupHomology (Rep.res ι M) n ⟶ groupHomology (Rep.res ι M) n :=
  haveI := D.finiteIndex
  trR D.S (Rep.res ι M) n ≫ groupHomology.map D.f (corrMapG D g' hf' M) n

theorem heckeOpG_self {Γ Ĝ : Type} [Group Γ] [Group Ĝ] {ι : Γ →* Ĝ} {g : Ĝ} (D : HeckeDatum ι g) (M : Rep.{0} ℚ Ĝ)
    (n : ℕ) : heckeOpG D g D.hf M n = heckeOp D M n := rfl

theorem corrMapG_C1 (d : ℕ) :
    corrMapG (binDatum p) (C1 p) (binDatum p).hf (binMod d) =
      (p : ℚ) ^ d • corrMapG (binDatum p) (Cp p) (hf_Cp p) (binMod d) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun w => ?_
  rw [Rep.smul_hom]
  change (binMod d).ρ (C1 p) w = (p : ℚ) ^ d • (binMod d).ρ (Cp p) w
  rw [C1_eq, map_mul]
  exact binMod_zS p d _

/-- **`T₂(p) = p^d · T_*(diag(1, p))`.**  The homology Hecke operator `heckeOp (binDatum p) (binMod d) 1` of `diag(1/p, 1)`
on `H₁(GL₂(ℤ), Sym^d)` (coefficients `homogeneousAction d 0`) is `p^d` times the operator with the same cosets and transport by
`diag(1, p)`. -/
theorem hecke2_usual (d : ℕ) (x : groupHomology (Dplain d) 1) :
    (heckeOp (binDatum p) (binMod d) 1).hom x =
      (p : ℚ) ^ d • (heckeOpG (binDatum p) (Cp p) (hf_Cp p) (binMod d) 1).hom x := by
  rw [← heckeOpG_self, heckeOpG, heckeOpG, corrMapG_C1, map_smul'']
  rfl


theorem binMod_right_action (d : ℕ) (C : GL2) (q : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    (binMod d).ρ C⁻¹ q = homogeneousBinarySubstitute d C.val q := by
  rw [binMod_apply, inv_inv]

theorem fibre_right_action (n : ℕ) (C : GL2) (a : (FibRep n).V) :
    fiberLin n (fibreMap n C⁻¹ a) = (C.val.det) • homogeneousBinarySubstitute (n + 1) C.val (fiberLin n a) := by
  rw [fiberLin_fibreMap, inv_inv]
  have : ((C⁻¹ : GL2).val).det = (C.val.det)⁻¹ := by
    simp [Matrix.det_nonsing_inv]
  rw [this, inv_inv]

end TernaryPeriodPolynomials.Argument.HeckeHomology
