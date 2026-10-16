module

public import TernaryPeriodPolynomials.BoundaryComparison.RadicalCohomologyTables
public import TernaryPeriodPolynomials.BoundaryComparison.AlternatingEven

@[expose] public section


/-!
# The cohomology tables of the plane radical `N_P` for the determinant-twisted coefficients `E_{n,e} = Sym^n((ℚ³)*) ⊗ det^e`

Formalized by Claude Sonnet 5.5.  Proof of Proposition `thm:J-vanishes`,:
`H¹(N_P,E_n) = det⁻¹ Sym^{n+1}((ℚ²)*)`, `H²(N_P,E_n) = det⁻² Sym^n((ℚ²)*)`, "the two opposite binary unipotents have no common invariant in positive degree".

The library's tables `plane_radical_H1`, `plane_radical_H2` (`Exports/RadicalCohomologyTables`, `Exports/AlternatingEven`) are for the untwisted coefficients `E_{n,0} = Sym^n((ℚ³)*)` (`integralAction n 0`).
The paper's `E_n` is `E_{n,-1} = Sym^n ⊗ det⁻¹` (`integralAction n (-1)`; `rationalCoefficientComponent n trivialCharacter` on `GL₃(ℤ)`).  Here, for every exponent `e ∈ ℤ`:

* `integralAction_twist`: `ρ_e(g) = det(g)^e • ρ_0(g)` for `g ∈ GL₃(ℤ)`; on the plane radical `det = 1`, so `E_{n,e}|_{N_P} = E_{n,0}|_{N_P}` (`planeRep_twist`) and `H^i(N_P,E_{n,e})` is the same group;
* `planeCoefficientHomT n e M`, `planeH1ActionT`, `planeH2ActionT`: the genuine conjugation action of the Levi element `diag(M,1) ∈ GL₂(ℤ)` on `H^i(N_P, E_{n,e})`
  (`groupCohomology.map` along the inverse lattice conjugation with the coefficient map `ρ_e(diag(M,1))`);
* `plane_radical_H1_twisted`: `H¹(N_P,E_{n,e}) ≅ det^e Sym^{n+1}(x,y)*` as `GL₂(ℤ)`-modules; `plane_radical_H2_twisted`: `H²(N_P,E_{n,e}) ≅ det^{e-1} Sym^n(x,y)*`;
  for `e = -1` these are the displayed formulas of the paper, for `e = 0` the existing tables;
* `plane_H2_fixed_zero_twisted`: for `n > 0` and every `e`, a class of `H²(N_P,E_{n,e})` fixed by the whole Levi `GL₂(ℤ)` is zero: only the two opposite unipotents (determinant `1`) are used.
-/

open CategoryTheory Matrix MvPolynomial
open TernaryPoly TernaryPoly.RadicalFirstCohomology TernaryPoly.RadicalTopCohomology
open TernaryPoly.LatticeTopCohomology TernaryPoly.RadicalFirstCohomologyLattice TernaryPoly.RadicalCoinvariantAlgebra
open TernaryPoly.RelativeStabilizerParameters TernaryPoly.RelativeStabilizerMatrices
open TernaryPoly.PolynomialGLAction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.BadPlane

/-- The determinant character `det^e` of `GL₂(ℤ)` with values in `ℚ`. -/
def detChar (e : ℤ) (A : GL2) : ℚ := ((A.val.det : ℤ) : ℚ) ^ e

theorem integralAction_twist (n : ℕ) (e : ℤ) (g : ModThreeGoodAction.IntegralGL) :
    integralAction n e g = (((g.val.det : ℤ) : ℚ) ^ e) • integralAction n 0 g := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  have hdet : determinantCharacter e (GeneralLinearGroup.map (Int.castRingHom ℚ) g) =
      ((g.val.det : ℤ) : ℚ) ^ e := by
    change ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℚ) g) : ℚˣ) : ℚ) ^ e = _
    congr 1
    simp [Matrix.GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (Int.castRingHom ℚ) g.val).symm
  rw [LinearMap.smul_apply, Submodule.coe_smul, integralAction_coe, integralAction_coe, action_apply,
    action_apply, hdet]
  have h0 : determinantCharacter 0 (GeneralLinearGroup.map (Int.castRingHom ℚ) g) = 1 := by
    simp [determinantCharacter]
  rw [h0, one_smul]

theorem det_planeElement (A : GL2) (u : Fin 2 → ℤ) : (planeElement A u).val.det = A.val.det := by
  rw [planeElement_val, det_planeMatrix]


/-- On the plane radical the determinant is one: the radical module of `E_{n,e}` is the radical module of `E_{n,0}`. -/
theorem planeRep_twist (n : ℕ) (e : ℤ) (g : Lattice) :
    integralAction n e (planeHom g) = integralAction n 0 (planeHom g) := by
  have h : ((planeHom g).val.det : ℤ) = 1 := by
    change (planeElement 1 ![g.toAdd.1, g.toAdd.2]).val.det = 1
    rw [det_planeElement]
    simp
  rw [integralAction_twist n e (planeHom g), h]
  simp

/-- The coefficient morphism of the Levi element `diag(M,1)` acting on `H^*(N_P, E_{n,e})`: `ρ_e(diag(M,1))`, over the inverse lattice conjugation. -/
def planeCoefficientHomT (n : ℕ) (e : ℤ) (M : GL2) :
    Rep.res (matrixLattice M⁻¹).toMonoidHom (planeRep n) ⟶ planeRep n :=
  Rep.ofHom ⟨integralAction n e (planeElement M 0), fun g => by
    change integralAction n e (planeElement M 0) *
      integralAction n 0 (planeHom (matrixLattice M⁻¹ g)) =
      integralAction n 0 (planeHom g) * integralAction n e (planeElement M 0)
    rw [integralAction_twist n e (planeElement M 0), smul_mul_assoc, mul_smul_comm,
      ← map_mul, ← map_mul, plane_inverse_commute]⟩

/-- The Levi action on `H¹(N_P, E_{n,e})`. -/
def planeH1ActionT (n : ℕ) (e : ℤ) (M : GL2) :
    groupCohomology (planeRep n) 1 ⟶ groupCohomology (planeRep n) 1 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHomT n e M) 1

/-- The Levi action on `H²(N_P, E_{n,e})`. -/
def planeH2ActionT (n : ℕ) (e : ℤ) (M : GL2) :
    groupCohomology (planeRep n) 2 ⟶ groupCohomology (planeRep n) 2 :=
  groupCohomology.map (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHomT n e M) 2

theorem planeH1ActionT_eq (n : ℕ) (e : ℤ) (M : GL2) (x : groupCohomology (planeRep n) 1) :
    planeH1ActionT n e M x = detChar e M • planeH1Action n M x := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  unfold planeH1ActionT planeH1Action
  rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_comp_map_apply, ← map_smul]
  congr 1
  apply Subtype.ext
  funext g
  change integralAction n e (planeElement M 0) (c (matrixLattice M⁻¹ g)) =
    detChar e M • integralAction n 0 (planeElement M 0) (c (matrixLattice M⁻¹ g))
  rw [integralAction_twist, LinearMap.smul_apply, det_planeElement]
  rfl

theorem planeH2ActionT_eq (n : ℕ) (e : ℤ) (M : GL2) (x : groupCohomology (planeRep n) 2) :
    planeH2ActionT n e M x = detChar e M • planeH2Action n M x := by
  refine groupCohomology.H2_induction_on x ?_
  intro c
  unfold planeH2ActionT planeH2Action
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, ← map_smul]
  congr 1
  apply Subtype.ext
  funext g
  change integralAction n e (planeElement M 0) (c ((matrixLattice M⁻¹) g.1, (matrixLattice M⁻¹) g.2)) =
    detChar e M • integralAction n 0 (planeElement M 0) (c ((matrixLattice M⁻¹) g.1, (matrixLattice M⁻¹) g.2))
  rw [integralAction_twist, LinearMap.smul_apply, det_planeElement]
  rfl


/-- **`H¹(N_P, E_{n,e}) ≅ det^e Sym^{n+1}(x,y)*`** as `GL₂(ℤ)`-modules (inverse substitution times `det^e`);
`e = -1` is the paper's `E_n`, `e = 0` the existing table `plane_radical_H1`. -/
theorem plane_radical_H1_twisted (n : ℕ) (e : ℤ) :
    ∃ iso : groupCohomology (planeRep n) 1 ≃ₗ[ℚ] BinaryH (n + 1),
      ∀ (A : GL2) (v : groupCohomology (planeRep n) 1),
        (iso (planeH1ActionT n e A v) : MvPolynomial (Fin 2) ℚ) =
          detChar e A • binaryMatrixSubst (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
            (iso v : MvPolynomial (Fin 2) ℚ) := by
  obtain ⟨iso, -, h⟩ := Statements.RadicalCohomologyTables.plane_radical_H1 n
  exact ⟨iso, fun A v => by rw [planeH1ActionT_eq, map_smul, Submodule.coe_smul, h]⟩

theorem detChar_sub_one (e : ℤ) (A : GL2) :
    detChar (e - 1) A = detChar e A * ((A.val.det : ℚ))⁻¹ := by
  unfold detChar
  have hne : ((A.val.det : ℤ) : ℚ) ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det A.val).mp A.isUnit).ne_zero
    exact_mod_cast this
  rw [zpow_sub_one₀ hne]

/-- **`H²(N_P, E_{n,e}) ≅ det^{e-1} Sym^n(x,y)*`** as `GL₂(ℤ)`-modules; `e = -1` gives the paper's `H²(N_P,E_n) = det⁻² Sym^n`. -/
theorem plane_radical_H2_twisted (n : ℕ) (e : ℤ) :
    ∃ iso : groupCohomology (planeRep n) 2 ≃ₗ[ℚ] BinaryH n,
      ∀ (A : GL2) (v : groupCohomology (planeRep n) 2),
        (iso (planeH2ActionT n e A v) : MvPolynomial (Fin 2) ℚ) =
          detChar (e - 1) A • binaryMatrixSubst (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
            (iso v : MvPolynomial (Fin 2) ℚ) := by
  obtain ⟨iso, h⟩ := Statements.AlternatingEven.plane_radical_H2 n
  refine ⟨iso, fun A v => ?_⟩
  rw [planeH2ActionT_eq, map_smul, Submodule.coe_smul, h, smul_smul, detChar_sub_one]

theorem det_binaryUpper : (binaryUpper.val.det : ℤ) = 1 := by
  rw [Matrix.det_fin_two]
  simp [binaryUpper]

theorem det_binaryLower : (binaryLower.val.det : ℤ) = 1 := by
  rw [Matrix.det_fin_two]
  simp [binaryLower]

/-- **(b): the second module has no `L_P`-invariants in positive degree.**  For `n > 0` and every twist `e`, a class of `H²(N_P, E_{n,e})` fixed by the whole Levi `GL₂(ℤ)` is
zero; only the two opposite binary unipotents (determinant one) are used. -/
theorem plane_H2_fixed_zero_twisted (n : ℕ) (hn : 0 < n) (e : ℤ) (v : groupCohomology (planeRep n) 2)
    (hv : ∀ M : GL2, planeH2ActionT n e M v = v) : v = 0 := by
  obtain ⟨iso, h⟩ := plane_radical_H2_twisted n e
  apply iso.injective
  rw [map_zero]
  apply binary_transvections_fixed_zero hn (iso v)
  · have h1 := h binaryUpper v
    rw [hv, binaryUpper_substitute] at h1
    have h2 : detChar (e - 1) binaryUpper = 1 := by simp [detChar, det_binaryUpper]
    rw [h2, one_smul] at h1
    exact h1.symm
  · have h1 := h binaryLower v
    rw [hv, binaryLower_substitute] at h1
    have h2 : detChar (e - 1) binaryLower = 1 := by simp [detChar, det_binaryLower]
    rw [h2, one_smul] at h1
    exact h1.symm

end TernaryPeriodPolynomials.Argument.Identities.BadPlane
