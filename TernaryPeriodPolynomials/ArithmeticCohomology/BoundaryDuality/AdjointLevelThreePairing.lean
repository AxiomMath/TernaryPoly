module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreeHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointConcrete

@[expose] public section


/-!
# The Lefschetz pairing between the bad-line and the good-plane Levi cohomology

The bad-line Levi `Γ₁'(3)` carries `H¹(Γ₁'(3), Sym^{n+1})` and the good-plane Levi carries
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`.  For odd `n` the classical invariant pairing of binary forms
`binaryPairing (n + 1)` pairs the two coefficient systems (`e + e' - m = -(n + 2)` is odd), and the
cup product on the parabolic classes, computed on the fundamental two-chain of the sphere with two
cusps and one cone point, is a bilinear form

  `badGoodPairing : H¹_par(Γ₁'(3), Sym^{n+1}) × H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹) → ℂ`

(the parabolic pairing of `ParabolicDualityLevelThree`).

*Why the pairing lives on parabolic classes on both sides.*  The cup formula of a pair of crossed
homomorphisms `(z, z')` uses a primitive triple `v` of the first one, determined up to a triple `f`
of vectors fixed by `T`, `L`, `(T L⁻¹)⁻¹`.  Changing `v` by `f` changes the value by
`∑ᵢ B(fᵢ, z'(gᵢ))` (`cupFormula_add_fixed`), which vanishes exactly when `z'` takes coboundary values
at the three special elements, i.e. when `z'` is parabolic.  So there is no canonical extension of the
pairing to a non-parabolic second variable; a local class whose edge image is not parabolic has to
be excluded, and the Hecke-stable subspace of the plane cohomology with parabolic edge image is the
domain on which the pairing is used.

*The Hecke operators.*  The Hecke operator `T_p` of the cosets `α_j = [[1, j], [0, p]]`,
`α_∞ = ε_p [[p, 0], [0, 1]]` (all of determinant `p`) preserves the parabolic classes
(`parabolicHecke`).  By the semi-invariance `⟨σ_e(g) v, σ_{e'}(g) w⟩ = det(g)^{e + e' - m} ⟨v, w⟩` of
the pairing of binary forms,
`⟨σ_0(α_j)⁻¹ v, w⟩ = p^{n+2} ⟨v, σ_{-1}(α_j) w⟩` for every coset (`pairing_heckeRep_inv_badGood`),
and the scalar `p·α_j⁻¹` of the inverse double coset acts on `Sym^{n+1} ⊗ det⁻¹` by `p^{-(n+3)}`.
Hence the adjoint of `T_p` for the pairing is `p⁻¹` times the Hecke operator of the same double coset
`Γ diag(1, p) Γ = Γ diag(p, 1) Γ` on the dual side:

  `⟨T_p x, y⟩ = κ_p ⟨x, T_p y⟩`,  `κ_p = p⁻¹`.

This is the value forced by the edge formulas
`E_line (A y) = E y + p^{-(n+1)} T E y` and `E_plane (A y) = E y + p^{-(n+2)} T E y`: with `s = p^{-(n+1)}`
and `s' = p^{-(n+2)}` one has `s' = s κ_p` and the dual eigenvalue equals the eigenvalue of the line
class (`dualEigenvalue_badGood`).  The statement `LevelThreeParabolicAdjoint` records the adjointness
for the parabolic classes, and `goodPlane_pairing_eigen_parabolic` derives, from it and the edge
formulas, the eigenfunctional relation on every Hecke-stable subspace of the plane cohomology with
parabolic edge image.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree

open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (CuspH2 localOp)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets (heckeRep)

section Scalars

/-- **Semi-invariance of the pairing of binary forms under rational matrices.**  For `α ∈ GL₂(ℚ)` of
determinant `d` (in `ℂ`), `⟨σ_e(α) v, σ_{e'}(α) w⟩ = d^{e + e' - m} ⟨v, w⟩`. -/
theorem binaryPairing_rationalRho (m : ℕ) (e e' : ℤ) (α : GL (Fin 2) ℚ) (d : ℂ)
    (hd : ((GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α) : ℂˣ) :
      ℂ) = d)
    (v w : Binary.HomogeneousPoly m) :
    BinaryPairing.binaryPairing m (rationalRho m e α v) (rationalRho m e' α w) =
      d ^ (e + e' - (m : ℤ)) * BinaryPairing.binaryPairing m v w := by
  have h := BinaryPairing.binaryPairing_homogeneousAction m e e'
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α) v w
  rw [hd] at h
  exact h

/-- **The adjoint of the action of `α⁻¹`.**  For `α ∈ GL₂(ℚ)` of determinant `d`,
`⟨σ_e(α⁻¹) v, w⟩ = d^{-(e + e' - m)} ⟨v, σ_{e'}(α) w⟩`. -/
theorem binaryPairing_rationalRho_inv (m : ℕ) (e e' : ℤ) (α : GL (Fin 2) ℚ) (d : ℂ)
    (hd : ((GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α) : ℂˣ) :
      ℂ) = d)
    (v w : Binary.HomogeneousPoly m) :
    BinaryPairing.binaryPairing m (rationalRho m e α⁻¹ v) w =
      d ^ (-(e + e' - (m : ℤ))) * BinaryPairing.binaryPairing m v (rationalRho m e' α w) := by
  have hd' : ((GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) α⁻¹) :
      ℂˣ) : ℂ) = d⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, hd]
  have h := binaryPairing_rationalRho m e e' α⁻¹ d⁻¹ hd' v (rationalRho m e' α w)
  have hw : rationalRho m e' α⁻¹ (rationalRho m e' α w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hw, _root_.inv_zpow'] at h
  exact h

/-- Every Hecke coset representative `α_j` has determinant `p`. -/
theorem det_heckeRep (p : Nat.Primes) (j : Option (Fin p.val)) :
    ((GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) (heckeRep p j)) :
      ℂˣ) : ℂ) = (p.val : ℂ) := by
  rw [GeneralLinearGroup.val_det_apply]
  rcases j with _ | i
  · exact TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryHecke.det_none p
  · exact TernaryPeriodPolynomials.LevelThree.LevelThreeBoundaryHecke.det_some p i

/-- **Scalar of the Hecke cosets.**  For every coset representative `α_j` of the Hecke operator of
prime `p`, `⟨σ_e(α_j)⁻¹ v, w⟩ = p^{-(e + e' - m)} ⟨v, σ_{e'}(α_j) w⟩`. -/
theorem pairing_heckeRep_inv (m : ℕ) (e e' : ℤ) (p : Nat.Primes) (j : Option (Fin p.val))
    (v w : Binary.HomogeneousPoly m) :
    BinaryPairing.binaryPairing m (rationalRho m e (heckeRep p j)⁻¹ v) w =
      (p.val : ℂ) ^ (-(e + e' - (m : ℤ))) *
        BinaryPairing.binaryPairing m v (rationalRho m e' (heckeRep p j) w) :=
  binaryPairing_rationalRho_inv m e e' _ _ (det_heckeRep p j) v w

/-- **The scalar for the bad-line / good-plane pair** `(m, e, e') = (n + 1, 0, -1)`:
`⟨σ_0(α_j)⁻¹ v, w⟩ = p^{n+2} ⟨v, σ_{-1}(α_j) w⟩`. -/
theorem pairing_heckeRep_inv_badGood (n : ℕ) (p : Nat.Primes) (j : Option (Fin p.val))
    (v w : Binary.HomogeneousPoly (n + 1)) :
    BinaryPairing.binaryPairing (n + 1) (rationalRho (n + 1) 0 (heckeRep p j)⁻¹ v) w =
      (p.val : ℂ) ^ (n + 2) *
        BinaryPairing.binaryPairing (n + 1) v (rationalRho (n + 1) (-1) (heckeRep p j) w) := by
  have hex : -((0 : ℤ) + (-1) - (((n + 1 : ℕ)) : ℤ)) = ((n + 2 : ℕ) : ℤ) := by omega
  rw [pairing_heckeRep_inv (n + 1) 0 (-1) p j v w, hex, zpow_natCast]

end Scalars

section Obstruction

/-- **Dependence of the cup formula on the primitive.**  Changing the primitive triple `v` of the
first crossed homomorphism by a triple `f` changes the cup formula by `∑ᵢ B(fᵢ, z'(gᵢ))`.  For `f`
fixed by the three special elements this vanishes when `z'` takes coboundary values there, but not
for a general crossed homomorphism `z'`. -/
theorem cupFormula_add_fixed {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ G W)
    (a g₂ : G) (z : G → V) (z' : G → W) (v f : V × V × V) :
    CocycleBridge.cupFormula B ρ' a g₂ z z' (v + f) =
      CocycleBridge.cupFormula B ρ' a g₂ z z' v -
        (B f.1 (z' a) + B f.2.1 (z' g₂) + B f.2.2 (z' (a * g₂)⁻¹)) := by
  unfold CocycleBridge.cupFormula
  simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

end Obstruction

section Pairing

/-- **The Lefschetz pairing of the bad-line Levi with the good-plane Levi** (`n` odd): the parabolic
cup pairing of `H¹_par(Γ₁'(3), Sym^{n+1})` with `H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` for the pairing
of binary forms. -/
def badGoodPairing {n : ℕ} (hodd : Odd n) :
    parabolicCrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ :=
  parabolicPairing (twistedPairing_badLine_goodPlane hodd)

/-- **The adjointness constant** `κ_p = p⁻¹`: `⟨T_p x, y⟩ = κ_p ⟨x, T_p y⟩`. -/
def levelThreeKappa (p : Nat.Primes) : ℂ := ((p.val : ℂ))⁻¹

/-- **Hecke adjointness of a pairing on parabolic classes.**  The pairing `π` of
`H¹_par(Γ₁'(3), Sym^{n+1})` with `H¹_par(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` satisfies
`π (T_p x, y) = κ_p π (x, T_p y)` for every prime `p ≠ 3`, with the Hecke operators restricted to the
parabolic classes. -/
def LevelThreeParabolicAdjoint (n : ℕ)
    (π : parabolicCrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ) : Prop :=
  ∀ (p : Nat.Primes) (hp3 : p.val ≠ 3), IsHeckeAdjoint π (parabolicHecke (n + 1) 0 p hp3)
    (parabolicHecke (n + 1) (-1) p hp3) (κ p)

/-- **The adjointness statement for the Lefschetz pairing** `badGoodPairing`, with `κ_p = p⁻¹`. -/
def BadGoodHeckeAdjoint {n : ℕ} (hodd : Odd n) : Prop :=
  LevelThreeParabolicAdjoint n (badGoodPairing hodd) levelThreeKappa

/-- `κ_p` is nonzero. -/
theorem levelThreeKappa_ne_zero (p : Nat.Primes) : levelThreeKappa p ≠ 0 := by
  have hp0 : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  unfold levelThreeKappa
  exact inv_ne_zero hp0

/-- **Consistency of the dual eigenvalue.**  With the edge coefficients `s = p^{-(n+1)}` of the bad
line and `s' = p^{-(n+2)}` of the good plane, `s' = s κ_p`, so the dual eigenvalue of an eigenvalue
`c` is `c` itself. -/
theorem dualEigenvalue_badGood (n : ℕ) (p : Nat.Primes) (c : ℂ) :
    dualEigenvalue 1 (((p.val : ℂ) ^ (n + 1))⁻¹) 1 (((p.val : ℂ) ^ (n + 2))⁻¹)
      (levelThreeKappa p) c = c := by
  have hp0 : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  refine dualEigenvalue_self c (inv_ne_zero (pow_ne_zero _ hp0)) (levelThreeKappa_ne_zero p) ?_
  unfold levelThreeKappa
  have h : (p.val : ℂ) ^ (n + 2) = (p.val : ℂ) ^ (n + 1) * (p.val : ℂ) := by ring
  rw [h, mul_inv]

end Pairing

section Eigen

/-- **Eigenfunctional relation at the good plane, for parabolic classes.**  Let `x` be a parabolic
class of the bad-line Levi with `a x + s T_p x = c x`, the pairing `π` be `κ_p`-adjoint on parabolic
classes, and `𝒜` a subspace of the good-plane local cohomology which is stable under the local
operator of `T_p` and whose edge images are parabolic.  Then on `𝒜` the functional `π x (E ·)` is an
eigenfunctional of the local operator, with the dual eigenvalue `a' + s'(c - a)/(s κ_p)`. -/
theorem goodPlane_pairing_eigen_parabolic (n : ℕ) (hn : 0 < n) (p : Nat.Primes)
    (hp3 : p.val ≠ 3)
    (π : parabolicCrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      parabolicCrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ)
    (hadj : LevelThreeParabolicAdjoint n π κ) (hκ : κ p ≠ 0)
    {x : parabolicCrossedH1 (levelRep (n + 1) 0)} (a s c : ℂ) (hs : s ≠ 0)
    (hx : a • x + s • parabolicHecke (n + 1) 0 p hp3 x = c • x)
    (𝒜 : Submodule ℂ (CuspH2 n trivialCharacter .plane true))
    (hA : ∀ η ∈ 𝒜, localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .plane true η ∈ 𝒜)
    (hpar : ∀ η ∈ 𝒜, LevelThree.GoodPlaneEdge3.goodPlaneEdge hn η ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1)))
    (η : CuspH2 n trivialCharacter .plane true) (hη : η ∈ 𝒜) :
    π x ⟨LevelThree.GoodPlaneEdge3.goodPlaneEdge hn
        (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
          .plane true η), hpar _ (hA η hη)⟩ =
      dualEigenvalue a s 1 (((p.val : ℂ) ^ (n + 2))⁻¹) (κ p) c *
        π x ⟨LevelThree.GoodPlaneEdge3.goodPlaneEdge hn η, hpar η hη⟩ := by
  have hg : ∀ w : 𝒜,
      ((LevelThree.GoodPlaneEdge3.goodPlaneEdge hn).restrict hpar)
          (((localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
            .plane true).restrict hA) w) =
        (1 : ℂ) • ((LevelThree.GoodPlaneEdge3.goodPlaneEdge hn).restrict hpar) w +
          (((p.val : ℂ) ^ (n + 2))⁻¹) •
            parabolicHecke (n + 1) (-1) p hp3
              (((LevelThree.GoodPlaneEdge3.goodPlaneEdge hn).restrict hpar) w) := by
    intro w
    apply Subtype.ext
    simp only [LinearMap.coe_restrict_apply, Submodule.coe_add, Submodule.coe_smul,
      parabolicHecke_coe, one_smul]
    exact LevelThree.GoodPlaneLocalOp.goodPlaneEdge_localOp_tp p hp3 n hn w.1
  exact pairing_eigen_of_edge π (parabolicHecke (n + 1) 0 p hp3)
    (parabolicHecke (n + 1) (-1) p hp3) (κ p) (hadj p hp3)
    ((LevelThree.GoodPlaneEdge3.goodPlaneEdge hn).restrict hpar)
    ((localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
      .plane true).restrict hA)
    a s 1 (((p.val : ℂ) ^ (n + 2))⁻¹) c hs hκ hg hx ⟨η, hη⟩

/-- **The eigen-edge of the bad line is an eigenvector of the parabolic Hecke operator.**  If the
edge map `f` intertwines the local operator with `1 + s T_p`, takes values in the parabolic classes,
and `A y = c y`, then the parabolic edge class `x` satisfies `x + s T_p x = c x`. -/
theorem edge_eigen_relation_parabolic {V : Type*} [AddCommGroup V] [Module ℂ V] (m : ℕ) (e : ℤ)
    (p : Nat.Primes) (hp3 : p.val ≠ 3) (f : V →ₗ[ℂ] CrossedH1 (levelRep m e))
    (hf : ∀ v, f v ∈ parabolicCrossedH1 (levelRep m e)) (A : Module.End ℂ V) (s c : ℂ)
    (hAf : ∀ v, f (A v) = f v + s • LevelThree.LevelThreeHeckeH1.levelHecke m e p hp3 (f v))
    {v : V} (hv : A v = c • v) :
    (1 : ℂ) • (⟨f v, hf v⟩ : parabolicCrossedH1 (levelRep m e)) +
        s • parabolicHecke m e p hp3 ⟨f v, hf v⟩ = c • ⟨f v, hf v⟩ := by
  apply Subtype.ext
  have h := hAf v
  rw [hv, map_smul] at h
  simp only [Submodule.coe_add, Submodule.coe_smul, parabolicHecke_coe, one_smul]
  rw [← h]

end Eigen

end TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
