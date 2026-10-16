module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeLevi

@[expose] public section


/-!
# The level-one bridge at the good line

The `GL₂(ℤ)`-modules of the parabolic duality at the good line are the Levi modules
`M = Sym^{n+1} ⊗ det^e`, `M' = Sym^{n+1} ⊗ det^{e'}` with `(e, e') = (0, -1)` for the trivial
character and `(e, e') = (-1, 0)` for a character with `χ(-1_∞) = -1`.  The coordinates are the
good-line coordinate `PhiTotal` and the rotated identity-plane coordinate `PsiTotal`; the Levi
cocycles `γ ↦ Φ(A(k_γ⁻¹))` and `γ ↦ Ψ(A'(k_γ⁻¹))` are one-cocycles of `GL₂(ℤ)`
(`bridgeX`, `bridgeX'`) because the coordinates are equivariant on the `U`-equivariant
one-cocycles (`Phi_levi`, `Psi_levi`) and the Levi cocycles are such cocycles for every `γ`
(`uCocycle_leviCocycle_hom`); the Kostant pairing is `−(n+1)!` times the binary pairing of the
coordinates (`kostant_eq_binaryPairing`).  The determinant twists produced by the sign of the
coefficients and by the rotation are brought to `e`, `e'` by the equality of the actions of
`GL₂(ℤ)` on `Sym^d ⊗ det^e` and `Sym^d ⊗ det^{e'}` for `e - e'` even, which uses that the degree `n`
is odd (`levelOneBridgeOfTwists`, `levelOneBridgeTrivial`, `levelOneBridgeOdd`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (GL2Z toGL cocycleInclusion)

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (cochainRep cochainRep_apply pull1 leviCocycle leviCocycle_mul)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant FiberHyp)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolic (LevelOneBridge)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### The determinant twists -/

/-- The twist hypothesis at the line coordinate: the sign-twisted Levi action on `Sym^{n+1}` is the
action of `Sym^{n+1} ⊗ det^e`. -/
def PhiTwist (n : ℕ) (χ : RankOneCharacter) (e : ℤ) : Prop :=
  ∀ γ : GL2Z, Twisted.detSign χ (leviHom γ) •
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) =
    Binary.homogeneousAction (n + 1) e (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)

/-- The twist hypothesis at the rotated plane coordinate: the sign-twisted Levi action through the
rotation is the action of `Sym^{n+1} ⊗ det^{e'}`. -/
def PsiTwist (n : ℕ) (χ : RankOneCharacter) (e' : ℤ) : Prop :=
  ∀ γ : GL2Z, Twisted.detSign χ (leviHom (invT γ)) •
      Binary.homogeneousAction (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
        (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) =
    Binary.homogeneousAction (n + 1) e' (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)

/-- For the trivial character the determinant sign is `1`. -/
theorem detSign_trivial (g : RationalGL3) : Twisted.detSign trivialCharacter g = 1 := by
  rw [Twisted.detSign_eq_ite]
  split_ifs <;> rfl

/-- The twist at the line coordinate for the trivial character: `e = 0`. -/
theorem phiTwist_trivial (n : ℕ) : PhiTwist n trivialCharacter 0 := by
  intro γ
  rw [detSign_trivial, one_smul]

/-- The twist at the plane coordinate for the trivial character and odd `n`: `e' = -1`. -/
theorem psiTwist_trivial {n : ℕ} (hn : Odd n) : PsiTwist n trivialCharacter (-1) := by
  intro γ
  rw [detSign_trivial, one_smul]
  obtain ⟨k, hk⟩ := hn
  exact homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1)) (-1)
    ⟨(k : ℤ) + 2, by omega⟩ γ

/-- The twist at the line coordinate for a character with `χ(-1_∞) = -1`: `e = -1`. -/
theorem phiTwist_odd {n : ℕ} {χ : RankOneCharacter}
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1) : PhiTwist n χ (-1) := by
  intro γ
  have t := Twisted.homogeneousAction_succ_twist (n + 1) 0
    (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)
  rw [zero_add, det_map_complex] at t
  rw [leviHom_eq, Twisted.detSign_arithmeticLevi_odd h γ, ← t]
  exact homogeneousAction_even_twist (n + 1) 1 (-1) ⟨1, by norm_num⟩ γ

/-- The twist at the plane coordinate for a character with `χ(-1_∞) = -1` and odd `n`: `e' = 0`. -/
theorem psiTwist_odd {n : ℕ} {χ : RankOneCharacter} (hn : Odd n)
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1) : PsiTwist n χ 0 := by
  intro γ
  have t := Twisted.homogeneousAction_succ_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
    (GeneralLinearGroup.map (Int.castRingHom ℂ) γ)
  rw [det_map_complex] at t
  rw [leviHom_eq, Twisted.detSign_arithmeticLevi_odd h (invT γ), det_invT, ← t]
  obtain ⟨k, hk⟩ := hn
  exact homogeneousAction_even_twist (n + 1) (((n + 1 : ℕ) : ℤ) - (-1) + 1) 0
    ⟨(k : ℤ) + 2, by omega⟩ γ

/-! ### The Levi cocycles as one-cocycles of `GL₂(ℤ)` -/

section Bridge

/-- A binary form, viewed as an element of the arithmetic module `Sym^{n+1} ⊗ det^e`. -/
abbrev asArith (n : ℕ) (e : ℤ) (x : Binary.HomogeneousPoly (n + 1)) : arithmeticBinaryRep (n + 1) e :=
  x

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The line cocycle of the bridge**: `γ ↦ Φ(A(k_γ⁻¹))`, a one-cocycle of `GL₂(ℤ)` with values in
`Sym^{n+1} ⊗ det^e`. -/
def bridgeX (positive : 0 < n) (e : ℤ) (hΦ : PhiTwist n χ e)
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) e) :=
  ⟨fun γ => PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom γ)⁻¹),
    (groupCohomology.mem_cocycles₁_iff _).mpr (fun g h => by
      have e1 : leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom (g * h))⁻¹ =
          leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom g)⁻¹ +
            cochainRep (rationalCoefficientComponent n χ) (leviHom g)
              (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom h)⁻¹) := by
        rw [map_mul, _root_.mul_inv_rev]
        exact leviCocycle_mul (rationalCoefficientComponent n χ) ωU (leviHom h)⁻¹ (leviHom g)⁻¹
      have hM : (arithmeticBinaryRep (n + 1) e).ρ g
          (PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom h)⁻¹)) =
          Twisted.detSign χ (leviHom g) •
            Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) g)
              (PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom h)⁻¹)) :=
        (LinearMap.congr_fun (hΦ g) _).symm
      show PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom (g * h))⁻¹) =
        (arithmeticBinaryRep (n + 1) e).ρ g
          (PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom h)⁻¹)) +
          asArith n e (PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom g)⁻¹))
      rw [e1, map_add, Phi_levi n χ positive (uCocycle_leviCocycle_hom hF h).1 g, hM]
      exact add_comm _ _)⟩

/-- **The plane cocycle of the bridge**: `γ ↦ Ψ(A'(k_γ⁻¹))`, a one-cocycle of `GL₂(ℤ)` with values
in `Sym^{n+1} ⊗ det^{e'}`. -/
def bridgeX' (e' : ℤ) (hΨ : PsiTwist n χ e')
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) e') :=
  ⟨fun γ => PsiTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom γ)⁻¹),
    (groupCohomology.mem_cocycles₁_iff _).mpr (fun g h => by
      have e1 : leviCocycle (dualRep (dualityData n χ)) θU (leviHom (g * h))⁻¹ =
          leviCocycle (dualRep (dualityData n χ)) θU (leviHom g)⁻¹ +
            cochainRep (dualRep (dualityData n χ)) (leviHom g)
              (leviCocycle (dualRep (dualityData n χ)) θU (leviHom h)⁻¹) := by
        rw [map_mul, _root_.mul_inv_rev]
        exact leviCocycle_mul (dualRep (dualityData n χ)) θU (leviHom h)⁻¹ (leviHom g)⁻¹
      have hM : (arithmeticBinaryRep (n + 1) e').ρ g
          (PsiTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom h)⁻¹)) =
          Twisted.detSign χ (leviHom (invT g)) •
            Binary.homogeneousAction (n + 1) (((n + 1 : ℕ) : ℤ) - (-1))
              (GeneralLinearGroup.map (Int.castRingHom ℂ) g)
              (PsiTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom h)⁻¹)) :=
        (LinearMap.congr_fun (hΨ g) _).symm
      show PsiTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom (g * h))⁻¹) =
        (arithmeticBinaryRep (n + 1) e').ρ g
          (PsiTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom h)⁻¹)) +
          asArith n e' (PsiTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom g)⁻¹))
      rw [e1, map_add, Psi_levi n χ (uCocycle_leviCocycle_hom hF h).2 g, hM]
      exact add_comm _ _)⟩

/-- **The level-one bridge at the good line**, for the twists `e`, `e'` of the modules.  The
Kostant constant is `c = -(n+1)!`. -/
def levelOneBridgeOfTwists (positive : 0 < n) (e e' : ℤ) (hΦ : PhiTwist n χ e)
    (hΨ : PsiTwist n χ e')
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :
    LevelOneBridge (dualityData n χ) ωU θU (arithmeticBinaryRep (n + 1) e)
      (arithmeticBinaryRep (n + 1) e') (BinaryPairing.binaryPairing (n + 1))
      (bridgeX positive e hΦ hF) (bridgeX' e' hΨ hF) (-((n + 1).factorial : ℂ)) where
  levi := leviHom
  Φ := PhiTotal n
  Ψ := PsiTotal n
  levi_S := leviHom_S
  levi_T := leviHom_T
  pairing := fun _ _ hf hg => kostant_eq_binaryPairing n χ positive hf hg
  alpha := fun _ => rfl
  beta := fun _ => rfl
  equivΦ := fun γ _ hf => (Phi_levi n χ positive hf γ).trans (LinearMap.congr_fun (hΦ γ) _)
  equivΨ := fun γ _ hg => (Psi_levi n χ hg γ).trans (LinearMap.congr_fun (hΨ γ) _)

/-- **The level-one bridge for the trivial character**: `M = Sym^{n+1} ⊗ det^0`,
`M' = Sym^{n+1} ⊗ det^{-1}`, for odd `n`. -/
def levelOneBridgeTrivial (hn : Odd n)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :=
  levelOneBridgeOfTwists hn.pos 0 (-1) (phiTwist_trivial n) (psiTwist_trivial hn) hF

/-- **The level-one bridge for a character with `χ(-1_∞) = -1`** (for example the odd quadratic
character of conductor three): `M = Sym^{n+1} ⊗ det^{-1}`, `M' = Sym^{n+1} ⊗ det^0`, for odd `n`. -/
def levelOneBridgeOdd (hn : Odd n) (h : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hF : FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ))
      (dualityData n χ).B (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU) :=
  levelOneBridgeOfTwists hn.pos (-1) 0 (phiTwist_odd h) (psiTwist_odd hn h) hF

end Bridge

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
