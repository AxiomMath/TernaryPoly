module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.SymRepSL
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupport.Cusps
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESSpan

@[expose] public section


/-!
# The coefficient dictionary between `binRep Λ n` and `EuclideanSpace ℂ (Fin (n + 2))`

The values of the period cocycles of Lemma C.3 (`SeedC3S4c.binRep Λ n = Sym^{n+1} ⊗ det⁻¹`,
binary forms of degree `n + 1` acted on by substitution) are identified with coefficient vectors
in the monomial basis `X₀^{n+1-i} X₁^i` (`toW`, inverse `ofW`), and the action becomes
`Matrix.toEuclideanLin (symRep (n + 1) γ)` (`toW_rho`). Cocycles, coboundaries and the parabolic
condition transport accordingly (`cocycleW`, `cocycleW_mul`, `cocycleW_parabolic`,
`H1π_eq_zero_of_coboundaryW`). This is the dictionary through which the analytic
Eichler–Shimura route (on `EuclideanSpace`) proves `ESSpan`.

Written by Claude Opus 5.5.
-/

open GeneralEisenstein MvPolynomial CategoryTheory groupCohomology
open TernaryPeriodPolynomials.SphericalDetection.Helpers TernaryPeriodPolynomials.Argument.SeedC3
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.BinCoeff

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
open TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport (IsParabolicElt)

variable {Λ : Subgroup SL(2, ℤ)} {n : ℕ}

/-- The coefficient space. -/
abbrev Wn (n : ℕ) : Type := EuclideanSpace ℂ (Fin (n + 1 + 1))

theorem isHomogeneous_bvalΛ (x : binRep Λ n) : (bvalΛ x).IsHomogeneous (n + 1) :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mp (x : Binary.HomogeneousPoly (n + 1)).2

/-- Coefficient vector of a binary form. -/
def toW (x : binRep Λ n) : Wn n := (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).symm
  (coords (n + 1) (bvalΛ x))

theorem toW_apply (x : binRep Λ n) (i : Fin (n + 1 + 1)) : toW x i = coords (n + 1) (bvalΛ x) i :=
  rfl

theorem isHomogeneous_thetaPoly (v : Fin (n + 1 + 1) → ℂ) :
    (thetaPoly (n + 1) v).IsHomogeneous (n + 1) :=
  MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
    (isHomogeneous_monoPoly (n + 1) i).C_mul (v i)

/-- The binary form with a given coefficient vector. -/
def ofW (v : Wn n) : binRep Λ n :=
  (⟨thetaPoly (n + 1) (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ v),
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (isHomogeneous_thetaPoly _)⟩ :
    Binary.HomogeneousPoly (n + 1))

theorem toW_ofW (v : Wn n) : toW (ofW (Λ := Λ) v) = v := by
  rw [toW]
  change (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).symm
    (coords (n + 1) (thetaPoly (n + 1) (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ v))) = v
  rw [coords_thetaPoly]
  exact (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).symm_apply_apply v

theorem ofW_toW (x : binRep Λ n) : ofW (toW x) = x := by
  apply Subtype.ext
  change thetaPoly (n + 1) (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ
    ((EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).symm (coords (n + 1) (bvalΛ x)))) = bvalΛ x
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact thetaPoly_coords (n + 1) (isHomogeneous_bvalΛ x)

theorem toW_injective : Function.Injective (toW (Λ := Λ) (n := n)) := fun x y h => by
  rw [← ofW_toW x, ← ofW_toW y, h]

theorem toW_add (x y : binRep Λ n) : toW (x + y) = toW x + toW y := by
  rw [toW, toW, toW, ← map_add]
  congr 1

theorem toW_sub (x y : binRep Λ n) : toW (x - y) = toW x - toW y := by
  have h := toW_add (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem toW_smul (a : ℂ) (x : binRep Λ n) : toW (a • x) = a • toW x := by
  rw [toW, toW, ← map_smul]
  congr 1

/-- The coefficient representation of `Λ`. -/
def rhoW (Λ : Subgroup SL(2, ℤ)) (n : ℕ) : Λ →* Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ :=
  (symRep (n + 1)).comp Λ.subtype

/-- The action of `Λ` becomes the matrix action of `symRep`. -/
theorem toW_rho (γ : Λ) (x : binRep Λ n) :
    toW ((binRep Λ n).ρ γ x) = Matrix.toEuclideanLin (rhoW Λ n γ) (toW x) := by
  have h1 : bvalΛ ((binRep Λ n).ρ γ x) =
      bind₁ (invCoordPoly (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)))) (bvalΛ x) :=
    modularBinaryRep_coe (n + 1) γ.1 x
  rw [toW, toW, h1, ← symRepGL_mulVec (n + 1) _ (isHomogeneous_bvalΛ x)]
  rfl

/-- A cocycle with values in binary forms, as a function to coefficient vectors. -/
def cocycleW (c : cocycles₁ (binRep Λ n)) (γ : Λ) : Wn n := toW (c γ)

theorem cocycleW_mul (c : cocycles₁ (binRep Λ n)) (δ γ : Λ) :
    cocycleW c (δ * γ) = cocycleW c δ + Matrix.toEuclideanLin (rhoW Λ n δ) (cocycleW c γ) := by
  have h := (mem_cocycles₁_iff (A := binRep Λ n) c).1 c.2 δ γ
  rw [cocycleW, cocycleW, cocycleW, h, toW_add, toW_rho, add_comm]

theorem cocycleW_parabolic {c : cocycles₁ (binRep Λ n)} (hc : c ∈ parabolicCocycles Λ n)
    (γ : Λ) (hγ : IsParabolicElt γ.1) :
    ∃ u : Wn n, cocycleW c γ = Matrix.toEuclideanLin (rhoW Λ n γ) u - u := by
  obtain ⟨u, hu⟩ := hc γ hγ
  exact ⟨toW u, by rw [cocycleW, hu, toW_sub, toW_rho]⟩

/-- A cocycle whose coefficient vectors form a coboundary has trivial class. -/
theorem H1π_eq_zero_of_coboundaryW (c : cocycles₁ (binRep Λ n)) (w : Wn n)
    (hw : ∀ δ : Λ, cocycleW c δ = Matrix.toEuclideanLin (rhoW Λ n δ) w - w) :
    H1π (binRep Λ n) c = 0 := by
  rw [H1π_eq_zero_iff]
  refine ⟨ofW (Λ := Λ) w, ?_⟩
  funext δ
  apply toW_injective
  rw [d₀₁_hom_apply, toW_sub, toW_rho, toW_ofW, ← hw δ]
  rfl

end TernaryPeriodPolynomials.Argument.ESFoundations.BinCoeff
