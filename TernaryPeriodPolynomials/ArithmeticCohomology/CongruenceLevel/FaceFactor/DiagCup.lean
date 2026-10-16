module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.NerveDiagonal
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section


/-!
# The Alexander-Whitney diagonal of the nerve model restricts to the cup product of the bar cochains

Formalized by Claude Sonnet 5.5.

For a subgroup `S ≤ Γ` fixing the label `z`, a base vertex `v₀` and a cochain `f` of the permutation resolution `prodComplex Γ V Z`, the *bar cochain* of `f` on `S`
is `F f (x₁, …, x_k) = f [((x₁⋯x_i) v₀)_i ; z]` (this is what `fixThetaBar` pulls back).  The diagonal `nerveDelta` of the model evaluated on the image of a bar simplex
`(x₁, …, x_{p+q})` is the pairing of `F f (x₁..x_p)` with `x₁⋯x_p · F g (x_{p+1}..x_{p+q})` (`diag_pair_bar`): the inhomogeneous cup-product formula.
-/

open CategoryTheory MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Partial

variable {M : Type} [Monoid M]

theorem pp_succ {n : ℕ} (x : Fin n → M) (i : ℕ) (hi : i < n) :
    Fin.partialProd x ⟨i + 1, by omega⟩ = Fin.partialProd x ⟨i, by omega⟩ * x ⟨i, hi⟩ :=
  Fin.partialProd_succ x ⟨i, hi⟩

/-- The partial products of the first `p` letters are the first partial products. -/
theorem pp_front {p q : ℕ} (x : Fin (p + q) → M) (i : ℕ) (hi : i ≤ p) :
    Fin.partialProd x ⟨i, by omega⟩ = Fin.partialProd (fun j : Fin p => x ⟨j, by omega⟩) ⟨i, by omega⟩ := by
  induction i with
  | zero => simp [Fin.partialProd_zero]
  | succ i ih =>
    rw [pp_succ x i (by omega), pp_succ (fun j : Fin p => x ⟨j, by omega⟩) i (by omega), ih (by omega)]

/-- The partial products of the last letters: `P_x(p + i) = P_x(p) · P_{x∘(p+·)}(i)`. -/
theorem pp_back {p q : ℕ} (x : Fin (p + q) → M) (i : ℕ) (hi : i ≤ q) :
    Fin.partialProd x ⟨p + i, by omega⟩ =
      Fin.partialProd x ⟨p, by omega⟩ * Fin.partialProd (fun j : Fin q => x ⟨p + j, by omega⟩) ⟨i, by omega⟩ := by
  induction i with
  | zero => simp [Fin.partialProd_zero]
  | succ i ih =>
    have e : (⟨p + (i + 1), by omega⟩ : Fin (p + q + 1)) = ⟨(p + i) + 1, by omega⟩ := rfl
    rw [e, pp_succ x (p + i) (by omega), pp_succ (fun j : Fin q => x ⟨p + j, by omega⟩) i (by omega), ih (by omega), mul_assoc]

end Partial

section Diag

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (S : Subgroup Γ) (v₀ : V) (z : Z)

/-- The simplex of `prodComplex Γ V Z` attached to a bar simplex `(x₁, …, x_k)` of `S`. -/
def barSimplex {k : ℕ} (x : Fin k → S) : (Fin (k + 1) → V) × Z :=
  (fun i => ((Fin.partialProd x i : S) : Γ) • v₀, z)

/-- The bar cochain of a cochain of the permutation resolution. -/
def barCochain {W : Rep.{0} ℚ Γ} {k : ℕ} (f : (prodComplex Γ V Z).X k ⟶ W) (x : Fin k → S) : W :=
  f.hom (MonoidAlgebra.single (barSimplex S v₀ z x) 1)

variable (hz : ∀ s : S, (s : Γ) • z = z)
include hz

/-- **The model diagonal restricted to bar simplices is the inhomogeneous cup product.** -/
theorem diag_pair_bar {W W' : Rep.{0} ℚ Γ} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ)) (p q : ℕ)
    (f : (prodComplex Γ V Z).X p ⟶ W) (g : (prodComplex Γ V Z).X q ⟶ W') (x : Fin (p + q) → S) :
    (nerveDelta Γ V Z p q (p + q) rfl ≫ (f ⊗ₘ g) ≫ π).hom (MonoidAlgebra.single (barSimplex S v₀ z x) 1) =
      π.hom (barCochain S v₀ z f (fun j : Fin p => x ⟨j, by omega⟩) ⊗ₜ[ℚ]
        W'.ρ ((Fin.partialProd x ⟨p, by omega⟩ : S) : Γ)
          (barCochain S v₀ z g (fun j : Fin q => x ⟨p + j, by omega⟩))) := by
  have key : (nerveDelta Γ V Z p q (p + q) rfl ≫ (f ⊗ₘ g) ≫ π).hom (MonoidAlgebra.single (barSimplex S v₀ z x) 1) =
      π.hom (f.hom (MonoidAlgebra.single (frontFace V Z p (p + q) (by omega) (barSimplex S v₀ z x)) 1) ⊗ₜ[ℚ]
        g.hom (MonoidAlgebra.single (backFace V Z p q (p + q) rfl (barSimplex S v₀ z x)) 1)) := by
    change π.hom ((f ⊗ₘ g).hom ((nerveDelta Γ V Z p q (p + q) rfl).hom (MonoidAlgebra.single _ 1))) = _
    rw [nerveDelta_single]
    exact congrArg π.hom (tensorHom_tmul' f g _ _)
  refine key.trans ?_
  have hfront : frontFace V Z p (p + q) (by omega) (barSimplex S v₀ z x) =
      barSimplex S v₀ z (fun j : Fin p => x ⟨j, by omega⟩) := by
    refine Prod.ext ?_ rfl
    funext j
    show ((Fin.partialProd x ⟨j.1, by omega⟩ : S) : Γ) • v₀ = ((Fin.partialProd _ j : S) : Γ) • v₀
    rw [pp_front x j.1 (by omega)]
  have hback : backFace V Z p q (p + q) rfl (barSimplex S v₀ z x) =
      ((Fin.partialProd x ⟨p, by omega⟩ : S) : Γ) • barSimplex S v₀ z (fun j : Fin q => x ⟨p + j, by omega⟩) := by
    refine Prod.ext ?_ (hz _).symm
    funext j
    show ((Fin.partialProd x ⟨p + j.1, by omega⟩ : S) : Γ) • v₀ =
      ((Fin.partialProd x ⟨p, by omega⟩ : S) : Γ) • (((Fin.partialProd _ j : S) : Γ) • v₀)
    rw [pp_back x j.1 (by omega), Subgroup.coe_mul, mul_smul]
  rw [hfront, hback]
  congr 2
  exact (congrArg g.hom (X_ρ_single Γ V Z q ((Fin.partialProd x ⟨p, by omega⟩ : S) : Γ)
    (barSimplex S v₀ z (fun j : Fin q => x ⟨p + j, by omega⟩)) 1).symm).trans
    (Rep.hom_comm_apply g ((Fin.partialProd x ⟨p, by omega⟩ : S) : Γ) _)

end Diag

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
