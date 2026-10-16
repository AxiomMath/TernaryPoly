module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Carriers

@[expose] public section


/-!
# Cap systems on chain complexes of representations

A `CapSystem` on a chain complex `C` of representations of `Γ` is the data of the Alexander-Whitney cap of
`C` with cochains evaluated on the *front* face: for every cocycle `b : C.X a ⟶ W` and every `q` a morphism
`cap b q : C.X (a+q) ⟶ W ⊗ C.X q`, satisfying the Leibniz rule `∂ ≫ cap b q = (-1)^a • cap b (q+1) ≫ (W ◁ ∂)`
and the counit rule with respect to an augmentation `eps : C.X 0 ⟶ 𝟙_`.

`cap_compat`: a chain map `u : C ⟶ D` between complexes with cap systems, carried by acyclic carriers, is
compatible with the caps up to a carried homotopy, for every cocycle of `D`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- The cap of a chain complex of representations against cocycles on the front face. -/
structure CapSystem (C : ChainComplex (Rep.{0} ℚ Γ) ℕ) where
  cap : ∀ {W : Rep.{0} ℚ Γ} {a : ℕ} (b : C.X a ⟶ W), C.d (a+1) a ≫ b = 0 → ∀ q : ℕ, C.X (a+q) ⟶ W ⊗ C.X q
  intertwine : ∀ {W : Rep.{0} ℚ Γ} {a : ℕ} (b : C.X a ⟶ W) (hb : C.d (a+1) a ≫ b = 0) (q : ℕ),
    C.d (a+q+1) (a+q) ≫ cap b hb q = ((-1 : ℤ)^a) • (cap b hb (q+1) ≫ (W ◁ C.d (q+1) q))
  eps : C.X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ)
  eps_d : C.d 1 0 ≫ eps = 0
  counit : ∀ {W : Rep.{0} ℚ Γ} {a : ℕ} (b : C.X a ⟶ W) (hb : C.d (a+1) a ≫ b = 0),
    cap b hb 0 ≫ (W ◁ eps) ≫ (ρ_ W).hom = b

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
