module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QSide

@[expose] public section


/-!
# Naturality of the `Q`-side Hochschild-Serre step in the complex `Z`

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {Q : Type} [Group Q]

section Z

variable {Z Z' : ChainComplex (Rep.{0} ℚ Q) ℕ} (z : Z ⟶ Z')

/-- The map `(Z ⊗ X)_Q → (Z' ⊗ X)_Q` induced by a chain map `z : Z → Z'`. -/
def muX (X : Rep.{0} ℚ Q) : CxF Z X ⟶ CxF Z' X :=
  ((FX X).mapHomologicalComplex (ComplexShape.down ℕ)).map z

theorem muX_f (X : Rep.{0} ℚ Q) (j : ℕ) : (muX z X).f j = (FX X).map (z.f j) := rfl

theorem muX_comm {X Y : Rep.{0} ℚ Q} (φ : X ⟶ Y) : muX z X ≫ CxMap Z' φ = CxMap Z φ ≫ muX z Y := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  simp only [HomologicalComplex.comp_f, muX_f, CxMap_f]
  exact (FXmap φ).naturality (z.f j)

variable (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0)

/-- The morphism of short complexes of coinvariant complexes induced by `z`. -/
def sesCMap : sesC Z P1 P0 d ε hdε ⟶ sesC Z' P1 P0 d ε hdε where
  τ₁ := muX z P1
  τ₂ := muX z P0
  τ₃ := muX z (Rep.trivial ℚ Q ℚ)
  comm₁₂ := muX_comm z d
  comm₂₃ := muX_comm z ε

end Z


section Amb

variable {Z Z' : ChainComplex (Rep.{0} ℚ Q) ℕ} (z : Z ⟶ Z')

theorem phiH_nat (X : Rep.{0} ℚ Q) [Projective X] (n : ℕ) :
    HomologicalComplex.homologyMap (muX z X) n ≫ (phiH Z' X n).hom =
      (phiH Z X n).hom ≫ (FX X).map (HomologicalComplex.homologyMap z n) := by
  have := FX_preservesHomology X
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) n).map z) (FX X)

variable (P1 P0 : Rep.{0} ℚ Q) (d : P1 ⟶ P0) (ε : P0 ⟶ Rep.trivial ℚ Q ℚ) (hdε : d ≫ ε = 0)
  [Projective P1] [Projective P0] (hZ : ∀ j, Projective (Z.X j)) (hZ' : ∀ j, Projective (Z'.X j))
  (hS : (ShortComplex.mk d ε hdε).ShortExact)

/-- The ambient Hochschild-Serre map `H₃((Z ⊗ 1)_Q) → (H₂ Z ⊗ P1)_Q`: connecting homomorphism followed by `phiH`. -/
def hsAmb (Z : ChainComplex (Rep.{0} ℚ Q) ℕ) (hZ : ∀ j, Projective (Z.X j)) :
    (CxF Z (Rep.trivial ℚ Q ℚ)).homology 3 ⟶ (FX P1).obj (Z.homology 2) :=
  (sesC_shortExact Z P1 P0 d ε hdε hZ hS).δ 3 2 rfl ≫ (phiH Z P1 2).hom

/-- **Naturality of the ambient Hochschild-Serre map in the complex `Z`.** -/
theorem hsAmb_nat :
    HomologicalComplex.homologyMap (muX z (Rep.trivial ℚ Q ℚ)) 3 ≫ hsAmb P1 P0 d ε hdε hS Z' hZ' =
      hsAmb P1 P0 d ε hdε hS Z hZ ≫ (FX P1).map (HomologicalComplex.homologyMap z 2) := by
  unfold hsAmb
  have h1 := HomologicalComplex.HomologySequence.δ_naturality (sesCMap z P1 P0 d ε hdε)
    (sesC_shortExact Z P1 P0 d ε hdε hZ hS) (sesC_shortExact Z' P1 P0 d ε hdε hZ' hS) 3 2 rfl
  have h2 := phiH_nat z P1 2
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun w => w ≫ (phiH Z' P1 2).hom) h1.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun w => (sesC_shortExact Z P1 P0 d ε hdε hZ hS).δ 3 2 rfl ≫ w) h2).trans ?_
  exact (Category.assoc _ _ _).symm

end Amb

end TernaryPeriodPolynomials.Argument.HochschildSerre
