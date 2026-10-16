module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeCoordinates
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains

@[expose] public section


/-!
# Chain maps out of the signed cone with vanishing corner homotopy

For chain maps `a : F ⟶ L`, `b : F ⟶ P` of chain complexes of rational representations and
`α : L ⟶ Q`, `β : P ⟶ Q` with `a ≫ α = b ≫ β`, the signed cone `signedCone a b` (the homotopy cofibre of
`(a, -b) : F ⟶ L ⊞ P`, the total complex of the arithmetic boundary) maps to `Q` by `coneDesc`, with zero
homotopy on the corner.  Its restrictions to the line and plane summands are `α` and `β`
(`signedLineInclusion_coneDesc`, `signedPlaneInclusion_coneDesc`), and it vanishes on the corner
(`signedCornerInclusion_coneDesc`).  On cochains with values in a representation `W` this gives the
cone cochain `(0, α^* c, β^* c)` attached to a cochain `c` of `Q` (`coneDescCochain`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex Preadditive Linear

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall

section Generic

variable {G : Type} [Group G] {F L P Q : ChainComplex (Rep.{0} ℚ G) ℕ}
  (a : F ⟶ L) (b : F ⟶ P) (α : L ⟶ Q) (β : P ⟶ Q)

theorem signedArrow_desc_zero (h : a ≫ α = b ≫ β) :
    signedArrow a b ≫ biprod.desc α β = 0 := by
  simp only [signedArrow, biprod.lift_desc, Preadditive.neg_comp, h]
  simp

/-- The chain map from the signed cone to `Q` that restricts to `α` on the line summand and to `β` on
the plane summand, with zero homotopy. -/
def coneDesc (h : a ≫ α = b ≫ β) : signedCone a b ⟶ Q :=
  homotopyCofiber.desc (signedArrow a b) (biprod.desc α β)
    (Homotopy.ofEq (signedArrow_desc_zero a b α β h))

theorem inrX_coneDesc (h : a ≫ α = b ≫ β) (n : ℕ) :
    homotopyCofiber.inrX (signedArrow a b) n ≫ (coneDesc a b α β h).f n =
      (biprod.desc α β).f n :=
  homotopyCofiber.inrX_desc_f _ _ _ _

theorem signedLineInclusion_coneDesc (h : a ≫ α = b ≫ β) (n : ℕ) :
    signedLineInclusion a b n ≫ (coneDesc a b α β h).f n = α.f n := by
  unfold signedLineInclusion
  rw [Category.assoc, inrX_coneDesc]
  simp [← comp_f]

theorem signedPlaneInclusion_coneDesc (h : a ≫ α = b ≫ β) (n : ℕ) :
    signedPlaneInclusion a b n ≫ (coneDesc a b α β h).f n = β.f n := by
  unfold signedPlaneInclusion
  rw [Category.assoc, inrX_coneDesc]
  simp [← comp_f]

theorem signedCornerInclusion_coneDesc (h : a ≫ α = b ≫ β) (n : ℕ) :
    signedCornerInclusion a b n ≫ (coneDesc a b α β h).f (n + 1) = 0 := by
  unfold signedCornerInclusion coneDesc
  rw [homotopyCofiber.inlX_desc_f]
  rfl

variable (W : Rep.{0} ℚ G)

/-- **The cone coordinates of the pullback of a cochain of `Q`**: corner component zero, line component
`α^* c`, plane component `β^* c`. -/
theorem signedConeHomSucc_coneDesc (h : a ≫ α = b ≫ β) (n : ℕ) (c : Q.X (n + 1) ⟶ W) :
    signedConeHomSucc a b W n ((coneDesc a b α β h).f (n + 1) ≫ c) =
      (0, (α.f (n + 1) ≫ c, β.f (n + 1) ≫ c)) := by
  rw [signedConeHomSucc_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change signedCornerInclusion a b n ≫ (coneDesc a b α β h).f (n + 1) ≫ c = 0
    rw [← Category.assoc, signedCornerInclusion_coneDesc, zero_comp]
  · change signedLineInclusion a b (n + 1) ≫ (coneDesc a b α β h).f (n + 1) ≫ c = _
    rw [← Category.assoc, signedLineInclusion_coneDesc]
  · change signedPlaneInclusion a b (n + 1) ≫ (coneDesc a b α β h).f (n + 1) ≫ c = _
    rw [← Category.assoc, signedPlaneInclusion_coneDesc]

end Generic

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
