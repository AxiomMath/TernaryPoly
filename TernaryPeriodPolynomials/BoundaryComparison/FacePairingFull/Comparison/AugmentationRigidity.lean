module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeCoordinates
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Desc

@[expose] public section


/-!
# Chain maps into a degree-zero complex are rigid under homotopy

Two chain maps `X ⟶ single₀ T` from a chain complex to the complex concentrated in degree zero that are
homotopic are equal (the homotopy terms vanish for lack of differentials), and a chain map `X ⟶ single₀ T`
is determined by its degree-zero component.  Consequently, for a chain homotopy equivalence
`e : X ≃ Y` and chain maps `a : X ⟶ single₀ T`, `b : Y ⟶ single₀ T` with `e.hom ≫ b = a`, also
`e.inv ≫ a = b` (`inv_comp_eq_of_hom_comp`).  Two morphisms out of degree zero of a signed cone are equal as soon as
their restrictions to the line and plane summands agree (`signedCone_ext_zero`); consequently a chain map out of a
signed cone into `single₀ T` is determined by its line and plane components (`signedCone_ext_single₀`,
`cone_desc_comp_single₀`, `cone_map_desc_single₀`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

section Generic

variable {C : Type*} [Category* C] [Abelian C] {X Y : ChainComplex C ℕ} {T : C}

/-- Homotopic chain maps into `single₀ T` are equal. -/
theorem eq_of_homotopy_single₀ {f g : X ⟶ (ChainComplex.single₀ C).obj T} (h : Homotopy f g) :
    f = g := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  have h0 := h.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h0
  change f.f 0 = g.f 0
  have hd : ((ChainComplex.single₀ C).obj T).d (0 + 1) 0 = 0 :=
    (Limits.IsZero.eq_of_src (Limits.isZero_zero C) _ _)
  rw [h0, hd]
  simp only [zero_add, Limits.comp_zero]

/-- A homotopy-inverse preserves a chain map to `single₀ T`. -/
theorem inv_comp_eq_of_hom_comp (e : HomotopyEquiv X Y) (a : X ⟶ (ChainComplex.single₀ C).obj T)
    (b : Y ⟶ (ChainComplex.single₀ C).obj T) (h : e.hom ≫ b = a) : e.inv ≫ a = b := by
  rw [← h, ← Category.assoc]
  have H : Homotopy ((e.inv ≫ e.hom) ≫ b) (𝟙 Y ≫ b) := e.homotopyInvHomId.compRight b
  rw [Category.id_comp] at H
  exact eq_of_homotopy_single₀ H

/-- Two chain maps into `single₀ T` with the same degree-zero component are equal. -/
theorem eq_of_f_zero_single₀ {f g : X ⟶ (ChainComplex.single₀ C).obj T} (h : f.f 0 = g.f 0) :
    f = g := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  exact Subtype.ext h

end Generic

section Cone

open TernaryPoly.SymmetricSpaceBoundaryFull

variable {G : Type} [Group G] {F L P : ChainComplex (Rep.{0} ℚ G) ℕ} (a : F ⟶ L) (b : F ⟶ P)
  {W : Rep.{0} ℚ G}

/-- Morphisms out of degree zero of a signed cone are determined by the line and plane restrictions. -/
theorem signedCone_ext_zero {f g : (signedCone a b).X 0 ⟶ W}
    (hL : signedLineInclusion a b 0 ≫ f = signedLineInclusion a b 0 ≫ g)
    (hP : signedPlaneInclusion a b 0 ≫ f = signedPlaneInclusion a b 0 ≫ g) : f = g := by
  apply (signedConeHomZero a b W).injective
  rw [signedConeHomZero_apply, signedConeHomZero_apply, hL, hP]

/-- Chain maps from a signed cone into `single₀ W` are determined by the line and plane restrictions in
degree zero. -/
theorem signedCone_ext_single₀ {f g : signedCone a b ⟶ (ChainComplex.single₀ (Rep.{0} ℚ G)).obj W}
    (hL : signedLineInclusion a b 0 ≫ f.f 0 = signedLineInclusion a b 0 ≫ g.f 0)
    (hP : signedPlaneInclusion a b 0 ≫ f.f 0 = signedPlaneInclusion a b 0 ≫ g.f 0) : f = g :=
  eq_of_f_zero_single₀ (signedCone_ext_zero a b hL hP)

end Cone

section ConeAug

open TernaryPoly.SymmetricSpaceBoundaryFull

variable {G : Type} [Group G] {F L P F' L' P' K : ChainComplex (Rep.{0} ℚ G) ℕ} {T : Rep.{0} ℚ G}
  (a : F ⟶ L) (b : F ⟶ P) (a' : F' ⟶ L') (b' : F' ⟶ P')

theorem signedLineInclusion_comp (g : signedCone a b ⟶ K) (n : ℕ) :
    signedLineInclusion a b n ≫ g.f n =
      (biprod.inl ≫ homotopyCofiber.inr (signedArrow a b) ≫ g).f n := by
  simp [signedLineInclusion]

theorem signedPlaneInclusion_comp (g : signedCone a b ⟶ K) (n : ℕ) :
    signedPlaneInclusion a b n ≫ g.f n =
      (biprod.inr ≫ homotopyCofiber.inr (signedArrow a b) ≫ g).f n := by
  simp [signedPlaneInclusion]

theorem signedLineInclusion_map {g : signedCone a b ⟶ signedCone a' b'} {uL : L ⟶ L'} {uP : P ⟶ P'}
    (h : homotopyCofiber.inr (signedArrow a b) ≫ g =
      biprod.map uL uP ≫ homotopyCofiber.inr (signedArrow a' b')) (n : ℕ) :
    signedLineInclusion a b n ≫ g.f n = uL.f n ≫ signedLineInclusion a' b' n := by
  rw [signedLineInclusion_comp, h]
  simp [signedLineInclusion]

theorem signedPlaneInclusion_map {g : signedCone a b ⟶ signedCone a' b'} {uL : L ⟶ L'} {uP : P ⟶ P'}
    (h : homotopyCofiber.inr (signedArrow a b) ≫ g =
      biprod.map uL uP ≫ homotopyCofiber.inr (signedArrow a' b')) (n : ℕ) :
    signedPlaneInclusion a b n ≫ g.f n = uP.f n ≫ signedPlaneInclusion a' b' n := by
  rw [signedPlaneInclusion_comp, h]
  simp [signedPlaneInclusion]

theorem signedLineInclusion_desc {g : signedCone a b ⟶ K} {α : L ⟶ K} {β : P ⟶ K}
    (h : homotopyCofiber.inr (signedArrow a b) ≫ g = biprod.desc α β) (n : ℕ) :
    signedLineInclusion a b n ≫ g.f n = α.f n := by
  rw [signedLineInclusion_comp, h]
  simp

theorem signedPlaneInclusion_desc {g : signedCone a b ⟶ K} {α : L ⟶ K} {β : P ⟶ K}
    (h : homotopyCofiber.inr (signedArrow a b) ≫ g = biprod.desc α β) (n : ℕ) :
    signedPlaneInclusion a b n ≫ g.f n = β.f n := by
  rw [signedPlaneInclusion_comp, h]
  simp

theorem coneDesc_congr {α α' : L ⟶ K} {β β' : P ⟶ K} (hα : α = α') (hβ : β = β')
    {h : a ≫ α = b ≫ β} {h' : a ≫ α' = b ≫ β'} : coneDesc a b α β h = coneDesc a b α' β' h' := by
  subst hα hβ
  rfl

/-- A chain map out of a signed cone, composed with a chain map to `single₀ T`, is the cone map built from the
line and plane components. -/
theorem cone_desc_comp_single₀ {g : signedCone a b ⟶ K} {α : L ⟶ K} {β : P ⟶ K}
    (h : homotopyCofiber.inr (signedArrow a b) ≫ g = biprod.desc α β)
    (A : K ⟶ (ChainComplex.single₀ (Rep.{0} ℚ G)).obj T) (h0 : a ≫ α ≫ A = b ≫ β ≫ A) :
    g ≫ A = coneDesc a b (α ≫ A) (β ≫ A) h0 := by
  apply signedCone_ext_single₀ a b
  · rw [comp_f, ← Category.assoc, signedLineInclusion_desc a b h, signedLineInclusion_coneDesc, comp_f]
  · rw [comp_f, ← Category.assoc, signedPlaneInclusion_desc a b h, signedPlaneInclusion_coneDesc, comp_f]

/-- Compatibility of the cone maps built from line and plane components with a cone morphism over
`uL`, `uP`. -/
theorem cone_map_desc_single₀ {g : signedCone a b ⟶ signedCone a' b'} {uL : L ⟶ L'} {uP : P ⟶ P'}
    (h : homotopyCofiber.inr (signedArrow a b) ≫ g =
      biprod.map uL uP ≫ homotopyCofiber.inr (signedArrow a' b'))
    (α' : L' ⟶ (ChainComplex.single₀ (Rep.{0} ℚ G)).obj T)
    (β' : P' ⟶ (ChainComplex.single₀ (Rep.{0} ℚ G)).obj T) (h' : a' ≫ α' = b' ≫ β')
    (α : L ⟶ (ChainComplex.single₀ (Rep.{0} ℚ G)).obj T)
    (β : P ⟶ (ChainComplex.single₀ (Rep.{0} ℚ G)).obj T) (h0 : a ≫ α = b ≫ β)
    (hL : uL ≫ α' = α) (hP : uP ≫ β' = β) :
    g ≫ coneDesc a' b' α' β' h' = coneDesc a b α β h0 := by
  apply signedCone_ext_single₀ a b
  · rw [comp_f, ← Category.assoc, signedLineInclusion_map a b a' b' h, Category.assoc,
      signedLineInclusion_coneDesc, signedLineInclusion_coneDesc, ← comp_f, hL]
  · rw [comp_f, ← Category.assoc, signedPlaneInclusion_map a b a' b' h, Category.assoc,
      signedPlaneInclusion_coneDesc, signedPlaneInclusion_coneDesc, ← comp_f, hP]

end ConeAug

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
