module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeCoordinates

@[expose] public section


/-!
# D2: the corner cohomology of the signed cone

For chain maps `a : F ⟶ L`, `b : F ⟶ P` of chain complexes of representations and `W` a representation,
`signedCone a b` is the total complex of the boundary of the arithmetic bordification (`F` the
complete-flag corners, `L`, `P` the line and plane faces; `TernaryPoly.SymmetricSpaceBoundaryFull`).
Its cochains `Hom(cone, W)` have the coordinates `signedConeHomSucc`: a corner component, a line
component and a plane component. This file records the coordinate form of the total coboundary and the
two facts used to identify the top cohomology of the boundary with a quotient of corner cocycles:

* `cone_coboundary_coordinates`: `δ(e, l, p) = (-d e + a^* l - b^* p, d l, d p)`;
* `corner_coboundary` (injectivity): a corner cocycle that is a total coboundary is a corner
  coboundary plus pullbacks of line and plane cocycles;
* `total_cocycle_cohomologous_corner` (surjectivity): if the line and plane cochains have no cohomology in
  the relevant degree, every total cocycle is cohomologous to a corner cocycle.

Hence, in degree `m + 2`, the corner cocycles modulo corner coboundaries and pullbacks of line and plane
cocycles are identified with the total cohomology; this is the cochain-level form of "boundary traces
are the functionals on `H⁴(∂M)`".

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex Preadditive Linear

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly.SymmetricSpaceBoundaryFull

section
variable {G : Type} [Group G] {F L P : ChainComplex (Rep.{0} ℚ G) ℕ}
  (a : F ⟶ L) (b : F ⟶ P) (W : Rep.{0} ℚ G)

/-- The cone cochain of degree `n + 1` with corner component `e` and zero face components. -/
def cornerCochain (n : ℕ) (e : F.X n ⟶ W) : (signedCone a b).X (n+1) ⟶ W :=
  (signedConeHomSucc a b W n).symm (e, 0, 0)

/-- Coordinates of the cone coboundary: corner, line, plane. -/
theorem cone_coboundary_coordinates (n : ℕ) (c : (signedCone a b).X (n+1) ⟶ W) :
    signedConeHomSucc a b W (n+1) ((signedCone a b).d (n+2) (n+1) ≫ c) =
      (-(F.d (n+1) n ≫ (signedConeHomSucc a b W n c).1) +
          a.f (n+1) ≫ (signedConeHomSucc a b W n c).2.1 -
          b.f (n+1) ≫ (signedConeHomSucc a b W n c).2.2,
        (L.d (n+2) (n+1) ≫ (signedConeHomSucc a b W n c).2.1,
          P.d (n+2) (n+1) ≫ (signedConeHomSucc a b W n c).2.2)) := by
  have hc := signedConeHomSucc_apply a b W n c
  rw [signedConeHomSucc_apply a b W (n+1)]
  rw [hc]
  apply Prod.ext
  · simp only
    rw [← Category.assoc, signedCornerInclusion_d_succ]
    simp only [add_comp, sub_comp, neg_comp, Category.assoc]
    abel
  apply Prod.ext
  · simp only
    rw [← Category.assoc, signedLineInclusion_d, Category.assoc]
  · simp only
    rw [← Category.assoc, signedPlaneInclusion_d, Category.assoc]


theorem cornerCochain_coords (n : ℕ) (e : F.X n ⟶ W) :
    signedConeHomSucc a b W n (cornerCochain a b W n e) = (e, 0, 0) :=
  (signedConeHomSucc a b W n).apply_symm_apply _

/-- A cone coboundary with vanishing face components exhibits its corner component as a
coboundary plus pullbacks of face cocycles. -/
theorem corner_coboundary (m : ℕ) (e : F.X (m+1) ⟶ W) (c' : (signedCone a b).X (m+1) ⟶ W)
    (h : (signedCone a b).d (m+2) (m+1) ≫ c' = cornerCochain a b W (m+1) e) :
    ∃ (e' : F.X m ⟶ W) (l' : L.X (m+1) ⟶ W) (p' : P.X (m+1) ⟶ W),
      L.d (m+2) (m+1) ≫ l' = 0 ∧ P.d (m+2) (m+1) ≫ p' = 0 ∧
      e = -(F.d (m+1) m ≫ e') + a.f (m+1) ≫ l' - b.f (m+1) ≫ p' := by
  refine ⟨(signedConeHomSucc a b W m c').1, (signedConeHomSucc a b W m c').2.1,
    (signedConeHomSucc a b W m c').2.2, ?_, ?_, ?_⟩
  · have := congrArg (fun z => (signedConeHomSucc a b W (m+1) z).2.1) h
    simp only [cone_coboundary_coordinates, cornerCochain_coords] at this
    exact this
  · have := congrArg (fun z => (signedConeHomSucc a b W (m+1) z).2.2) h
    simp only [cone_coboundary_coordinates, cornerCochain_coords] at this
    exact this
  · have := congrArg (fun z => (signedConeHomSucc a b W (m+1) z).1) h
    simp only [cone_coboundary_coordinates, cornerCochain_coords] at this
    exact this.symm

/-- **Surjectivity of the corner map.** If the line and plane cochain complexes have no cohomology
in degree `m + 2`, every total cocycle of degree `m + 2` is cohomologous to a corner cocycle. -/
theorem total_cocycle_cohomologous_corner (m : ℕ)
    (hL : ∀ l : L.X (m+2) ⟶ W, L.d (m+3) (m+2) ≫ l = 0 → ∃ l' : L.X (m+1) ⟶ W,
      L.d (m+2) (m+1) ≫ l' = l)
    (hP : ∀ p : P.X (m+2) ⟶ W, P.d (m+3) (m+2) ≫ p = 0 → ∃ p' : P.X (m+1) ⟶ W,
      P.d (m+2) (m+1) ≫ p' = p)
    (c : (signedCone a b).X (m+2) ⟶ W) (hc : (signedCone a b).d (m+3) (m+2) ≫ c = 0) :
    ∃ (e : F.X (m+1) ⟶ W) (c' : (signedCone a b).X (m+1) ⟶ W), F.d (m+2) (m+1) ≫ e = 0 ∧
      c = cornerCochain a b W (m+1) e + (signedCone a b).d (m+2) (m+1) ≫ c' := by
  have hcoords := cone_coboundary_coordinates a b W (m+1) c
  rw [hc] at hcoords
  have hz : signedConeHomSucc a b W (m+2) 0 = 0 := map_zero _
  rw [hz] at hcoords
  have h1 := congrArg (fun z => z.1) hcoords
  have h2 := congrArg (fun z => z.2.1) hcoords
  have h3 := congrArg (fun z => z.2.2) hcoords
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2 h3
  obtain ⟨l', hl'⟩ := hL _ h2.symm
  obtain ⟨p', hp'⟩ := hP _ h3.symm
  set e0 := (signedConeHomSucc a b W (m+1) c).1
  refine ⟨e0 - a.f (m+1) ≫ l' + b.f (m+1) ≫ p',
    (signedConeHomSucc a b W m).symm (0, l', p'), ?_, ?_⟩
  · have ha := HomologicalComplex.Hom.comm a (m+2) (m+1)
    have hb := HomologicalComplex.Hom.comm b (m+2) (m+1)
    rw [comp_add, comp_sub, ← Category.assoc, ← Category.assoc, ← ha, ← hb]
    simp only [Category.assoc, hl', hp']
    have h1' : -(F.d (m+2) (m+1) ≫ e0) + a.f (m+2) ≫ (signedConeHomSucc a b W (m+1) c).2.1 -
        b.f (m+2) ≫ (signedConeHomSucc a b W (m+1) c).2.2 = 0 := by
      exact h1.symm
    rw [← neg_eq_zero]
    rw [← h1']
    abel
  · apply (signedConeHomSucc a b W (m+1)).injective
    rw [map_add, cornerCochain_coords, cone_coboundary_coordinates]
    have hc0 : signedConeHomSucc a b W m ((signedConeHomSucc a b W m).symm (0, l', p')) = (0, l', p') :=
      (signedConeHomSucc a b W m).apply_symm_apply _
    rw [hc0]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change e0 = (e0 - a.f (m+1) ≫ l' + b.f (m+1) ≫ p') +
        (-(F.d (m+1) m ≫ 0) + a.f (m+1) ≫ l' - b.f (m+1) ≫ p')
      rw [comp_zero, neg_zero, zero_add]
      abel
    · change _ = (0 : _) + L.d (m+2) (m+1) ≫ l'
      rw [zero_add, hl']
    · change _ = (0 : _) + P.d (m+2) (m+1) ≫ p'
      rw [zero_add, hp']

end

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
