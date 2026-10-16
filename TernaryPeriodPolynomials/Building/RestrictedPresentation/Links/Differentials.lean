module

public import TernaryPeriodPolynomials.Building.BadVertex.SquareCaps
public import TernaryPeriodPolynomials.Building.BadEdge.SquareCycles
public import TernaryPeriodPolynomials.Building.BadTriangle.NeighborCycles
public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Dictionary

@[expose] public section


/-!
# Appendix A: the fillings behind the three differentials (the first, second and third obstruction)

Formalized by Claude Sonnet 5.5.  The spectral sequence `eq:bad-filtration`
itself and its differentials are NOT formalized (the library proves Lemma A.1 and restricted acyclicity by chain-level fillings instead, `AmbientTwoFilling`, `Exports/AppendixAAcyclicity`); here are the concrete
combinatorial claims used in that part of the proof.

Conventions: a basis `g` of `ℤ³` has columns `b = g e₀`, `c = g e₁`, `w = g e₂` and the augmented frame `{b, c, w, b + c}`; `b, c` bad means `columnResidue g 0 = 0 = columnResidue g 1` (so `w` is good).

* **First differential.**  `five_good_vectors`: `A = w, B = w + b, C = w + c, D = w + b + c, W = A + D = B + C` and the lines of the library's `capLine g i` are their spans; `five_vertices_good`: all five are good;
  `square_cap_fills`: the all-good augmented-frame chain `[W,B,C,D] - [W,A,C,D] + [W,A,B,D] - [W,A,B,C]` (`eq:square-cap`) lies in `chains good 4` (each of its four tetrahedra is an augmented frame of the good complex)
  and has boundary `∂[A,B,C,D]`; `tetraSphere_square` / `tetraSpheres_filled`: every tetrahedral generator `∂[u_k,u_{k+1},v_l,v_{l+1}]` of Lemma A.1 is `± ∂[A,B,C,D]` for a basis `g'` with two bad columns, hence
  bounds the square cap in `Y` (normalizing the two lifted quotient vectors to the same covector value, the difference of `u_k` and `v_l` is the bad vector `c`).
* **Second differential.**  `second_differential_fillings`: the unit square `[A,B] + [B,D] + [D,C] + [C,A]` of the good link of the bad edge `{b, c}` (it is the library's `squareLoop g (0,0)`, `unitSquare_eq_squareLoop`)
  is filled in the link `L_b` by `[A,B,C] + [B,D,C]` and in `L_c` by `[A,B,D] + [A,D,C]` (both lie in the chains of the respective good links), and their difference is `-∂[A,B,C,D]`, `= -∂(squareCap g)`.
* **Third differential.**  `third_differential_cycle`: the eight-term chain `Z₀` of `eq:triangle-cycle` (for the vectors `u, v, s = u + v, w, w' = w + u, q = v - w` of a basis `g`) lies in `chains ambient 4`, each
  tetrahedron is an augmented frame, and `∂Z₀ = 0`; `third_differential_leading`: its three-bad component is `-[w,v,u,s] + [v,u,w',s]`, which is the join of the bad triangle `[u,v,s]` with `[w'] - [w]`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixA.Links

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.AugmentedBadFaces TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction
  TernaryPoly.AugmentedSquareCaps


private theorem res_two_ne_zero (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    columnResidue g 2 ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_columnResidue_ne_zero g
  rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) j with rfl | rfl | rfl
  · exact absurd h0 hj
  · exact absurd h1 hj
  · exact hj

/-! ### The first differential -/

/-- The integral vector `A, B, C, D, W` of the cap, in the rational space of the basis `g`. -/
def capVec (g : IntegralGL) (i : Fin 5) : Space :=
  rationalRepresentation g (rationalVector (capVector i))

/-- **The five vectors of the square cap**: with `b = g e₀`, `c = g e₁`, `w = g e₂`:
`A = w`, `B = w + b`, `C = w + c`, `D = w + b + c`, `W = A + D = B + C`; the lines are their spans. -/
theorem five_good_vectors (g : IntegralGL) :
    capVec g 0 = rationalRepresentation g (Pi.single 2 1) ∧
    capVec g 1 = rationalRepresentation g (Pi.single 2 1) + rationalRepresentation g (Pi.single 0 1) ∧
    capVec g 2 = rationalRepresentation g (Pi.single 2 1) + rationalRepresentation g (Pi.single 1 1) ∧
    capVec g 3 = rationalRepresentation g (Pi.single 2 1) + rationalRepresentation g (Pi.single 0 1) +
      rationalRepresentation g (Pi.single 1 1) ∧
    capVec g 4 = capVec g 0 + capVec g 3 ∧ capVec g 4 = capVec g 1 + capVec g 2 ∧
    (∀ i : Fin 5, (capLine g i).val = Submodule.span ℚ {capVec g i}) := by
  have e0 : rationalVector (capVector 0) = (Pi.single 2 1 : Space) := by
    funext j; fin_cases j <;> simp [rationalVector, capVector]
  have e1 : rationalVector (capVector 1) = (Pi.single 2 1 : Space) + Pi.single 0 1 := by
    funext j; fin_cases j <;> simp [rationalVector, capVector]
  have e2 : rationalVector (capVector 2) = (Pi.single 2 1 : Space) + Pi.single 1 1 := by
    funext j; fin_cases j <;> simp [rationalVector, capVector]
  have e3 : rationalVector (capVector 3) = (Pi.single 2 1 : Space) + Pi.single 0 1 + Pi.single 1 1 := by
    funext j; fin_cases j <;> simp [rationalVector, capVector]
  have e4 : rationalVector (capVector 4) = rationalVector (capVector 0) + rationalVector (capVector 3) := by
    funext j; fin_cases j <;> simp [rationalVector, capVector]
    norm_num
  have e5 : rationalVector (capVector 4) = rationalVector (capVector 1) + rationalVector (capVector 2) := by
    funext j; fin_cases j <;> simp [rationalVector, capVector]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun i => rfl⟩
  · unfold capVec; rw [e0]
  · unfold capVec; rw [e1, map_add]
  · unfold capVec; rw [e2, map_add]
  · unfold capVec; rw [e3, map_add, map_add]
  · unfold capVec; rw [e4, map_add]
  · unfold capVec; rw [e5, map_add]

/-- **All five vertices of the square cap are good** (`b, c` bad, `w` good). -/
theorem five_vertices_good (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (i : Fin 5) : Good (capLine g i).val :=
  capLine_good g h0 h1 (res_two_ne_zero g h0 h1) i

/-- **The square cap** (`eq:square-cap`): the all-good chain `[W,B,C,D] - [W,A,C,D] + [W,A,B,D] - [W,A,B,C]`
is a chain of the good complex `Y` (each tetrahedron an augmented frame of `Y`) and has boundary `∂[A,B,C,D]`. -/
theorem square_cap_fills (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    squareCap g = simplex [W g, B g, C g, D g] - simplex [W g, A g, C g, D g] +
        simplex [W g, A g, B g, D g] - simplex [W g, A g, B g, C g] ∧
      squareCap g ∈ chains AugmentedFrameComplex.good 4 ∧
      boundary (squareCap g) = boundary (simplex [A g, B g, C g, D g]) ∧
      (∀ i : Fin 4, augmentedFrame (g * capGL i) = capFace g i ∧
        capFace g i ∈ AugmentedFrameComplex.good) :=
  ⟨rfl, squareCap_mem_chains g h0 h1 (res_two_ne_zero g h0 h1), squareCap_boundary g,
    fun i => ⟨augmentedFrame_capGL_eq_face g i, capFace_good g h0 h1 (res_two_ne_zero g h0 h1) i⟩⟩

private theorem simplex_swap_last' {V : Type*} (a b c d : V) :
    simplex [a, b, d, c] = -simplex [a, b, c, d] := by
  have h := congrArg (fun t => cons a (cons b t)) (simplex_swap_eq_neg d c [])
  simpa only [cons_simplex, map_neg] using h

/-- **Each tetrahedral generator `∂[u_k,u_{k+1},v_l,v_{l+1}]` is `± ∂[A,B,C,D]` of a square cap** (`g = (b, X, Y)`, `b` bad, `X, Y` good):
for a basis `g'` with two bad columns, `tetraSphere g k l = ε ∂[A g', B g', C g', D g']`, `ε = ±1`. -/
theorem tetraSphere_square (g : IntegralGL) (hb : columnResidue g 0 = 0) (hX : columnResidue g 1 ≠ 0)
    (hY : columnResidue g 2 ≠ 0) (k l : ℤ) :
    ∃ (g' : IntegralGL) (ε : ℚ), (ε = 1 ∨ ε = -1) ∧ columnResidue g' 0 = 0 ∧ columnResidue g' 1 = 0 ∧
      columnResidue g' 2 ≠ 0 ∧
      TernaryPeriodPolynomials.Argument.AppendixALink.tetraSphere g k l =
        ε • boundary (simplex [A g', B g', C g', D g']) := by
  rcases BadVertexSquareCaps.nonzero_residues_equal_or_opposite _ _ hX hY with he | he
  · refine ⟨BadVertexSquareCaps.squareBasis g 1 isUnit_one k l, 1, Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · rw [BadVertexSquareCaps.squareBasis_residue_zero]; exact hb
    · rw [BadVertexSquareCaps.squareBasis_residue_one, hb, zero_mul, zero_sub, ← he]
      simp
    · rw [BadVertexSquareCaps.squareBasis_residue_two, hb, zero_mul, zero_add]; exact hX
    · rw [one_smul]
      unfold TernaryPeriodPolynomials.Argument.AppendixALink.tetraSphere
      change _ = boundary (simplex [capLine _ 0, capLine _ 1, capLine _ 2, capLine _ 3])
      rw [BadVertexSquareCaps.capLine_squareBasis_zero, BadVertexSquareCaps.capLine_squareBasis_one,
        BadVertexSquareCaps.capLine_positive_two, BadVertexSquareCaps.capLine_positive_three]
  · refine ⟨BadVertexSquareCaps.squareBasis g (-1) isUnit_neg_one k (-l - 1), -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · rw [BadVertexSquareCaps.squareBasis_residue_zero]; exact hb
    · rw [BadVertexSquareCaps.squareBasis_residue_one, hb, zero_mul, zero_sub, he]
      simp
    · rw [BadVertexSquareCaps.squareBasis_residue_two, hb, zero_mul, zero_add]; exact hX
    · rw [neg_one_smul]
      unfold TernaryPeriodPolynomials.Argument.AppendixALink.tetraSphere
      change _ = -boundary (simplex [capLine _ 0, capLine _ 1, capLine _ 2, capLine _ 3])
      rw [BadVertexSquareCaps.capLine_squareBasis_zero, BadVertexSquareCaps.capLine_squareBasis_one,
        BadVertexSquareCaps.capLine_negative_two, BadVertexSquareCaps.capLine_negative_three,
        simplex_swap_last', map_neg]

/-- **The square cap fills every tetrahedral generator of `H₂(L_b)`** (Lemma A.1): for every `c ∈ tetraSpheres b`
there are a basis `g'` with two bad columns and `ε = ±1` with `c = ε ∂[A,B,C,D]`, the boundary of the all-good chain `ε • squareCap g'` of `Y`. -/
theorem tetraSpheres_filled {b : RationalLine} (hb : ¬ Good b.val)
    {c : Chain RationalLine} (hc : c ∈ TernaryPeriodPolynomials.Argument.AppendixALink.tetraSpheres b) :
    ∃ (g' : IntegralGL) (ε : ℚ), (ε = 1 ∨ ε = -1) ∧ columnResidue g' 0 = 0 ∧ columnResidue g' 1 = 0 ∧
      columnResidue g' 2 ≠ 0 ∧ c = ε • boundary (simplex [A g', B g', C g', D g']) ∧
      ε • squareCap g' ∈ chains AugmentedFrameComplex.good 4 ∧
      boundary (ε • squareCap g') = c := by
  obtain ⟨g, k, l, hgb, hx, hy, rfl⟩ := hc
  have hbad : ¬Good (augmentedLine g 0).val := by rw [hgb]; exact hb
  have hb0 : columnResidue g 0 = 0 := AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad
  have hX : columnResidue g 1 ≠ 0 := (BadVertexSimplexNormalForm.fiberLine_good_iff g hb0 0 0).mp hx
  have hY : columnResidue g 2 ≠ 0 := (BadVertexSimplexNormalForm.fiberLine_good_iff g hb0 1 0).mp hy
  obtain ⟨g', ε, hε, h0, h1, h2, hs⟩ := tetraSphere_square g hb0 hX hY k l
  refine ⟨g', ε, hε, h0, h1, h2, hs, ?_, ?_⟩
  · exact (chains AugmentedFrameComplex.good 4).smul_mem ε (squareCap_mem_chains g' h0 h1 h2)
  · rw [map_smul, squareCap_boundary, hs]


/-! ### The second differential -/

section SecondDifferential

local instance linksSecondDifferentialDecEq : DecidableEq RationalLine := Classical.decEq _


private theorem swap3 {V : Type*} (a b c : V) : simplex [a, c, b] = -simplex [a, b, c] := by
  have h := congrArg (cons a) (simplex_swap_eq_neg c b [])
  simpa only [cons_simplex, map_neg] using h

/-- The explicit matrices (columns `A,b,C`; `C,b,B`; `B,c,A`; `A,c,D`) of the four augmented frames `{b,A,B,C}`, `{b,B,D,C}`, `{c,A,B,D}`, `{c,A,D,C}`. -/
def secMatrix : Fin 4 → Mat :=
  ![!![0,1,0;0,0,1;1,0,1], !![0,1,1;1,0,0;1,0,1], !![1,0,0;0,1,0;1,0,1], !![0,0,1;0,1,1;1,0,1]]

def secIndex : Fin 4 → Fin 4 → Fin 6 := ![![2,0,4,3], ![4,0,3,5], ![3,1,2,5], ![2,1,5,4]]

theorem secMatrix_unit (i : Fin 4) : IsUnit (secMatrix i).det := by
  have h : ∀ j : Fin 4, (secMatrix j).det = (![1,-1,1,-1] : Fin 4 → ℤ) j := by decide +kernel
  rw [h]
  fin_cases i <;> norm_num

def secGL (i : Fin 4) : IntegralGL := Matrix.nonsingInvUnit (secMatrix i) (secMatrix_unit i)

private theorem secMatrix_template (i j : Fin 4) :
    (secMatrix i).mulVec (GoodAugmentedNormalForm.integralTemplate j) =
      BadEdgeSquareCycles.coneVector (secIndex i j) := by
  exact (by decide +kernel : ∀ i j : Fin 4,
    (secMatrix i).mulVec (GoodAugmentedNormalForm.integralTemplate j) =
      BadEdgeSquareCycles.coneVector (secIndex i j)) i j

private theorem coneLine_val' (g : IntegralGL) (i : Fin 6) :
    (BadEdgeSquareCycles.coneLine g i).val =
      Submodule.span ℚ {rationalRepresentation g (rationalVector (BadEdgeSquareCycles.coneVector i))} := by
  fin_cases i
  · change Submodule.span ℚ {rationalRepresentation g (template 0)} =
      Submodule.span ℚ {rationalRepresentation g (rationalVector (BadEdgeSquareCycles.coneVector 0))}
    rw [show rationalVector (BadEdgeSquareCycles.coneVector 0) = template 0 by decide +kernel]
  · change Submodule.span ℚ {rationalRepresentation g (template 1)} =
      Submodule.span ℚ {rationalRepresentation g (rationalVector (BadEdgeSquareCycles.coneVector 1))}
    rw [show rationalVector (BadEdgeSquareCycles.coneVector 1) = template 1 by decide +kernel]
  · rfl
  · rfl
  · rfl
  · rfl

theorem augmentedLine_secGL (g : IntegralGL) (i j : Fin 4) :
    augmentedLine (g * secGL i) j = BadEdgeSquareCycles.coneLine g (secIndex i j) := by
  apply Subtype.ext
  rw [coneLine_val']
  change Submodule.span ℚ {rationalRepresentation (g * secGL i) (template j)} = _
  rw [map_mul, LinearEquiv.mul_apply]
  have he : rationalRepresentation (secGL i) (template j) =
      rationalVector (BadEdgeSquareCycles.coneVector (secIndex i j)) := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate, ← rationalVector_mulVec]
    exact congrArg rationalVector (secMatrix_template i j)
  rw [he]

/-- The four vertex sets `{b,A,B,C}`, `{b,B,D,C}`, `{c,A,B,D}`, `{c,A,D,C}` are augmented frames. -/
def secFace (g : IntegralGL) : Fin 4 → Finset RationalLine :=
  ![{augmentedLine g 0, A g, B g, C g}, {augmentedLine g 0, B g, D g, C g},
    {augmentedLine g 1, A g, B g, D g}, {augmentedLine g 1, A g, D g, C g}]

theorem secFace_frame (g : IntegralGL) (i : Fin 4) : secFace g i = augmentedFrame (g * secGL i) := by
  unfold augmentedFrame
  rw [show augmentedLine (g * secGL i) = (fun j => BadEdgeSquareCycles.coneLine g (secIndex i j)) from
    funext (augmentedLine_secGL g i), show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  fin_cases i <;> ext L <;>
    simp [secFace, secIndex, BadEdgeSquareCycles.coneLine, BadEdgeSquareCycles.u, BadEdgeSquareCycles.v,
      or_comm, or_left_comm]

theorem secFace_ambient (g : IntegralGL) (i : Fin 4) : secFace g i ∈ ambient := by
  rw [secFace_frame]; exact augmentedFrame_mem _

private theorem simplex_mem_link (u : RationalLine) (l : List RationalLine) (hne : l ≠ [])
    (hamb : {u} ∪ l.toFinset ∈ ambient) (hgood : ∀ L ∈ l, Good L.val) :
    simplex l ∈ chains (augmentedGoodLink {u}) l.length := by
  refine simplex_mem_chains _ l (Or.inr ?_)
  unfold augmentedGoodLink
  rw [mem_goodLink]
  exact ⟨⟨l.head hne, List.mem_toFinset.mpr (List.head_mem hne)⟩, hamb,
    fun a ha => hgood a (List.mem_toFinset.mp ha)⟩

/-- The oriented unit square `A → B → D → C → A` (a 1-cycle of the good link of the bad edge `{b,c}`). -/
def unitSquare (g : IntegralGL) : Chain RationalLine :=
  simplex [A g, B g] + simplex [B g, D g] + simplex [D g, C g] + simplex [C g, A g]

/-- Its filling in the link `L_b`: `[A,B,C] + [B,D,C]`. -/
def fillingB (g : IntegralGL) : Chain RationalLine := simplex [A g, B g, C g] + simplex [B g, D g, C g]

/-- Its filling in the link `L_c`: `[A,B,D] + [A,D,C]`. -/
def fillingC (g : IntegralGL) : Chain RationalLine := simplex [A g, B g, D g] + simplex [A g, D g, C g]

/-- The unit square is the library's square loop at the origin of the grid of the bad-edge link. -/
theorem unitSquare_eq_squareLoop (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) :
    unitSquare g = (BadEdgeLinkChains.squareLoop g h0 h1 h2 (0, 0)).val := by
  rw [BadEdgeLinkChains.squareLoop_val]
  have hA : A g = BadEdgeLinkVertices.coordinateLine g (0, 0) := by
    simpa [BadEdgeSquareCycles.squarePoint] using BadEdgeSquareCycles.capLine_coordinate g 0
  have hB : B g = BadEdgeLinkVertices.coordinateLine g (1, 0) := by
    simpa [BadEdgeSquareCycles.squarePoint] using BadEdgeSquareCycles.capLine_coordinate g 1
  have hC : C g = BadEdgeLinkVertices.coordinateLine g (0, 1) := by
    simpa [BadEdgeSquareCycles.squarePoint] using BadEdgeSquareCycles.capLine_coordinate g 2
  have hD : D g = BadEdgeLinkVertices.coordinateLine g (1, 1) := by
    simpa [BadEdgeSquareCycles.squarePoint] using BadEdgeSquareCycles.capLine_coordinate g 3
  have e := simplex_swap_eq_neg (C g) (A g) []
  have e' := simplex_swap_eq_neg (D g) (C g) []
  unfold unitSquare
  rw [e, e', hA, hB, hC, hD]
  simp only [zero_add]
  abel

/-- **The second differential vanishes on unit squares**.  For a basis `g` with bad columns `b, c`
(`A,B,C,D` as above): `[A,B,C] + [B,D,C]` is a chain of the good link of `b` and `[A,B,D] + [A,D,C]` a chain of the good link
of `c`, both with boundary the unit square; their difference is `-∂[A,B,C,D]`, which is the boundary of the all-good square cap. -/
theorem second_differential_fillings (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    fillingB g ∈ chains (augmentedGoodLink {augmentedLine g 0}) 3 ∧ boundary (fillingB g) = unitSquare g ∧
    fillingC g ∈ chains (augmentedGoodLink {augmentedLine g 1}) 3 ∧ boundary (fillingC g) = unitSquare g ∧
    fillingB g - fillingC g = -boundary (simplex [A g, B g, C g, D g]) ∧
    fillingB g - fillingC g = -boundary (squareCap g) ∧
    squareCap g ∈ chains AugmentedFrameComplex.good 4 := by
  have h2 := res_two_ne_zero g h0 h1
  have hg := five_vertices_good g h0 h1
  have mem : ∀ (u : RationalLine) (i : Fin 4) (l : List RationalLine),
      l.toFinset ∪ {u} = secFace g i → l ≠ [] → (∀ L ∈ l, Good L.val) →
      simplex l ∈ chains (augmentedGoodLink {u}) l.length := by
    intro u i l hs hne hgood
    apply simplex_mem_link u l hne _ hgood
    rw [Finset.union_comm, hs]
    exact secFace_ambient g i
  have s1 := swap3 (B g) (C g) (D g)
  have s2 := swap3 (A g) (C g) (D g)
  have e := simplex_swap_eq_neg (C g) (A g) []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, squareCap_mem_chains g h0 h1 h2⟩
  · apply (chains _ 3).add_mem
    · exact mem (augmentedLine g 0) 0 [A g, B g, C g] (by
        ext L; simp [secFace, or_comm, or_left_comm]) (by simp)
        (by intro L hL; simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
            rcases hL with rfl | rfl | rfl <;> exact hg _)
    · exact mem (augmentedLine g 0) 1 [B g, D g, C g] (by
        ext L; simp [secFace, or_comm, or_left_comm]) (by simp)
        (by intro L hL; simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
            rcases hL with rfl | rfl | rfl <;> exact hg _)
  · simp only [fillingB, unitSquare, map_add, boundary_cons, boundary_nil, cons_simplex, map_sub, map_zero,
      sub_zero]
    rw [e]; abel
  · apply (chains _ 3).add_mem
    · exact mem (augmentedLine g 1) 2 [A g, B g, D g] (by
        ext L; simp [secFace, or_comm, or_left_comm]) (by simp)
        (by intro L hL; simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
            rcases hL with rfl | rfl | rfl <;> exact hg _)
    · exact mem (augmentedLine g 1) 3 [A g, D g, C g] (by
        ext L; simp [secFace, or_comm, or_left_comm]) (by simp)
        (by intro L hL; simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
            rcases hL with rfl | rfl | rfl <;> exact hg _)
  · simp only [fillingC, unitSquare, map_add, boundary_cons, boundary_nil, cons_simplex, map_sub, map_zero,
      sub_zero]
    rw [e]; abel
  · simp only [fillingB, fillingC, map_sub, boundary_cons, boundary_nil, cons_simplex, map_zero, sub_zero]
    rw [s1, s2]; abel
  · rw [squareCap_boundary]
    simp only [fillingB, fillingC, map_sub, boundary_cons, boundary_nil, cons_simplex, map_zero, sub_zero]
    rw [s1, s2]; abel

end SecondDifferential

/-! ### The third differential -/

/-- The eight-term chain `Z₀` of `eq:triangle-cycle`, written with the named lines `u, v, s = u + v, w, w' = w + u, q = v - w`. -/
theorem third_differential_cycle (g : IntegralGL) :
    AugmentedEightTermCycle.Z g =
        -simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.q g, AugmentedEightTermCycle.v g,
          AugmentedEightTermCycle.s g]
        - simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.v g, AugmentedEightTermCycle.u g,
          AugmentedEightTermCycle.s g]
        - simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.u g, AugmentedEightTermCycle.w2 g,
          AugmentedEightTermCycle.s g]
        + simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.q g, AugmentedEightTermCycle.v g,
          AugmentedEightTermCycle.w2 g]
        + simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.q g, AugmentedEightTermCycle.w2 g,
          AugmentedEightTermCycle.s g]
        + simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.v g, AugmentedEightTermCycle.u g,
          AugmentedEightTermCycle.w2 g]
        + simplex [AugmentedEightTermCycle.q g, AugmentedEightTermCycle.v g, AugmentedEightTermCycle.w2 g,
          AugmentedEightTermCycle.s g]
        + simplex [AugmentedEightTermCycle.v g, AugmentedEightTermCycle.u g, AugmentedEightTermCycle.w2 g,
          AugmentedEightTermCycle.s g] ∧
      AugmentedEightTermCycle.Z g ∈ chains ambient 4 ∧
      (∀ i : Fin 8, (AugmentedEightTermCycle.termList g i).toFinset =
        augmentedFrame (g * AugmentedEightTermCycle.basisChange i)) ∧
      boundary (AugmentedEightTermCycle.Z g) = 0 :=
  ⟨rfl, AugmentedEightTermCycle.Z_mem_chains g, AugmentedEightTermCycle.termList_toFinset g,
    AugmentedEightTermCycle.boundary_Z g⟩

/-- The relations that make each tetrahedron an augmented frame: `v = w + q`, `s = u + v`, `w' = w + u`, `s = q + w'`
(as vectors of the basis `g`), with `u = b`, `v = c`, `w = g e₂`; and the bad/good pattern when `b, c` are bad. -/
theorem third_differential_vectors (g : IntegralGL) :
    let vec := fun i => rationalRepresentation g (rationalVector (AugmentedEightTermCycle.cycleVector i))
    vec 0 = rationalRepresentation g (Pi.single 0 1) ∧ vec 1 = rationalRepresentation g (Pi.single 1 1) ∧
    vec 2 = rationalRepresentation g (Pi.single 2 1) ∧
    vec 1 = vec 2 + vec 5 ∧ vec 3 = vec 0 + vec 1 ∧ vec 4 = vec 2 + vec 0 ∧ vec 3 = vec 5 + vec 4 := by
  intro vec
  have key : ∀ i j k : Fin 6, rationalVector (AugmentedEightTermCycle.cycleVector i) =
      rationalVector (AugmentedEightTermCycle.cycleVector j) +
        rationalVector (AugmentedEightTermCycle.cycleVector k) →
      vec i = vec j + vec k := by
    intro i j k h
    show rationalRepresentation g _ = rationalRepresentation g _ + rationalRepresentation g _
    rw [h, map_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show rationalRepresentation g _ = _
    congr 1; funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector]
  · show rationalRepresentation g _ = _
    congr 1; funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector]
  · show rationalRepresentation g _ = _
    congr 1; funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector]
  · exact key 1 2 5 (by funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector])
  · exact key 3 0 1 (by funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector])
  · exact key 4 2 0 (by funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector])
  · exact key 3 5 4 (by funext j; fin_cases j <;> simp [rationalVector, AugmentedEightTermCycle.cycleVector])

/-- With `b = u`, `c = v` bad: `u, v, s` are bad and `w, w', q` are good. -/
theorem third_differential_good_bad (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    (¬ Good (AugmentedEightTermCycle.u g).val ∧ ¬ Good (AugmentedEightTermCycle.v g).val ∧
      ¬ Good (AugmentedEightTermCycle.s g).val) ∧
    (Good (AugmentedEightTermCycle.w g).val ∧ Good (AugmentedEightTermCycle.w2 g).val ∧
      Good (AugmentedEightTermCycle.q g).val) := by
  have h2 := res_two_ne_zero g h0 h1
  have hi := AugmentedEightTermCycle.cycleLine_good_iff g h0 h1 h2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [AugmentedEightTermCycle.u, hi]; decide
  · rw [AugmentedEightTermCycle.v, hi]; decide
  · rw [AugmentedEightTermCycle.s, hi]; decide
  · exact (hi 2).mpr (by decide)
  · exact (hi 4).mpr (by decide)
  · exact (hi 5).mpr (by decide)

/-- **The highest filtered component of `Z₀`**: its terms with three bad vertices are `-[w,v,u,s] + [v,u,w',s]`, i.e. the join of the bad triangle `[u,v,s]` with the
adjacent complement difference `[w'] - [w]`. -/
theorem third_differential_leading (g : IntegralGL) (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    OrientedChainProjection.badCountProjection (fun L : RationalLine => Good L.val) 3 (AugmentedEightTermCycle.Z g) =
        -simplex [AugmentedEightTermCycle.w g, AugmentedEightTermCycle.v g, AugmentedEightTermCycle.u g,
          AugmentedEightTermCycle.s g] +
          simplex [AugmentedEightTermCycle.v g, AugmentedEightTermCycle.u g, AugmentedEightTermCycle.w2 g,
            AugmentedEightTermCycle.s g] ∧
      OrientedChainProjection.badCountProjection (fun L : RationalLine => Good L.val) 3
          (AugmentedEightTermCycle.Z g) =
        OrientedChainJoin.join
          (simplex [AugmentedEightTermCycle.u g, AugmentedEightTermCycle.v g, AugmentedEightTermCycle.s g])
          (simplex [AugmentedEightTermCycle.w2 g] - simplex [AugmentedEightTermCycle.w g]) :=
  ⟨AugmentedEightTermCycle.leading_badCount_three g h0 h1 (res_two_ne_zero g h0 h1),
    BadTriangleNeighborCycles.leading_eq_join g h0 h1 (res_two_ne_zero g h0 h1)⟩

end TernaryPeriodPolynomials.Argument.AppendixA.Links
