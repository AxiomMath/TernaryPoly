module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadCochain

@[expose] public section


/-!
# The Kostant identity of the level-three bridge at the bad line

For `U`-equivariant homogeneous one-cocycles `f` (coefficients `ρ`) and `g` (coefficients `ρ ∘ φ`)
at the lattice `latL0` of the bad line, the fiber-integration pairing `κ(f, g) = ⟨f ⌣ g, σ⟩` is
minus the bad-line Kostant value of the inhomogeneous cocycles `zBad f`, `wBad g`
(`kostantBad_eq_neg_K`).  The proof decomposes the crossed cocycle `zBad f` into an invariant part
and a coboundary: on the invariant part both sides are computed by the invariance of `dualPairing`
and the cocycle law of `g` at the inverse lattice elements, and on the coboundary part both sides
vanish by the closedness of `g`.  With the explicit evaluation of the bad-line Kostant value one
obtains, for even `n`,

  `κ(f, g) = (n+1)!/3 · binaryPairing (n+1) (Φ f) (Ψ g)`    (`kostantBad_eq_binaryPairing`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (uL0)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (kostant)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### Elementary facts -/

/-- A vector fixed by `c` is fixed by `c⁻¹`. -/
theorem fixed_inv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {c : G} {x : V} (h : ρ c x = x) : ρ c⁻¹ x = x := by
  have h' := congrArg (ρ c⁻¹) h
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h'
  exact h'.symm

/-- The first generator of the lattice is the line radical `radicalGenerator 0`. -/
theorem u10_eq : latL0.u 1 0 = radicalGenerator 0 := by
  change uL0 1 0 = radicalGenerator 0
  rw [radicalGenerator_zero, uL0_eq_lineUnipotent]
  simp

/-- The second generator of the lattice is the line radical `radicalGenerator 1`. -/
theorem u01_eq : latL0.u 0 1 = radicalGenerator 1 := by
  change uL0 0 1 = radicalGenerator 1
  rw [radicalGenerator_one, uL0_eq_lineUnipotent]
  simp

theorem hom_gen_zero : latL0.hom (integralRadicalGenerator 0) = latL0.u 1 0 := by
  change latL0.u (if (0 : Fin 2) = 0 then 1 else 0) (if (0 : Fin 2) = 1 then 1 else 0) =
    latL0.u 1 0
  simp

theorem hom_gen_one : latL0.hom (integralRadicalGenerator 1) = latL0.u 0 1 := by
  change latL0.u (if (1 : Fin 2) = 0 then 1 else 0) (if (1 : Fin 2) = 1 then 1 else 0) =
    latL0.u 0 1
  simp

/-- The anti-diagonal negation of the first generator is the inverse of the second lattice
generator. -/
theorem swapNeg_first : latL0.hom (swapNegHom radicalLatticeFirst) = (latL0.u 0 1)⁻¹ := by
  have h : swapNegHom radicalLatticeFirst = (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))⁻¹ := by
    apply Multiplicative.toAdd.injective
    simp [swapNegHom_toAdd, radicalLatticeFirst]
  rw [h, map_inv]
  rfl

/-- The anti-diagonal negation of the second generator is the inverse of the first lattice
generator. -/
theorem swapNeg_second : latL0.hom (swapNegHom radicalLatticeSecond) = (latL0.u 1 0)⁻¹ := by
  have h : swapNegHom radicalLatticeSecond = (Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ)))⁻¹ := by
    apply Multiplicative.toAdd.injective
    simp [swapNegHom_toAdd, radicalLatticeSecond]
  rw [h, map_inv]
  rfl

theorem rho_frame_cancel (n : ℕ) (y : HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter badFrame
      (rationalCoefficientComponent n trivialCharacter badFrame⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- The embedded binary forms are fixed by the first lattice generator. -/
theorem embed_fixed_a (n : ℕ) (p : Binary.HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter (latL0.u 1 0) (binaryHomogeneousEmbedding n p) =
      binaryHomogeneousEmbedding n p := by
  rw [u10_eq, radicalGenerator_zero]
  exact binaryHomogeneousEmbedding_lineUnipotent n 1 0 p

/-- The embedded binary forms are fixed by the second lattice generator. -/
theorem embed_fixed_b (n : ℕ) (p : Binary.HomogeneousPoly n) :
    rationalCoefficientComponent n trivialCharacter (latL0.u 0 1) (binaryHomogeneousEmbedding n p) =
      binaryHomogeneousEmbedding n p := by
  rw [u01_eq, radicalGenerator_one]
  exact binaryHomogeneousEmbedding_lineUnipotent n 0 1 p

/-! ### Decomposition of a crossed cocycle of the radical -/

/-- **A crossed cocycle of the bad-line radical is an invariant pair plus a coboundary.** -/
theorem badCrossed_decomp (n : ℕ) (positive : 0 < n)
    (z : crossedCocycles ((standardBadLineRepresentation n).comp SemidirectProduct.inl)) :
    ∃ (p0 p1 : Binary.HomogeneousPoly n) (v : HomogeneousPoly n),
      z.val (integralRadicalGenerator 0) = binaryHomogeneousEmbedding n p0 +
        (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) v - v) ∧
      z.val (integralRadicalGenerator 1) = binaryHomogeneousEmbedding n p1 +
        (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) v - v) := by
  obtain ⟨pair, hpair⟩ := standardRadicalH1_binaryPair_representative n positive
    ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ z)
  have hdiff : explicitBinaryPairCocycle n pair - z ∈
      crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl) := by
    rw [← Submodule.Quotient.eq]
    exact hpair
  obtain ⟨v, hv⟩ := hdiff
  have hz : ∀ i : Fin 2, z.val (integralRadicalGenerator i) =
      binaryHomogeneousEmbedding n (if i = 0 then pair.1 else pair.2) +
        (rationalCoefficientComponent n trivialCharacter (radicalGenerator i) (-v) - (-v)) := by
    intro i
    have h1 := congrArg (fun c => c.val (integralRadicalGenerator i)) hv
    change ((standardBadLineRepresentation n).comp SemidirectProduct.inl)
        (integralRadicalGenerator i) v - v =
      (explicitBinaryPairCocycle n pair).val (integralRadicalGenerator i) -
        z.val (integralRadicalGenerator i) at h1
    rw [rho_s_generator] at h1
    have h2 : z.val (integralRadicalGenerator i) =
        (explicitBinaryPairCocycle n pair).val (integralRadicalGenerator i) -
          (rationalCoefficientComponent n trivialCharacter (radicalGenerator i) v - v) := by
      rw [h1]
      abel
    have hE : (explicitBinaryPairCocycle n pair).val (integralRadicalGenerator i) =
        binaryHomogeneousEmbedding n (if i = 0 then pair.1 else pair.2) :=
      binaryPairRadicalCocycle_generator n pair i
    rw [h2, hE, map_neg]
    abel
  have e0 : (if (0 : Fin 2) = 0 then pair.1 else pair.2) = pair.1 := ite_eq_left rfl
  have e1 : (if (1 : Fin 2) = 0 then pair.1 else pair.2) = pair.2 := ite_eq_right (by decide)
  refine ⟨pair.1, pair.2, -v, ?_, ?_⟩
  · have h := hz 0
    rw [e0] at h
    exact h
  · have h := hz 1
    rw [e1] at h
    exact h

/-! ### The bad-line Kostant value of the invariant part -/

/-- `⟨P, w⟩_bad` for `w = wBad g` at the first generator, `P` fixed by the second lattice
generator. -/
theorem badW_first (n : ℕ) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g)
    {P : HomogeneousPoly n} (hP : rationalCoefficientComponent n trivialCharacter (latL0.u 0 1) P = P) :
    badDualForm n P (wBad n hg radicalLatticeFirst) =
      -dualPairing n P (g ![1, latL0.u 0 1]) := by
  have hc : latL0.u 0 1 ∈ latL0.sub := latL0.u_mem 0 1
  rw [wBad_apply, swapNeg_first, badDualForm_apply_aux, rho_frame_cancel,
    uCocycle_inv_gen hg hc, map_neg]
  have i := dualPairing_invariant n trivialCharacter (latL0.u 0 1)⁻¹ P (g ![1, latL0.u 0 1])
  rw [fixed_inv hP] at i
  exact congrArg Neg.neg i

/-- `⟨P, w⟩_bad` for `w = wBad g` at the second generator, `P` fixed by the first lattice
generator. -/
theorem badW_second (n : ℕ) {g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g)
    {P : HomogeneousPoly n} (hP : rationalCoefficientComponent n trivialCharacter (latL0.u 1 0) P = P) :
    badDualForm n P (wBad n hg radicalLatticeSecond) =
      -dualPairing n P (g ![1, latL0.u 1 0]) := by
  have hc : latL0.u 1 0 ∈ latL0.sub := latL0.u_mem 1 0
  rw [wBad_apply, swapNeg_second, badDualForm_apply_aux, rho_frame_cancel,
    uCocycle_inv_gen hg hc, map_neg]
  have i := dualPairing_invariant n trivialCharacter (latL0.u 1 0)⁻¹ P (g ![1, latL0.u 1 0])
  rw [fixed_inv hP] at i
  exact congrArg Neg.neg i

/-- **The algebra of the cup-product value**: for `z₀ = P₀ + (a v - v)`, `z₁ = P₁ + (b v - v)` with
`a P₀ = P₀`, `b P₁ = P₁` and the closedness of the dual values. -/
theorem bad_kappa_special (n : ℕ) (a b : RationalGL3) (P0 P1 v H0 H1 : HomogeneousPoly n)
    (hPa : rationalCoefficientComponent n trivialCharacter a P0 = P0)
    (hPb : rationalCoefficientComponent n trivialCharacter b P1 = P1)
    (hcl : dualRep (dualityData n trivialCharacter) a H1 - H1 =
      dualRep (dualityData n trivialCharacter) b H0 - H0) :
    dualPairing n (P0 + (rationalCoefficientComponent n trivialCharacter a v - v))
          (dualRep (dualityData n trivialCharacter) a H1) -
        dualPairing n (P1 + (rationalCoefficientComponent n trivialCharacter b v - v))
          (dualRep (dualityData n trivialCharacter) b H0) =
      dualPairing n P0 H1 - dualPairing n P1 H0 := by
  have i1 : dualPairing n (rationalCoefficientComponent n trivialCharacter a P0)
      (dualRep (dualityData n trivialCharacter) a H1) = dualPairing n P0 H1 :=
    dualPairing_invariant n trivialCharacter a P0 H1
  have i2 : dualPairing n (rationalCoefficientComponent n trivialCharacter b P1)
      (dualRep (dualityData n trivialCharacter) b H0) = dualPairing n P1 H0 :=
    dualPairing_invariant n trivialCharacter b P1 H0
  have i3 : dualPairing n (rationalCoefficientComponent n trivialCharacter a v)
      (dualRep (dualityData n trivialCharacter) a H1) = dualPairing n v H1 :=
    dualPairing_invariant n trivialCharacter a v H1
  have i4 : dualPairing n (rationalCoefficientComponent n trivialCharacter b v)
      (dualRep (dualityData n trivialCharacter) b H0) = dualPairing n v H0 :=
    dualPairing_invariant n trivialCharacter b v H0
  rw [hPa] at i1
  rw [hPb] at i2
  have hcl' := congrArg (dualPairing n v) hcl
  simp only [map_sub] at hcl'
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  linear_combination i1 - i2 + i3 - i4 - hcl'

/-! ### The Kostant pairing in terms of the bad-line Kostant value -/

/-- **The fiber-integration pairing is minus the bad-line Kostant value of the inhomogeneous
cocycles.** -/
theorem kostantBad_eq_neg_K (n : ℕ) (positive : 0 < n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    kostant (dualityData n trivialCharacter).B latL0.σ f g =
      -kostantValue (badDualForm n) ((zBad n hf).val (integralRadicalGenerator 0))
        ((zBad n hf).val (integralRadicalGenerator 1)) (wBad n hg radicalLatticeSecond)
        (wBad n hg radicalLatticeFirst) := by
  obtain ⟨p0, p1, v, hz0, hz1⟩ := badCrossed_decomp n positive (zBad n hf)
  have ha : latL0.u 1 0 ∈ latL0.sub := latL0.u_mem 1 0
  have hb : latL0.u 0 1 ∈ latL0.sub := latL0.u_mem 0 1
  -- the generator values of `f`
  have hf0 : f ![1, latL0.u 1 0] = binaryHomogeneousEmbedding n p0 +
      (rationalCoefficientComponent n trivialCharacter (latL0.u 1 0) v - v) := by
    have h : f ![1, latL0.hom (integralRadicalGenerator 0)] = _ := hz0
    rw [hom_gen_zero, ← u10_eq] at h
    exact h
  have hf1 : f ![1, latL0.u 0 1] = binaryHomogeneousEmbedding n p1 +
      (rationalCoefficientComponent n trivialCharacter (latL0.u 0 1) v - v) := by
    have h : f ![1, latL0.hom (integralRadicalGenerator 1)] = _ := hz1
    rw [hom_gen_one, ← u01_eq] at h
    exact h
  -- the closedness of the dual cocycle
  have hcl : dualRep (dualityData n trivialCharacter) (latL0.u 1 0) (g ![1, latL0.u 0 1]) -
      g ![1, latL0.u 0 1] =
      dualRep (dualityData n trivialCharacter) (latL0.u 0 1) (g ![1, latL0.u 1 0]) -
        g ![1, latL0.u 1 0] := by
    have h1 := uCocycle_mul_gen hg ha (latL0.u 0 1)
    have h2 := uCocycle_mul_gen hg hb (latL0.u 1 0)
    rw [latL0.commute.eq] at h1
    exact sub_eq_sub_iff_add_eq_add.mpr (h1.symm.trans h2)
  -- the cup-product value
  have gA : g ![latL0.u 1 0, latL0.u 1 0 * latL0.u 0 1] =
      dualRep (dualityData n trivialCharacter) (latL0.u 1 0) (g ![1, latL0.u 0 1]) := by
    have h := hg.1 (latL0.u 1 0) ha 1 (latL0.u 0 1)
    rwa [mul_one] at h
  have gB : g ![latL0.u 0 1, latL0.u 0 1 * latL0.u 1 0] =
      dualRep (dualityData n trivialCharacter) (latL0.u 0 1) (g ![1, latL0.u 1 0]) := by
    have h := hg.1 (latL0.u 0 1) hb 1 (latL0.u 1 0)
    rwa [mul_one] at h
  have hκ : kostant (dualityData n trivialCharacter).B latL0.σ f g =
      dualPairing n (binaryHomogeneousEmbedding n p0) (g ![1, latL0.u 0 1]) -
        dualPairing n (binaryHomogeneousEmbedding n p1) (g ![1, latL0.u 1 0]) := by
    rw [kostant_lattice latL0, gA, gB]
    change dualPairing n (f ![1, latL0.u 1 0]) _ - dualPairing n (f ![1, latL0.u 0 1]) _ = _
    rw [hf0, hf1]
    exact bad_kappa_special n (latL0.u 1 0) (latL0.u 0 1) _ _ v _ _ (embed_fixed_a n p0)
      (embed_fixed_b n p1) hcl
  -- the bad-line Kostant value
  have hw := (oneCocycle_generator_closed (upperRadicalLatticeRep n) (wBad n hg)
    radicalLatticeFirst radicalLatticeSecond (Commute.all _ _)).symm
  rw [upperRep_first, upperRep_second] at hw
  have hbd : kostantValue (badDualForm n)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) v - v)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) v - v)
      (wv n (wBad n hg) radicalLatticeSecond) (wv n (wBad n hg) radicalLatticeFirst) = 0 :=
    kostantValue_boundary_left_end (badDualForm n)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0))
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1))
      (rationalCoefficientComponent n trivialCharacter (planeUnipotent 0 1))
      (rationalCoefficientComponent n trivialCharacter (planeUnipotent 1 0))
      (bad_adjoint_first n) (bad_adjoint_second n) v _ _ hw
  have hK : kostantValue (badDualForm n) ((zBad n hf).val (integralRadicalGenerator 0))
      ((zBad n hf).val (integralRadicalGenerator 1)) (wv n (wBad n hg) radicalLatticeSecond)
      (wv n (wBad n hg) radicalLatticeFirst) =
      -dualPairing n (binaryHomogeneousEmbedding n p0) (g ![1, latL0.u 0 1]) +
        dualPairing n (binaryHomogeneousEmbedding n p1) (g ![1, latL0.u 1 0]) := by
    have h2 := congrArg₂ (fun x y => kostantValue (badDualForm n) x y
      (wv n (wBad n hg) radicalLatticeSecond) (wv n (wBad n hg) radicalLatticeFirst)) hz0 hz1
    have h1 := kostantValue_add_left (badDualForm n) (binaryHomogeneousEmbedding n p0)
      (binaryHomogeneousEmbedding n p1)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) v - v)
      (rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) v - v)
      (wv n (wBad n hg) radicalLatticeSecond) (wv n (wBad n hg) radicalLatticeFirst)
    have h3 := congrArg (fun t => kostantValue (badDualForm n) (binaryHomogeneousEmbedding n p0)
      (binaryHomogeneousEmbedding n p1) (wv n (wBad n hg) radicalLatticeSecond)
      (wv n (wBad n hg) radicalLatticeFirst) + t) hbd
    refine h2.trans (h1.trans (h3.trans ((add_zero _).trans ?_)))
    unfold kostantValue
    rw [badW_first n hg (embed_fixed_b n p0), badW_second n hg (embed_fixed_a n p1)]
    ring
  rw [hκ, hK]
  ring

/-! ### The pairing in binary coordinates -/

theorem det_swapUnit : ((GeneralLinearGroup.det swapUnit : ℂˣ) : ℂ) = -1 := by
  rw [GeneralLinearGroup.val_det_apply]
  simp [swapUnit, swap01, Matrix.det_fin_two]

/-- **Skew-symmetry of the pairing under the exchange of the variables** in odd degree:
`⟨σ x, y⟩ = -⟨x, σ y⟩`. -/
theorem binaryPairing_swapVar (N : ℕ) (hodd : Odd N) (x y : Binary.HomogeneousPoly N) :
    BinaryPairing.binaryPairing N (binarySwapVar N x) y =
      -BinaryPairing.binaryPairing N x (binarySwapVar N y) := by
  have h := BinaryPairing.binaryPairing_homogeneousAction N 0 0 swapUnit x (binarySwapVar N y)
  have hz : ((GeneralLinearGroup.det swapUnit : ℂˣ) : ℂ) ^ ((0 : ℤ) + 0 - (N : ℤ)) = -1 := by
    rw [det_swapUnit]
    have h0 : (0 : ℤ) + 0 - (N : ℤ) = -(N : ℤ) := by ring
    have hodd' : Odd (N : ℤ) := (Int.odd_coe_nat N).mpr hodd
    rw [h0, _root_.zpow_neg, hodd'.neg_one_zpow]
    norm_num
  change BinaryPairing.binaryPairing N (binarySwapVar N x) (binarySwapVar N (binarySwapVar N y)) =
    _ at h
  rw [hz, binarySwapVar_involutive, neg_one_mul] at h
  exact h

/-- **The Kostant identity of the level-three bridge**:
`κ(f, g) = (n+1)!/3 · binaryPairing (n+1) (Φ f) (Ψ g)` for even `n`. -/
theorem kostantBad_eq_binaryPairing (n : ℕ) (positive : 0 < n) (heven : Even n)
    {f g : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hf : UCocycle (rationalCoefficientComponent n trivialCharacter) latL0.sub f)
    (hg : UCocycle (dualRep (dualityData n trivialCharacter)) latL0.sub g) :
    kostant (dualityData n trivialCharacter).B latL0.σ f g =
      (((n + 1).factorial : ℂ) / 3) *
        BinaryPairing.binaryPairing (n + 1) (PhiBad n positive f) (PsiBad n g) := by
  rw [kostantBad_eq_neg_K n positive hf hg, badLineKostantValue_eq n positive (zBad n hf) (wBad n hg),
    ← PhiBad_eq n positive hf, ← upperTotalBad_eq n hg, binApolar_eq_binaryPairing,
    binaryPairing_swapVar (n + 1) heven.add_one]
  simp only [PsiBad, LinearMap.comp_apply]
  ring

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
