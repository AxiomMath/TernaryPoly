module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESSpan
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.OneES

@[expose] public section


/-!
# Eichler--Shimura spanning at level one (Lemma C.3, spanning clause, `Λ = SL₂(ℤ)`)

Paper: Lemma C.3
(`ar:lem:seed`) and the mixed cuspidal group `𝒞_P`.

`esSpan_top n : ESSpan ⊤ n` discharges the proposition `ESSpan` unconditionally for the full
modular group: every parabolic class of `H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is a combination of the
holomorphic and antiholomorphic period classes of cusp forms of weight `n + 3` for `SL₂(ℤ)`.
The proof restricts the cocycles from `SL₂(ℤ)` to the subgroup `⊤` (`topPull`, `topPush`),
applies the library's level-one Eichler--Shimura dimension count (`es_levelOne_modular`) for
odd `n`, where it is stated for the classical period cocycle `c_f` and its reflection `R c_f`, and
identifies these with D's Eichler cocycle of `f` and the conjugate cocycle of `f^*`
(`topPull_classical`, `topPull_reflection`); for even `n` the group vanishes
(`modularH1_eq_zero_of_odd`).

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup ComplexConjugate OnePoint
open GeneralEisenstein MvPolynomial CategoryTheory Matrix
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

section Prim

variable {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] {n : ℕ} (f : CuspForm Λ ((n + 3 : ℕ) : ℤ))

/-- The `i`-normalized moment primitives of a cusp form for any group are unique. -/
theorem momentPrim_unique_gen (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (UpperHalfPlane.ofComplex z) * z ^ j) z)
    (j : ℕ) {w : ℂ} (hw : 0 < w.im) : G j w = momentPrim Λ n f j w := by
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have heq : Set.EqOn (G j) (momentPrim Λ n f j) {u : ℂ | 0 < u.im} := by
    refine hopen.eqOn_of_deriv_eq hconn
      (fun u hu => (hG j u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (momentPrim_hasDerivAt Λ n f j u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => ?_) (show (0 : ℝ) < Complex.I.im by simp) ?_
    · rw [(hG j u hu).deriv, (momentPrim_hasDerivAt Λ n f j u hu).deriv]
      rfl
    · rw [hG0 j, momentPrim_zero]
  exact heq hw

/-- The Eichler cocycle does not depend on the choice of normalized moment primitives. -/
theorem eichlerCocycle_eq_momentPrim_gen (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (UpperHalfPlane.ofComplex z) * z ^ j) z)
    (m : SpecialLinearGroup (Fin 2) ℤ) :
    eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ m) =
      eichlerCocycle n (momentPrim Λ n f) (SpecialLinearGroup.mapGL ℝ m) := by
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ m : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob : mob (SpecialLinearGroup.mapGL ℝ m) Complex.I =
      ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ m) hpos UpperHalfPlane.I
    simpa using this
  have him : 0 < (mob (SpecialLinearGroup.mapGL ℝ m) Complex.I).im := by
    rw [hmob]; exact UpperHalfPlane.im_pos _
  unfold eichlerCocycle eichlerPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [momentPrim_unique_gen f G hG0 hG j him]

end Prim

section Top

open groupCohomology

variable (n : ℕ)

/-- The identity isomorphism `SL₂(ℤ) → ⊤` as a monoid homomorphism. -/
def topInv : SL(2, ℤ) →* (⊤ : Subgroup SL(2, ℤ)) where
  toFun m := ⟨m, Subgroup.mem_top m⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restriction of cocycles from `SL₂(ℤ)` to the subgroup `⊤`. -/
def topPull : cocycles₁ (modularBinaryRep (n + 1) (-1)) →ₗ[ℂ] cocycles₁ (binRep ⊤ n) :=
  oneCocyclePullback (modularBinaryRep (n + 1) (-1)) (binRep ⊤ n) (⊤ : Subgroup SL(2, ℤ)).subtype
    LinearMap.id (fun _ => rfl)

/-- The inverse of `topPull`. -/
def topPush : cocycles₁ (binRep ⊤ n) →ₗ[ℂ] cocycles₁ (modularBinaryRep (n + 1) (-1)) :=
  oneCocyclePullback (binRep ⊤ n) (modularBinaryRep (n + 1) (-1)) (topInv) LinearMap.id
    (fun _ => rfl)

/-- Restriction on `H¹` from `SL₂(ℤ)` to the subgroup `⊤`. -/
def topPullH1 : H1 (modularBinaryRep (n + 1) (-1)) →ₗ[ℂ] H1 (binRep ⊤ n) :=
  oneCocyclePullbackH1 (modularBinaryRep (n + 1) (-1)) (binRep ⊤ n)
    (⊤ : Subgroup SL(2, ℤ)).subtype LinearMap.id (fun _ => rfl)

theorem topPull_apply (c : cocycles₁ (modularBinaryRep (n + 1) (-1)))
    (g : (⊤ : Subgroup SL(2, ℤ))) : topPull n c g = c g.1 := rfl

theorem topPull_topPush (c : cocycles₁ (binRep ⊤ n)) : topPull n (topPush n c) = c := by
  apply cocycles₁_ext
  intro g
  rfl

theorem topPullH1_π (c : cocycles₁ (modularBinaryRep (n + 1) (-1))) :
    topPullH1 n (H1π (modularBinaryRep (n + 1) (-1)) c) = H1π (binRep ⊤ n) (topPull n c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

/-- The level-one cusp form as a cusp form for the image of `⊤`. -/
def liftTop (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
    ((n + 3 : ℕ) : ℤ)) : CuspForm (LamGL (⊤ : Subgroup SL(2, ℤ))) ((n + 3 : ℕ) : ℤ) :=
  CuspForm.mcast rfl f (MonoidHom.range_eq_map _).symm

variable {n}

theorem liftTop_apply (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
    ((n + 3 : ℕ) : ℤ)) (z : ℍ) : liftTop n f z = f z := rfl

end Top

section Compare

open groupCohomology

variable {n : ℕ} (f : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
  ((n + 3 : ℕ) : ℤ))

/-- The library's holomorphic period cocycle on `⊤` is the Eichler cocycle of the lifted form. -/
theorem topPull_classical (hev : Even (n + 1)) (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    topPull n (classicalBinaryCocycle f (n + 1) hw (-1)) = holCocycle (liftTop n f) := by
  apply cocycles₁_ext
  intro g
  apply Subtype.ext
  have h := classicalBinaryCocycle_eq_eichlerCocycle f n hw (-1) (momentPrim Lvl1 n f)
    (momentPrim_zero Lvl1 n f) (momentPrim_hasDerivAt Lvl1 n f) g.1
  have h2 := eichlerCocycle_eq_momentPrim_gen (liftTop n f) (momentPrim Lvl1 n f)
    (momentPrim_zero Lvl1 n f) (momentPrim_hasDerivAt Lvl1 n f) g.1
  change (show Binary.HomogeneousPoly (n + 1) from
      classicalBinaryCocycle f (n + 1) hw (-1) g.1).val =
    eichlerCocycle n (momentPrim (LamGL (⊤ : Subgroup SL(2, ℤ))) n (liftTop n f))
      (SpecialLinearGroup.mapGL ℝ g.1)
  rw [h, hev.neg_one_pow, map_one, one_mul, h2]

/-- The reflection of the library's period cocycle on `⊤` is minus the antiholomorphic period
cocycle of `f^*`. -/
theorem topPull_reflection (hev : Even (n + 1))
    (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    topPull n (modularCocycleReflection (n + 1) (-1) (classicalBinaryCocycle f (n + 1) hw (-1))) =
      -antiholCocycle (liftTop n (fStar f)) := by
  apply cocycles₁_ext
  intro g
  apply Subtype.ext
  have h := modularCocycleReflection_classical f n hw (-1) (momentPrim Lvl1 n f)
    (momentPrim Lvl1 n (fStar f)) (momentPrim_zero Lvl1 n f) (momentPrim_zero Lvl1 n (fStar f))
    (momentPrim_hasDerivAt Lvl1 n f) (fun j z hz => momentPrim_fStar_hasDerivAt f j z hz) g.1
  have h2 := eichlerCocycle_eq_momentPrim_gen (liftTop n (fStar f))
    (momentPrim Lvl1 n (fStar f)) (momentPrim_zero Lvl1 n (fStar f))
    (momentPrim_hasDerivAt Lvl1 n (fStar f)) g.1
  change (show Binary.HomogeneousPoly (n + 1) from
      modularCocycleReflection (n + 1) (-1) (classicalBinaryCocycle f (n + 1) hw (-1)) g.1).val =
    -MvPolynomial.map (starRingEnd ℂ)
      (eichlerCocycle n (momentPrim (LamGL (⊤ : Subgroup SL(2, ℤ))) n (liftTop n (fStar f)))
        (SpecialLinearGroup.mapGL ℝ g.1))
  rw [h, hev.neg_one_pow, map_one, one_mul, h2]

end Compare

section Main

open groupCohomology

/-- **Eichler--Shimura spanning at level one, unconditionally**: every parabolic class of
`H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is a combination of holomorphic and antiholomorphic period classes
of cusp forms of weight `n + 3` for `SL₂(ℤ)`. -/
theorem esSpan_top (n : ℕ) : ESSpan (⊤ : Subgroup SL(2, ℤ)) n := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hx
  have hxc : H1π (binRep ⊤ n) c =
      topPullH1 n (H1π (modularBinaryRep (n + 1) (-1)) (topPush n c)) := by
    rw [topPullH1_π, topPull_topPush]
  change H1π (binRep ⊤ n) c ∈ _
  rw [hxc]
  rcases Nat.even_or_odd (n + 1) with hev | hodd
  · have hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
    have hz : ∃ u : modularBinaryRep (n + 1) (-1), topPush n c ModularGroup.T =
        (modularBinaryRep (n + 1) (-1)).ρ ModularGroup.T u - u := by
      obtain ⟨u, hu⟩ := hc ⟨ModularGroup.T, Subgroup.mem_top _⟩
        ⟨1, 1, Or.inl (by simp)⟩
      exact ⟨u, hu⟩
    have hmem := es_levelOne_modular (n + 1) hev (Nat.succ_pos n) ((n + 3 : ℕ) : ℤ) hw
      (topPush n c) hz
    have key := Submodule.mem_map_of_mem (f := topPullH1 n) hmem
    rw [Submodule.map_span] at key
    refine Submodule.span_le.mpr ?_ key
    rintro _ ⟨_, (⟨f, rfl⟩ | ⟨f, rfl⟩), rfl⟩
    · rw [topPullH1_π, topPull_classical f hev hw]
      exact Submodule.subset_span (Or.inl ⟨liftTop n f, rfl⟩)
    · rw [topPullH1_π, topPull_reflection f hev hw, map_neg]
      exact Submodule.neg_mem _ (Submodule.subset_span (Or.inr ⟨liftTop n (fStar f), rfl⟩))
  · rw [modularH1_eq_zero_of_odd (n + 1) hodd (-1) (H1π (modularBinaryRep (n + 1) (-1))
      (topPush n c)), map_zero]
    exact Submodule.zero_mem _

end Main

end TernaryPeriodPolynomials.Argument.SeedC3S4c
