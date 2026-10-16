module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.EngineLemmas
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.GridCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.TorusPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.TwistFamily
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FrameTranslation

@[expose] public section


/-!
# The abstract engine: a covariant periodic family with zero average has a trivial class

Let `F` be a radical frame inside a flag stabilizer `Γ` (a finite-index lattice `F.lattice N₀ ≤ Γ`),
and let `Θ r` (`r ∈ ℝ²`) be homogeneous 2-cocycles with values in `HomogeneousPoly n` that are

* `ℤ²`-periodic in `r`;
* shifted by radical points: `Θ r (u(w) y) = ρ(u(w)) Θ (r + w) y`;
* covariant under the Levi elements of the frame, `Θ r (m y) = ρ(m) Θ (A_m⁻¹ r) y`, and under all of
  `Γ` through some integral matrix;
* continuous in `r` with zero average over the unit square, and `Γ`-equivariant at `r = 0`.

Then `Θ 0` is a `Γ`-equivariant coboundary. Each grid point of the `K`-grid is cohomologous to
`Θ 0` on the finite-index lattice `F.lattice (N₀ K)` (by `translation_class_eq`), the grid average
is `Γ`-equivariant (`gridAverage_equivariant_of_covariant`), corestriction transports the
primitive from the lattice to `Γ`, and `isCoboundary_of_torus_average` finishes.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.FlagExactness

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

theorem reduction_eq_one_of_dvd {N K : ℕ} (h : K ∣ N) {A : GLTwo ℤ}
    (hA : reduction N A = 1) : reduction K A = 1 := by
  have key : (Matrix.GeneralLinearGroup.map (ZMod.castHom h (ZMod K))) ((reduction N) A) =
      (reduction K) A := by
    apply Units.ext
    ext i j
    simp [reduction, Matrix.GeneralLinearGroup.map]
  rw [← key, hA, map_one]

/-- One grid point is cohomologous to the origin on the level lattice. -/
theorem grid_point_primitive {n : ℕ} (χ : RankOneCharacter) (F : RadicalFrame) (q : RationalGL3)
    (hunip : ∀ r : ℚ × ℚ, F.point r ∈ conjUnitri q) (N K : ℕ) (hK : 0 < K) (hKN : K ∣ N)
    (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → HomogeneousPoly n)
    (hcoc : ∀ r, IsCocycle₂ (Θ r))
    (hshift : ∀ (w : ℚ × ℚ) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      Θ r (fun i => F.point w * y i) =
        rationalCoefficientComponent n χ (F.point w) (Θ (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y))
    (hperiodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ) (y : Fin 3 → RationalGL3),
      Θ (r.1 + (ℓ.1 : ℝ), r.2 + (ℓ.2 : ℝ)) y = Θ r y)
    (hcovF : ∀ m ∈ F.leviLevel N, ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      Θ r (fun i => F.leviHom m * y i) =
        rationalCoefficientComponent n χ (F.leviHom m)
          (Θ (realAct (F.leviMatrix m)⁻¹ r) y))
    (a b : ℕ) :
    ∃ P : cochains (F.latticeHom N).range (rationalCoefficientComponent n χ) 1,
      ∀ x, (differentialOne (F.latticeHom N).range (rationalCoefficientComponent n χ) P).val x =
        Θ ((a : ℝ) / K, (b : ℝ) / K) x - Θ 0 x := by
  set ρ := rationalCoefficientComponent n χ
  set v : ℚ × ℚ := ((a : ℚ) / K, (b : ℚ) / K) with hvdef
  have hv : ∀ m : F.leviLevel N, ∃ δ : ℤ × ℤ,
      ((δ.1 : ℚ), (δ.2 : ℚ)) = v - leviAct (F.leviMatrix (m : F.Levi)) v := by
    intro m
    have hm : reduction K (F.leviMatrix (m : F.Levi)) = 1 :=
      reduction_eq_one_of_dvd (A := F.leviMatrix (m : F.Levi)) hKN m.property
    have := exists_int_sub_leviAct (F.leviMatrix (m : F.Levi)) K hK hm (a : ℤ) (b : ℤ)
    simpa [hvdef] using this
  have hvR1 : ((v.1 : ℚ) : ℝ) = (a : ℝ) / K := by simp [hvdef]
  have hvR2 : ((v.2 : ℚ) : ℝ) = (b : ℝ) / K := by simp [hvdef]
  let C : ℤ → (Fin 3 → RationalGL3) → HomogeneousPoly n := fun k =>
    Θ ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K))
  have hC1 : ∀ x, C 1 x = Θ ((a : ℝ) / K, (b : ℝ) / K) x := by
    intro x
    simp [C]
  have hC0 : ∀ x, C 0 x = Θ 0 x := by
    intro x
    simp [C, Prod.mk_zero_zero]
  have shift : ∀ (k : ℤ) (x : Fin 3 → RationalGL3),
      C k (fun i => F.point v * x i) = ρ (F.point v) (C (k + 1) x) := by
    intro k x
    have h := hshift v ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) x
    have e1 : ((k + 1 : ℤ) : ℝ) * ((a : ℝ) / K) = (k : ℝ) * ((a : ℝ) / K) + ((v.1 : ℚ) : ℝ) := by
      rw [hvR1]; push_cast; ring
    have e2 : ((k + 1 : ℤ) : ℝ) * ((b : ℝ) / K) = (k : ℝ) * ((b : ℝ) / K) + ((v.2 : ℚ) : ℝ) := by
      rw [hvR2]; push_cast; ring
    show Θ _ (fun i => F.point v * x i) = ρ (F.point v) (Θ (((k + 1 : ℤ) : ℝ) * ((a : ℝ) / K),
      ((k + 1 : ℤ) : ℝ) * ((b : ℝ) / K)) x)
    rw [h, e1, e2]
  have equivRad : ∀ (ℓ : ℤ × ℤ) (k : ℤ) (x : Fin 3 → RationalGL3),
      C k (fun i => F.integral ℓ * x i) = ρ (F.integral ℓ) (C k x) := by
    intro ℓ k x
    have h := hshift ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) x
    have hper := hperiodic ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) ℓ x
    show Θ _ (fun i => F.point ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) * x i) =
      ρ (F.point ((ℓ.1 : ℚ), (ℓ.2 : ℚ)))
        (Θ ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) x)
    rw [h]
    exact congrArg (ρ (F.point ((ℓ.1 : ℚ), (ℓ.2 : ℚ)))) (by simpa using hper)
  have equivLevi : ∀ (m : F.leviLevel N) (k : ℤ) (x : Fin 3 → RationalGL3),
      C k (fun i => F.leviHom (m : F.Levi) * x i) = ρ (F.leviHom (m : F.Levi)) (C k x) := by
    intro m k x
    have h := hcovF (m : F.Levi) m.property
      ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) x
    have hr : ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) =
        ((((k * (a : ℤ) : ℤ)) : ℝ) / K, (((k * (b : ℤ) : ℤ)) : ℝ) / K) := by
      ext <;> simp [mul_div_assoc]
    have hinv : reduction K (F.leviMatrix (m : F.Levi))⁻¹ = 1 := by
      rw [map_inv, reduction_eq_one_of_dvd (A := F.leviMatrix (m : F.Levi)) hKN m.property,
        inv_one]
    obtain ⟨δ, hδ⟩ := realAct_div_sub (F.leviMatrix (m : F.Levi))⁻¹ K hK hinv (k * (a : ℤ))
      (k * (b : ℤ))
    show Θ _ (fun i => F.leviHom (m : F.Levi) * x i) = ρ (F.leviHom (m : F.Levi))
      (Θ ((k : ℝ) * ((a : ℝ) / K), (k : ℝ) * ((b : ℝ) / K)) x)
    rw [h, hr, hδ]
    exact congrArg (ρ (F.leviHom (m : F.Levi)))
      (hperiodic ((((k * (a : ℤ) : ℤ)) : ℝ) / K, (((k * (b : ℤ) : ℤ)) : ℝ) / K) δ x)
  have equiv : ∀ (k : ℤ) (g : SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N))
      (x : Fin 3 → RationalGL3), C k (fun i => F.latticeHom N g * x i) =
        ρ (F.latticeHom N g) (C k x) := by
    intro k g x
    rw [F.latticeHom_apply N g]
    have hfun : (fun i => (F.integral (Multiplicative.toAdd g.left) *
        F.leviHom (g.right : F.Levi)) * x i) =
        fun i => F.integral (Multiplicative.toAdd g.left) * (F.leviHom (g.right : F.Levi) * x i) := by
      funext i
      rw [mul_assoc]
    rw [hfun, equivRad, equivLevi, map_mul, Module.End.mul_apply]
  have period : ∀ x, C K x = C 0 x := by
    intro x
    have h : Θ ((0 : ℝ) + ((a : ℤ) : ℝ), (0 : ℝ) + ((b : ℤ) : ℝ)) x = Θ 0 x :=
      hperiodic (0, 0) ((a : ℤ), (b : ℤ)) x
    have e : ((((K : ℕ) : ℤ) : ℝ) * ((a : ℝ) / K), (((K : ℕ) : ℤ) : ℝ) * ((b : ℝ) / K)) =
        ((0 : ℝ) + ((a : ℤ) : ℝ), (0 : ℝ) + ((b : ℤ) : ℝ)) := by
      have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      ext <;> simp <;> field_simp
    show Θ ((((K : ℕ) : ℤ) : ℝ) * ((a : ℝ) / K), (((K : ℕ) : ℤ) : ℝ) * ((b : ℝ) / K)) x = C 0 x
    rw [e, h, hC0]
  have hℓ₀ : F.latticeHom N (SemidirectProduct.inl (Multiplicative.ofAdd ((a : ℤ), (b : ℤ)))) =
      (F.point v) ^ K := by
    rw [F.latticeHom_inl, F.integral_eq_point, ← F.point_pow]
    congr 1
    have hK' : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
    ext <;> simp [hvdef] <;> field_simp
  have hcomm : ∀ ℓ : Lat, F.latticeHom N (SemidirectProduct.inl ℓ) * F.point v =
      F.point v * F.latticeHom N (SemidirectProduct.inl ℓ) := by
    intro ℓ
    rw [F.latticeHom_inl, F.integral_eq_point]
    exact F.point_comm _ _
  obtain ⟨τ, hτ⟩ := translation_class_eq (F.latticeAction N) ρ (F.latticeHom N) (F.point v)
    (F.shiftHom N v hv) (F.latticeHom_shiftHom N v hv)
    (fun ℓ => twistHom_inl (F.latticeAction N) (F.shiftCocycle N v hv)
      (F.shiftCocycle_mul N v hv) ℓ)
    (fun g => twistHom_right (F.latticeAction N) (F.shiftCocycle N v hv)
      (F.shiftCocycle_mul N v hv) g)
    (Multiplicative.ofAdd ((a : ℤ), (b : ℤ))) K hK hℓ₀ hcomm
    ⟨2 * n + 1, RadicalFrame.nilpotent_of_conjUnitri χ (hunip v)⟩ C
    (fun k x => hcoc _ x) shift equiv period
  -- the cochain Θ v - Θ 0 on the lattice
  have hKc : ∀ (γ : (F.latticeHom N).range) (x : Fin 3 → RationalGL3),
      (fun y => Θ ((a : ℝ) / K, (b : ℝ) / K) y - Θ 0 y) (fun i => γ.val * x i) =
        ρ γ.val ((fun y => Θ ((a : ℝ) / K, (b : ℝ) / K) y - Θ 0 y) x) := by
    rintro ⟨_, g, rfl⟩ x
    have h1 := equiv 1 g x
    have h0 := equiv 0 g x
    simp only [hC1, hC0] at h1 h0
    simp only [map_sub, h1, h0]
  let Kc : cochains (F.latticeHom N).range ρ 2 :=
    ⟨fun y => Θ ((a : ℝ) / K, (b : ℝ) / K) y - Θ 0 y, hKc⟩
  have hcocycle : ∀ x : Fin 4 → RationalGL3,
      Kc.val ![x 1, x 2, x 3] - Kc.val ![x 0, x 2, x 3] + Kc.val ![x 0, x 1, x 3] -
        Kc.val ![x 0, x 1, x 2] = 0 := by
    intro x
    have h1 := hcoc ((a : ℝ) / K, (b : ℝ) / K) x
    have h0 := hcoc 0 x
    show (Θ _ _ - Θ 0 _) - (Θ _ _ - Θ 0 _) + (Θ _ _ - Θ 0 _) - (Θ _ _ - Θ 0 _) = 0
    linear_combination (norm := abel) h1 - h0
  have hτ' : ∀ g g' : SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N),
      Kc.val ![1, F.latticeHom N g, F.latticeHom N g * F.latticeHom N g'] =
        ρ (F.latticeHom N g) (τ g') - τ (g * g') + τ g := by
    intro g g'
    have := hτ g g'
    rw [hC1, hC0] at this
    exact this
  exact exists_primitive_range (F.latticeHom N) (F.latticeHom_injective N) ρ Kc hcocycle τ hτ'

/-- **The engine.** A periodic, shift- and Levi-covariant family of cocycles with continuous
functionals of zero torus average has a `Γ`-equivariant coboundary at the origin. -/
theorem engine_isCoboundary {n : ℕ} (χ : RankOneCharacter) (F : RadicalFrame) (q : RationalGL3)
    (hunip : ∀ r : ℚ × ℚ, F.point r ∈ conjUnitri q)
    (Γ : Subgroup RationalGL3) (N0 : ℕ)
    (hΓ : ∀ K : ℕ, 0 < K → F.lattice (N0 * K) ≤ Γ)
    (hfin : ∀ K : ℕ, 0 < K → (F.lattice (N0 * K)).relIndex Γ ≠ 0)
    (Θ : ℝ × ℝ → (Fin 3 → RationalGL3) → HomogeneousPoly n)
    (hcoc : ∀ r, IsCocycle₂ (Θ r))
    (hcont : ∀ (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ),
      Continuous fun r => μ (Θ r y))
    (hzero : ∀ (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ),
      ∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, μ (Θ r y) = 0)
    (hΘ0 : Equivariant Γ (rationalCoefficientComponent n χ) (Θ 0))
    (hshift : ∀ (w : ℚ × ℚ) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      Θ r (fun i => F.point w * y i) =
        rationalCoefficientComponent n χ (F.point w) (Θ (r.1 + (w.1 : ℝ), r.2 + (w.2 : ℝ)) y))
    (hperiodic : ∀ (r : ℝ × ℝ) (ℓ : ℤ × ℤ) (y : Fin 3 → RationalGL3),
      Θ (r.1 + (ℓ.1 : ℝ), r.2 + (ℓ.2 : ℝ)) y = Θ r y)
    (hcovF : ∀ m : F.Levi, F.leviHom m ∈ Γ → ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      Θ r (fun i => F.leviHom m * y i) =
        rationalCoefficientComponent n χ (F.leviHom m) (Θ (realAct (F.leviMatrix m)⁻¹ r) y))
    (hcov : ∀ γ ∈ Γ, ∃ A : GLTwo ℤ, ∀ (r : ℝ × ℝ) (y : Fin 3 → RationalGL3),
      Θ r (fun i => γ * y i) = rationalCoefficientComponent n χ γ (Θ (realAct A r) y))
    (riemann : ∀ φ : ℝ × ℝ → ℂ, Continuous φ → Filter.Tendsto
      (fun K : ℕ => (1 / (K : ℂ) ^ 2) • ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        φ ((a : ℝ) / K, (b : ℝ) / K)) Filter.atTop
        (nhds (∫ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, φ p))) :
    IsCoboundary Γ (rationalCoefficientComponent n χ) (Θ 0) := by
  have : FiniteDimensional ℂ (HomogeneousPoly n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)
  refine isCoboundary_of_torus_average_of_functional_continuous Γ
    (rationalCoefficientComponent n χ) Θ hcoc hcont hzero hΘ0 ?_ riemann
  intro K hK
  set ρ := rationalCoefficientComponent n χ
  set N := N0 * K
  have hpoint : ∀ a b : ℕ, ∃ P : cochains (F.latticeHom N).range ρ 1,
      ∀ x, (differentialOne (F.latticeHom N).range ρ P).val x =
        Θ ((a : ℝ) / K, (b : ℝ) / K) x - Θ 0 x :=
    fun a b => grid_point_primitive χ F q hunip N K hK (dvd_mul_left K N0) Θ hcoc hshift
      hperiodic (fun m hm r y => hcovF m (hΓ K hK (F.levi_mem N m hm)) r y) a b
  choose P hP using hpoint
  have hΛeq : ∀ a b, Equivariant (F.latticeHom N).range ρ (fun x => (P a b).val x) :=
    fun a b γ hγ x => (P a b).property ⟨γ, hγ⟩ x
  have hGeq : Equivariant (F.latticeHom N).range ρ (gridPrimitive (fun a b => (P a b).val) K) :=
    gridPrimitive_equivariant _ ρ _ K hΛeq
  have hcodiff : gridAverage Θ K - Θ 0 = codiff (gridPrimitive (fun a b => (P a b).val) K) := by
    apply gridAverage_sub_eq_codiff Θ (fun a b => (P a b).val) hK.ne'
    intro a _ b _
    funext x
    exact (hP a b x).symm
  have hGAeq : Equivariant Γ ρ (gridAverage Θ K) :=
    gridAverage_equivariant_of_covariant Γ ρ Θ hperiodic hcov K hK
  have hKΓ : Equivariant Γ ρ (gridAverage Θ K - Θ 0) := by
    intro γ hγ x
    have h1 := hGAeq γ hγ x
    have h0 := hΘ0 γ hγ x
    simp only [Pi.sub_apply, map_sub, h1, h0]
  let Kc2 : cochains Γ ρ 2 := ⟨gridAverage Θ K - Θ 0, fun γ x => hKΓ γ.val γ.property x⟩
  let P' : cochains (F.latticeHom N).range ρ 1 :=
    ⟨gridPrimitive (fun a b => (P a b).val) K, fun γ x => hGeq γ.val γ.property x⟩
  have : Finite (Quotient (QuotientGroup.rightRel ((F.latticeHom N).range.subgroupOf Γ))) := by
    rw [F.latticeHom_range N]
    exact finite_rightRel_of_relIndex_ne_zero _ _ (hfin K hK)
  obtain ⟨Pg, hPg⟩ := exists_primitive_of_finiteIndex Γ (F.latticeHom N).range ρ Kc2 P'
    (fun x => (congrFun hcodiff x).symm)
  exact ⟨Pg.val, fun γ hγ x => Pg.property ⟨γ, hγ⟩ x, funext fun x => (hPg x).symm⟩

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
