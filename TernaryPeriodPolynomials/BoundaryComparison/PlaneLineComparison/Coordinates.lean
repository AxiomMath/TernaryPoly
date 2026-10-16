module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Main
public import TernaryPeriodPolynomials.Building.FreeResolution.Main
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.PositiveDegree
public import TernaryPeriodPolynomials.BoundaryComparison.ConstantTerms
public import TernaryPeriodPolynomials.BoundaryComparison.FaceRestriction.Cocycles

@[expose] public section



/-! The template is `Isotropy.lean`'s `boundaryExact_of_plane_zero` (generic over `D : InducingData n`,
used only via `D.chi`) and `HalfDimension.lean`'s `line_eq_zero_of_associateDuality` (which calls it
with `AssociateDuality`). Both are re-derived here directly for `trivialCharacter`, with
`face_pairing_perfect`/`constant_terms` replacing
`AssociateDuality`/plane-surjectivity. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.Classification

/-- Pullback of a plane one-cochain to complete flags, specialized to `trivialCharacter` (so no
`InducingData` is needed) -- copy of `Isotropy.planeEdgeCochain`. -/
def planeEdgeCochainTrivial (n : ℕ) (u : MaximalCochains n trivialCharacter .plane 1) :
    EdgeCochains n trivialCharacter 1 :=
  ⟨fun x e => u.val x (endpoint .plane e), by
    intro γ x
    funext e
    have equivariant := congrFun (u.property γ x) (endpoint .plane e)
    change u.val (fun i => γ.val * x i) (endpoint .plane e) = _
    rw [equivariant]
    change rationalCoefficientComponent n trivialCharacter γ.val
        (u.val x (γ.val⁻¹ • endpoint .plane e)) =
      rationalCoefficientComponent n trivialCharacter γ.val
        (u.val x (endpoint .plane (γ.val⁻¹ • e)))
    rw [endpoint_smul]⟩

/-- **Zero version of Proposition C.5.** A global class whose plane coordinate vanishes and whose
line coordinate is mixed cuspidal has vanishing line coordinate -- the direct analogue of
`line_eq_zero_of_associateDuality`, using `face_pairing_perfect` in place of `AssociateDuality` and
`constant_terms` in place of plane-surjectivity of the boundary summand. -/
theorem lineCoord_eq_zero_of_planeCoord_zero (n : ℕ) (hn : 4 ≤ n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (planeZero : (globalCoordinates n trivialCharacter c).1 = 0)
    (lineInner : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2) :
    (globalCoordinates n trivialCharacter c).2 = 0 := by
  by_contra hne
  obtain ⟨ξ, hξInner, detects⟩ :=
    TernaryPeriodPolynomials.Argument.FacePairing.face_pairing_perfect_pos n (by omega) _
      lineInner hne
  obtain ⟨c', hc'plane, _hc'lineInner⟩ := constant_terms n hn ξ hξInner
  obtain ⟨u, primitive⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp planeZero)
  have top : GlobalTopVanishing :=
    TernaryPeriodPolynomials.TopVanishing.globalTopVanishing_of_topVanishing
      TernaryPeriodPolynomials.FreeResolution.topVanishing_rationalLevel
  have hlevel : ∀ g ∈ rationalLevel, dualInvolution g ∈ rationalLevel :=
    fun _ membership => dualInvolution_mem_rationalLevel membership
  have hinvariant : ∀ g ∈ rationalLevel, ∀ v w : HomogeneousPoly n,
      dualPairing n (rationalCoefficientComponent n trivialCharacter g v)
        (rationalCoefficientComponent n trivialCharacter (dualInvolution g) w) =
        dualPairing n v w :=
    fun g _ v w => dualPairing_invariant n trivialCharacter g v w
  obtain ⟨θ, θmem, θprimitive⟩ :=
    top (cupTwoTwo (dualPairing n) dualInvolution c.val.val c'.val.val)
      (cupTwoTwo_mem_trivial dualInvolution hlevel (dualPairing n) hinvariant c c')
      (differentialFourRaw_cupTwoTwo (dualPairing n) dualInvolution
        (isCocycleTwo_of_mem c) (isCocycleTwo_of_mem c'))
  have constantMem (X : Type) [MulAction RationalGL3 X] :
      (fun x (_ : X) => θ x) ∈ cochains rationalLevel (functionRepresentation scalarTrivial X) 3 := by
    intro γ x; funext F; exact θmem γ x
  set κ : (Fin 4 → RationalGL3) → Flags .plane → ℂ := fun x P =>
    cupOneTwo (dualPairing n) dualInvolution (fun x => u.val x P) c'.val.val x - θ x with κ_def
  have κmem : κ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .plane)) 3 := by
    intro γ x
    funext P
    have dual : dualInvolution γ.val ∈ rationalLevel := hlevel γ.val γ.property
    have pair := congrFun (cochain_pair u γ (x 0) (x 1)) P
    change dualPairing n (u.val ![γ.val * x 0, γ.val * x 1] P)
        (c'.val.val ![dualInvolution (γ.val * x 1), dualInvolution (γ.val * x 2),
          dualInvolution (γ.val * x 3)]) - θ (fun i => γ.val * x i) =
      dualPairing n (u.val ![x 0, x 1] (γ.val⁻¹ • P))
        (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]) - θ x
    rw [pair, map_mul, map_mul, map_mul, cochain_triple c'.val ⟨dualInvolution γ.val, dual⟩,
      θmem γ x]
    change dualPairing n
        (rationalCoefficientComponent n trivialCharacter γ.val
          (u.val ![x 0, x 1] (γ.val⁻¹ • P)))
        (rationalCoefficientComponent n trivialCharacter (dualInvolution γ.val)
          (c'.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)])) -
        θ x = _
    rw [hinvariant γ.val γ.property]
  have κcocycle : ∀ x, differentialThreeRaw κ x = 0 := by
    intro x
    funext P
    have leibniz := differentialThreeRaw_cupOneTwo (dualPairing n) dualInvolution
      (fun x => u.val x P) (isCocycleTwo_of_mem c') x
    have restricted : ∀ x' : Fin 3 → RationalGL3,
        differentialOneRaw (fun x => u.val x P) x' = c.val.val x' := by
      intro x'
      exact congrFun (congrArg (fun z => z.val.val x') primitive) P
    have product : cupTwoTwo (dualPairing n) dualInvolution
        (differentialOneRaw (fun x => u.val x P)) c'.val.val x =
        cupTwoTwo (dualPairing n) dualInvolution c.val.val c'.val.val x := by
      unfold cupTwoTwo; rw [restricted]
    have split : differentialThreeRaw κ x P =
        differentialThreeRaw
            (cupOneTwo (dualPairing n) dualInvolution (fun x => u.val x P) c'.val.val) x -
          differentialThreeRaw θ x := by
      simp only [differentialThreeRaw, κ_def, Pi.sub_apply, Pi.add_apply]; abel
    rw [split, leibniz, product, θprimitive, sub_self]
    rfl
  refine detects (restrictionCocycle n trivialCharacter .line c) rfl
    (planeEdgeCochainTrivial n u) ?_
    (restrictionCocycle n trivialCharacter .plane c') hc'plane
    (fun x _ => θ x) (constantMem (Flags .line)) (fun x _ => θprimitive x) ?_
  · intro x e
    exact (congrFun (congrArg (fun z => z.val.val x) primitive) (endpoint .plane e)).symm
  · refine ⟨0, κ, fun _ _ => 0, κmem, ?_, κcocycle, ?_, ?_⟩
    · intro γ x; rfl
    · intro x; funext F; simp [differentialThreeRaw]
    · intro x e
      rw [map_zero]
      change _ = (0 : (Fin 4 → RationalGL3) → Edges → ℂ) x e + κ x (endpoint .plane e) - 0
      rw [Pi.zero_apply, Pi.zero_apply, zero_add, sub_zero]; rfl

/-- Mixed-cuspidal (inner-boundary) classes form a submodule -- the same closure argument as
`GeneralEisenstein.goodCuspSubmodule`, specialized to `InnerBoundary`'s edge-exactness witness. -/
noncomputable def innerBoundarySubmodule (n : ℕ) (side : Side) :
    Submodule ℂ (StratumH2 n trivialCharacter side) where
  carrier := {a | InnerBoundary n trivialCharacter side a}
  zero_mem' := by
    refine ⟨0, map_zero _, 0, ?_⟩
    intro x e
    simp
  add_mem' := by
    rintro a b ⟨z, hz, u, hu⟩ ⟨w, hw, v, hv⟩
    refine ⟨z + w, by rw [map_add, hz, hw], u + v, ?_⟩
    intro x e
    change z.val.val x (endpoint side e) + w.val.val x (endpoint side e) = _
    rw [hu x e, hv x e, map_add]
    rfl
  smul_mem' := by
    rintro r a ⟨z, hz, u, hu⟩
    refine ⟨r • z, by rw [map_smul, hz], r • u, ?_⟩
    intro x e
    change r • z.val.val x (endpoint side e) = _
    rw [hu x e, map_smul]
    rfl

@[simp] theorem mem_innerBoundarySubmodule (n : ℕ) (side : Side)
    (a : StratumH2 n trivialCharacter side) :
    a ∈ innerBoundarySubmodule n side ↔ InnerBoundary n trivialCharacter side a := Iff.rfl

theorem restrictionCocycle_sub (n : ℕ) (s : Side)
    (c₁ c₂ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    restrictionCocycle n trivialCharacter s (c₁ - c₂) =
      restrictionCocycle n trivialCharacter s c₁ - restrictionCocycle n trivialCharacter s c₂ :=
  rfl

theorem restrictionCocycle_smul (n : ℕ) (s : Side) (r : ℂ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    restrictionCocycle n trivialCharacter s (r • c) =
      r • restrictionCocycle n trivialCharacter s c :=
  rfl

theorem globalCoordinates_fst_sub (n : ℕ)
    (c₁ c₂ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    (globalCoordinates n trivialCharacter (c₁ - c₂)).1 =
      (globalCoordinates n trivialCharacter c₁).1 - (globalCoordinates n trivialCharacter c₂).1 := by
  simp only [globalCoordinates, restrictionCocycle_sub, map_sub]

theorem globalCoordinates_snd_sub (n : ℕ)
    (c₁ c₂ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    (globalCoordinates n trivialCharacter (c₁ - c₂)).2 =
      (globalCoordinates n trivialCharacter c₁).2 - (globalCoordinates n trivialCharacter c₂).2 := by
  simp only [globalCoordinates, restrictionCocycle_sub, map_sub]

theorem globalCoordinates_fst_smul (n : ℕ) (r : ℂ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    (globalCoordinates n trivialCharacter (r • c)).1 = r • (globalCoordinates n trivialCharacter c).1 := by
  simp only [globalCoordinates, restrictionCocycle_smul, map_smul]

theorem globalCoordinates_snd_smul (n : ℕ) (r : ℂ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    (globalCoordinates n trivialCharacter (r • c)).2 = r • (globalCoordinates n trivialCharacter c).2 := by
  simp only [globalCoordinates, restrictionCocycle_smul, map_smul]

/-- Difference form of the zero-version lemma: two realizing classes with equal plane
coordinates and mixed-cuspidal line coordinates have equal line coordinates. -/
theorem lineCoord_eq_of_planeCoord_eq (n : ℕ) (hn : 4 ≤ n)
    (c₁ c₂ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hplane : (globalCoordinates n trivialCharacter c₁).1 = (globalCoordinates n trivialCharacter c₂).1)
    (hline1 : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c₁).2)
    (hline2 : InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c₂).2) :
    (globalCoordinates n trivialCharacter c₁).2 = (globalCoordinates n trivialCharacter c₂).2 := by
  have planeZero : (globalCoordinates n trivialCharacter (c₁ - c₂)).1 = 0 := by
    rw [globalCoordinates_fst_sub, hplane, sub_self]
  have lineInner : InnerBoundary n trivialCharacter .line
      (globalCoordinates n trivialCharacter (c₁ - c₂)).2 := by
    rw [globalCoordinates_snd_sub]
    exact (innerBoundarySubmodule n .line).sub_mem hline1 hline2
  have key := lineCoord_eq_zero_of_planeCoord_zero n hn (c₁ - c₂) planeZero lineInner
  rw [globalCoordinates_snd_sub] at key
  exact sub_eq_zero.mp key

open scoped Classical in
/-- The line coordinate of a chosen class realizing a mixed-cuspidal plane class `ξ`, via
`constant_terms`. Total on all of `StratumH2 n trivialCharacter .plane` by junk value `0` off the
mixed-cuspidal locus; only its values on that locus are used. -/
noncomputable def T₀Fun (n : ℕ) (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane) :
    StratumH2 n trivialCharacter .line :=
  if h : InnerBoundary n trivialCharacter .plane ξ then
    (globalCoordinates n trivialCharacter (constant_terms n hn ξ h).choose).2
  else 0

theorem T₀Fun_spec (n : ℕ) (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane)
    (h : InnerBoundary n trivialCharacter .plane ξ) :
    InnerBoundary n trivialCharacter .line (T₀Fun n hn ξ) ∧
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T₀Fun n hn ξ) := by
  unfold T₀Fun
  rw [dite_eq_left h]
  obtain ⟨hplane, hlineInner⟩ := (constant_terms n hn ξ h).choose_spec
  exact ⟨hlineInner, (constant_terms n hn ξ h).choose, Prod.ext hplane rfl⟩

theorem T₀Fun_add (n : ℕ) (hn : 4 ≤ n) (a b : StratumH2 n trivialCharacter .plane)
    (ha : InnerBoundary n trivialCharacter .plane a) (hb : InnerBoundary n trivialCharacter .plane b) :
    T₀Fun n hn (a + b) = T₀Fun n hn a + T₀Fun n hn b := by
  have hab : InnerBoundary n trivialCharacter .plane (a + b) :=
    (innerBoundarySubmodule n .plane).add_mem ha hb
  obtain ⟨ca, hca⟩ := (T₀Fun_spec n hn a ha).2
  obtain ⟨cb, hcb⟩ := (T₀Fun_spec n hn b hb).2
  obtain ⟨cab, hcab⟩ := (T₀Fun_spec n hn (a + b) hab).2
  have hca1 : (globalCoordinates n trivialCharacter ca).1 = a := by rw [hca]
  have hca2 : (globalCoordinates n trivialCharacter ca).2 = T₀Fun n hn a := by rw [hca]
  have hcb1 : (globalCoordinates n trivialCharacter cb).1 = b := by rw [hcb]
  have hcb2 : (globalCoordinates n trivialCharacter cb).2 = T₀Fun n hn b := by rw [hcb]
  have hcab1 : (globalCoordinates n trivialCharacter cab).1 = a + b := by rw [hcab]
  have hcab2 : (globalCoordinates n trivialCharacter cab).2 = T₀Fun n hn (a + b) := by rw [hcab]
  have planeZero : (globalCoordinates n trivialCharacter (cab - ca - cb)).1 = 0 := by
    rw [globalCoordinates_fst_sub, globalCoordinates_fst_sub, hcab1, hca1, hcb1]
    abel
  have lineInner : InnerBoundary n trivialCharacter .line
      (globalCoordinates n trivialCharacter (cab - ca - cb)).2 := by
    rw [globalCoordinates_snd_sub, globalCoordinates_snd_sub]
    refine (innerBoundarySubmodule n .line).sub_mem
      ((innerBoundarySubmodule n .line).sub_mem ?_ ?_) ?_
    · rw [hcab2]; exact (T₀Fun_spec n hn (a + b) hab).1
    · rw [hca2]; exact (T₀Fun_spec n hn a ha).1
    · rw [hcb2]; exact (T₀Fun_spec n hn b hb).1
  have zero := lineCoord_eq_zero_of_planeCoord_zero n hn (cab - ca - cb) planeZero lineInner
  rw [globalCoordinates_snd_sub, globalCoordinates_snd_sub, hcab2, hca2, hcb2, sub_sub] at zero
  exact sub_eq_zero.mp zero

theorem T₀Fun_smul (n : ℕ) (hn : 4 ≤ n) (r : ℂ) (a : StratumH2 n trivialCharacter .plane)
    (ha : InnerBoundary n trivialCharacter .plane a) :
    T₀Fun n hn (r • a) = r • T₀Fun n hn a := by
  have hra : InnerBoundary n trivialCharacter .plane (r • a) :=
    (innerBoundarySubmodule n .plane).smul_mem r ha
  obtain ⟨ca, hca⟩ := (T₀Fun_spec n hn a ha).2
  obtain ⟨cra, hcra⟩ := (T₀Fun_spec n hn (r • a) hra).2
  have hca1 : (globalCoordinates n trivialCharacter ca).1 = a := by rw [hca]
  have hca2 : (globalCoordinates n trivialCharacter ca).2 = T₀Fun n hn a := by rw [hca]
  have hcra1 : (globalCoordinates n trivialCharacter cra).1 = r • a := by rw [hcra]
  have hcra2 : (globalCoordinates n trivialCharacter cra).2 = T₀Fun n hn (r • a) := by rw [hcra]
  have planeZero : (globalCoordinates n trivialCharacter (cra - r • ca)).1 = 0 := by
    rw [globalCoordinates_fst_sub, globalCoordinates_fst_smul, hcra1, hca1, sub_self]
  have lineInner : InnerBoundary n trivialCharacter .line
      (globalCoordinates n trivialCharacter (cra - r • ca)).2 := by
    rw [globalCoordinates_snd_sub, globalCoordinates_snd_smul]
    refine (innerBoundarySubmodule n .line).sub_mem ?_
      ((innerBoundarySubmodule n .line).smul_mem r ?_)
    · rw [hcra2]; exact (T₀Fun_spec n hn (r • a) hra).1
    · rw [hca2]; exact (T₀Fun_spec n hn a ha).1
  have zero := lineCoord_eq_zero_of_planeCoord_zero n hn (cra - r • ca) planeZero lineInner
  rw [globalCoordinates_snd_sub, globalCoordinates_snd_smul, hcra2, hca2] at zero
  exact sub_eq_zero.mp zero

/-- `T₀Fun`, bundled as a linear map on the mixed-cuspidal plane submodule. -/
noncomputable def T₁ (n : ℕ) (hn : 4 ≤ n) :
    innerBoundarySubmodule n .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line where
  toFun a := T₀Fun n hn a.1
  map_add' a b := T₀Fun_add n hn a.1 b.1 a.2 b.2
  map_smul' r a := T₀Fun_smul n hn r a.1 a.2

/-- The target's `T`: `T₁` extended from the mixed-cuspidal plane submodule to the whole plane
stratum, via `LinearMap.exists_extend`. -/
noncomputable def T (n : ℕ) (hn : 4 ≤ n) :
    StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line :=
  (LinearMap.exists_extend (T₁ n hn)).choose

theorem T_eq_T₀Fun (n : ℕ) (hn : 4 ≤ n) (a : StratumH2 n trivialCharacter .plane)
    (ha : InnerBoundary n trivialCharacter .plane a) :
    T n hn a = T₀Fun n hn a := by
  have spec := (LinearMap.exists_extend (T₁ n hn)).choose_spec
  have := DFunLike.congr_fun spec (⟨a, ha⟩ : innerBoundarySubmodule n .plane)
  exact this

theorem prop_C_5_proof (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        InnerBoundary n trivialCharacter .line (T ξ) ∧
          ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
            globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
        InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  refine ⟨T n hn, ?_, ?_⟩
  · intro ξ hξ
    rw [T_eq_T₀Fun n hn ξ hξ]
    exact T₀Fun_spec n hn ξ hξ
  · intro c hplaneInner hlineInner
    obtain ⟨hTInner, c', hc'eq⟩ :=
      T₀Fun_spec n hn (globalCoordinates n trivialCharacter c).1 hplaneInner
    have hplane : (globalCoordinates n trivialCharacter c).1 =
        (globalCoordinates n trivialCharacter c').1 := by rw [hc'eq]
    have hline2 : InnerBoundary n trivialCharacter .line
        (globalCoordinates n trivialCharacter c').2 := by rw [hc'eq]; exact hTInner
    have step := lineCoord_eq_of_planeCoord_eq n hn c c' hplane hlineInner hline2
    rw [step, hc'eq]
    exact (T_eq_T₀Fun n hn _ hplaneInner).symm

end TernaryPeriodPolynomials.Argument.Classification
