module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Automorphic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-!
# Smooth vectors of unitary representations of `GL₂(𝔸)`

For a unitary representation `π` of `GL₂(𝔸)` on a complex inner product space, the vectors
`v` whose archimedean orbit map is analytic and which are fixed by an open compact subgroup of
`GL₂(𝔸_f)` form a `π`-stable subspace `smoothSubmodule π`. A closed invariant subspace carries
the restricted representation, whose smooth vectors are the smooth vectors of `π` lying in it.
Finally `ofModel` assembles a `CuspidalRepresentation` whose smooth subspace is
`smoothSubmodule π`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.Automorphic.SmoothVectors

/-! ### Components of adelic matrices -/

/-- The archimedean component `GL₂(𝔸) → GL₂(ℝ)`. -/
def realPart : BinaryAdelicGL →* BinaryRealGL :=
  GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)

/-- The finite component `GL₂(𝔸) → GL₂(𝔸_f)`. -/
def finitePart : BinaryAdelicGL →* BinaryFiniteGL :=
  GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)

/-- `combineGL` is multiplicative in both components. -/
theorem combineGL_mul (r r' : BinaryRealGL) (f f' : BinaryFiniteGL) :
    combineGL r f * combineGL r' f' = combineGL (r * r') (f * f') := by
  apply Units.ext
  ext i j <;> simp [combineGL, pairMatrix, Matrix.mul_apply]

/-- `combineGL` sends the identity pair to the identity. -/
theorem combineGL_one : combineGL (1 : BinaryRealGL) (1 : BinaryFiniteGL) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change (pairMatrix (1 : BinaryRealGL).val (1 : BinaryFiniteGL).val i j).1 =
      ((1 : Matrix (Fin 2) (Fin 2) Adeles) i j).1
    by_cases h : i = j <;> simp [pairMatrix, Matrix.one_apply, h]
  · change (pairMatrix (1 : BinaryRealGL).val (1 : BinaryFiniteGL).val i j).2 =
      ((1 : Matrix (Fin 2) (Fin 2) Adeles) i j).2
    by_cases h : i = j <;> simp [pairMatrix, Matrix.one_apply, h]

/-- `combineGL` commutes with inversion. -/
theorem combineGL_inv (r : BinaryRealGL) (f : BinaryFiniteGL) :
    (combineGL r f)⁻¹ = combineGL r⁻¹ f⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, combineGL_mul, mul_inv_cancel, mul_inv_cancel, combineGL_one]

/-- Every adelic matrix is the combination of its real and finite components. -/
theorem combineGL_parts (g : BinaryAdelicGL) : combineGL (realPart g) (finitePart g) = g := by
  apply Units.ext
  ext i j <;> rfl

/-- Conjugating an archimedean matrix by an adelic matrix only sees its real component. -/
theorem inv_mul_atInfinity_mul (g : BinaryAdelicGL) (x : BinaryRealGL) :
    g⁻¹ * atInfinity x * g = atInfinity ((realPart g)⁻¹ * x * realPart g) := by
  conv_lhs => rw [← combineGL_parts g]
  rw [atInfinity, atInfinity, combineGL_inv, combineGL_mul, combineGL_mul]
  simp

/-- Conjugating a finite-adelic matrix by an adelic matrix only sees its finite component. -/
theorem inv_mul_atFinite_mul (g : BinaryAdelicGL) (u : BinaryFiniteGL) :
    g⁻¹ * atFinite u * g = atFinite ((finitePart g)⁻¹ * u * finitePart g) := by
  conv_lhs => rw [← combineGL_parts g]
  rw [atFinite, atFinite, combineGL_inv, combineGL_mul, combineGL_mul]
  simp

/-- On invertible matrices, `invertibleMatrix` commutes with conjugation. -/
theorem invertibleMatrix_conj (r : BinaryRealGL) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    invertibleMatrix ((r⁻¹ : BinaryRealGL).val * A * r.val) = r⁻¹ * invertibleMatrix A * r := by
  have hdet : ((r⁻¹ : BinaryRealGL).val * A * r.val).det ≠ 0 := by
    rw [det_mul, det_mul]
    exact mul_ne_zero (mul_ne_zero (GeneralLinearGroup.det_ne_zero _) hA)
      (GeneralLinearGroup.det_ne_zero _)
  apply Units.ext
  simp only [invertibleMatrix, dite_eq_left hdet, dite_eq_left hA, Units.val_mul]
  rfl

/-! ### Open compact subgroups of `GL₂(𝔸_f)` -/

local instance integralCompletionTopologicalRing (v : FinitePlace) :
    IsTopologicalRing (v.adicCompletionIntegers ℚ) :=
  inferInstanceAs (IsTopologicalRing (v.adicCompletionIntegers ℚ).toSubring)

/-- A subgroup of `GL₂(𝔸_f)` is open and compact. -/
def IsOpenCompact (U : Subgroup BinaryFiniteGL) : Prop :=
  IsOpen (U : Set BinaryFiniteGL) ∧ IsCompact (U : Set BinaryFiniteGL)

/-- The integral points `GL₂(Ẑ)`, embedded in `GL₂(𝔸_f)`. -/
def integralLevel : Subgroup BinaryFiniteGL :=
  (GeneralLinearGroup.map (n := Fin 2) integralEmbedding).range

theorem integralMap_continuous :
    Continuous (GeneralLinearGroup.map integralEmbedding (n := Fin 2)) := by
  apply Units.continuous_map
  exact continuous_pi fun i => continuous_pi fun j =>
    integralEmbedding_isOpenEmbedding.continuous.comp
      ((continuous_apply j).comp (continuous_apply i))

/-- `GL₂(Ẑ)` is an open compact subgroup of `GL₂(𝔸_f)`. -/
theorem integralLevel_isOpenCompact : IsOpenCompact integralLevel := by
  refine ⟨?_, ?_⟩
  · have ho : IsOpenMap (GeneralLinearGroup.map integralEmbedding (n := Fin 2)) := by
      apply Units.isOpenMap_map
      · exact Matrix.map_injective integralEmbedding_injective
      · exact (Topology.IsOpenEmbedding.piMap fun _ : Fin 2 =>
          Topology.IsOpenEmbedding.piMap fun _ : Fin 2 =>
            integralEmbedding_isOpenEmbedding).isOpenMap
    rw [integralLevel, MonoidHom.coe_range]
    exact ho.isOpen_range
  · let : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
      inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
    rw [integralLevel, MonoidHom.coe_range]
    exact isCompact_range integralMap_continuous

/-- The intersection of two open compact subgroups is open compact. -/
theorem IsOpenCompact.inf {U U' : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    (hU' : IsOpenCompact U') : IsOpenCompact (U ⊓ U') :=
  ⟨hU.1.inter hU'.1, hU.2.inter_right (Subgroup.isClosed_of_isOpen U' hU'.1)⟩

/-- The conjugate `f U f⁻¹` of an open compact subgroup is open compact. -/
theorem IsOpenCompact.map_conj {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    (f : BinaryFiniteGL) : IsOpenCompact (U.map (MulAut.conj f).toMonoidHom) := by
  let e : BinaryFiniteGL ≃ₜ BinaryFiniteGL :=
    (Homeomorph.mulLeft f).trans (Homeomorph.mulRight f⁻¹)
  have he : (U.map (MulAut.conj f).toMonoidHom : Set BinaryFiniteGL) = e '' U := by
    rw [Subgroup.coe_map]
    rfl
  rw [IsOpenCompact, he]
  exact ⟨e.isOpenMap _ hU.1, hU.2.image e.continuous⟩

/-! ### The smooth subspace -/

section Smooth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Representation ℂ BinaryAdelicGL H)

/-- The zero vector is smooth. -/
theorem isSmoothVector_zero : IsSmoothVector π 0 := by
  refine ⟨?_, integralLevel, integralLevel_isOpenCompact.1, integralLevel_isOpenCompact.2,
    fun _ => map_zero _⟩
  simp only [Smooth, map_zero]
  exact contDiffOn_const

variable {π}

/-- Sums of smooth vectors are smooth. -/
theorem IsSmoothVector.add {v w : H} (hv : IsSmoothVector π v) (hw : IsSmoothVector π w) :
    IsSmoothVector π (v + w) := by
  obtain ⟨hvs, U, hUo, hUc, hUv⟩ := hv
  obtain ⟨hws, U', hUo', hUc', hUw⟩ := hw
  have hUU' := IsOpenCompact.inf ⟨hUo, hUc⟩ ⟨hUo', hUc'⟩
  refine ⟨?_, U ⊓ U', hUU'.1, hUU'.2, fun u => ?_⟩
  · simp only [Smooth, map_add]
    exact ContDiffOn.add hvs hws
  · rw [map_add, hUv ⟨u.val, u.property.1⟩, hUw ⟨u.val, u.property.2⟩]

/-- Complex multiples of smooth vectors are smooth. -/
theorem IsSmoothVector.smul (c : ℂ) {v : H} (hv : IsSmoothVector π v) :
    IsSmoothVector π (c • v) := by
  obtain ⟨hvs, U, hUo, hUc, hUv⟩ := hv
  refine ⟨?_, U, hUo, hUc, fun u => ?_⟩
  · simp only [Smooth, map_smul]
    exact ContDiffOn.const_smul c hvs
  · rw [map_smul, hUv u]

variable (π) in
/-- The smooth vectors of `π`: analytic along `GL₂(ℝ)` and fixed by an open compact subgroup of
`GL₂(𝔸_f)`. -/
def smoothSubmodule : Submodule ℂ H where
  carrier := {v | IsSmoothVector π v}
  zero_mem' := isSmoothVector_zero π
  add_mem' := IsSmoothVector.add
  smul_mem' := IsSmoothVector.smul

@[simp]
theorem mem_smoothSubmodule {v : H} : v ∈ smoothSubmodule π ↔ IsSmoothVector π v := Iff.rfl

/-- An operator of a unitary representation, as a continuous complex-linear map. -/
def unitaryOperator (hu : ∀ g v, ‖π g v‖ = ‖v‖) (g : BinaryAdelicGL) : H →L[ℂ] H :=
  (π g).mkContinuous 1 fun v => by rw [hu, one_mul]

@[simp]
theorem unitaryOperator_apply (hu : ∀ g v, ‖π g v‖ = ‖v‖) (g : BinaryAdelicGL) (v : H) :
    unitaryOperator hu g v = π g v := rfl

/-- The real-linear map `A ↦ r⁻¹ A r` on one-tuples of `2 × 2` real matrices. -/
def conjMatrixMap (r : BinaryRealGL) :
    (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) →L[ℝ] (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) :=
  LinearMap.toContinuousLinearMap <| LinearMap.pi fun i =>
    (LinearMap.mulLeft ℝ (r⁻¹ : BinaryRealGL).val ∘ₗ LinearMap.mulRight ℝ r.val) ∘ₗ
      LinearMap.proj i

theorem conjMatrixMap_apply (r : BinaryRealGL) (A : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)
    (i : Fin 1) : conjMatrixMap r A i = (r⁻¹ : BinaryRealGL).val * A i * r.val := by
  simp [conjMatrixMap, mul_assoc]

/-- The pointwise identity behind the stability of smooth vectors under translation:
`π(x) π(g) v = π(g) π(g⁻¹ x g) v` for an archimedean `x`. -/
theorem translate_pointwise (g : BinaryAdelicGL) (v : H) (x : BinaryRealGL) :
    π (atInfinity x) (π g v) = π g (π (atInfinity ((realPart g)⁻¹ * x * realPart g)) v) := by
  have h : atInfinity x * g = g * atInfinity ((realPart g)⁻¹ * x * realPart g) := by
    rw [← inv_mul_atInfinity_mul]
    group
  calc π (atInfinity x) (π g v) = π (atInfinity x * g) v := by
        rw [map_mul, Module.End.mul_apply]
    _ = π (g * atInfinity ((realPart g)⁻¹ * x * realPart g)) v := by rw [h]
    _ = π g (π (atInfinity ((realPart g)⁻¹ * x * realPart g)) v) := by
        rw [map_mul, Module.End.mul_apply]

/-- Smooth vectors are stable under every operator of a unitary representation. -/
theorem IsSmoothVector.translate (hu : ∀ g v, ‖π g v‖ = ‖v‖) (g : BinaryAdelicGL) {v : H}
    (hv : IsSmoothVector π v) : IsSmoothVector π (π g v) := by
  obtain ⟨hvs, U, hUo, hUc, hUv⟩ := hv
  have hU := (IsOpenCompact.map_conj ⟨hUo, hUc⟩ (finitePart g))
  refine ⟨?_, U.map (MulAut.conj (finitePart g)).toMonoidHom, hU.1, hU.2, fun u => ?_⟩
  · have hmaps : Set.MapsTo (conjMatrixMap (realPart g))
        {A : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ | ∀ i, (A i).det ≠ 0}
        {A | ∀ i, (A i).det ≠ 0} := by
      intro A hA i
      rw [conjMatrixMap_apply, det_mul, det_mul]
      exact mul_ne_zero (mul_ne_zero (GeneralLinearGroup.det_ne_zero _) (hA i))
        (GeneralLinearGroup.det_ne_zero _)
    have key := ((unitaryOperator hu g).restrictScalars ℝ).contDiff.comp_contDiffOn
      (ContDiffOn.comp hvs (conjMatrixMap (realPart g)).contDiff.contDiffOn hmaps)
    refine key.congr fun A hA => ?_
    have h2 : invertibleMatrix ((conjMatrixMap (realPart g) A) 0) =
        (realPart g)⁻¹ * invertibleMatrix (A 0) * realPart g := by
      rw [conjMatrixMap_apply]
      exact invertibleMatrix_conj (realPart g) (hA 0)
    have h1 := translate_pointwise (π := π) g v (invertibleMatrix (A 0))
    rw [← h2] at h1
    exact h1
  · obtain ⟨_, hmem⟩ := u
    obtain ⟨u, hu', rfl⟩ := Subgroup.mem_map.mp hmem
    have : π (atFinite ((MulAut.conj (finitePart g)).toMonoidHom u)) =
        π g * π (atFinite u) * π g⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      have h := inv_mul_atFinite_mul g⁻¹ u
      simp only [inv_inv, map_inv] at h
      rw [h]
      rfl
    rw [this, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (π g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hUv ⟨u, hu'⟩]

/-- Smooth vectors are stable under every operator of a unitary representation. -/
theorem smooth_stable (hu : ∀ g v, ‖π g v‖ = ‖v‖) (g : BinaryAdelicGL) {v : H}
    (hv : v ∈ smoothSubmodule π) : π g v ∈ smoothSubmodule π :=
  IsSmoothVector.translate hu g hv

/-- Assembling a `CuspidalRepresentation` whose smooth subspace is `smoothSubmodule π`: the
`smooth`, `smooth_exact` and `smooth_stable` fields are discharged here, and the caller supplies
the realization and its analytic properties. -/
def ofModel {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Representation ℂ BinaryAdelicGL H) (nontrivial : Nontrivial H)
    (unitary : ∀ g v, ‖π g v‖ = ‖v‖) (continuous : ∀ v, Continuous (fun g => π g v))
    (irreducible : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ g v, v ∈ W → π g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (realize : smoothSubmodule π →ₗ[ℂ] (BinaryAdelicGL → ℂ))
    (injective : Function.Injective realize)
    (equivariant : ∀ g (v : smoothSubmodule π) x,
      realize ⟨π g v.val, smooth_stable unitary g v.property⟩ x = realize v (x * g))
    (centralCharacter : Adelesˣ →* ℂ) (centralUnitary : ∀ t, ‖centralCharacter t‖ = 1)
    (central : ∀ t v x, realize v (GeneralLinearGroup.scalar (Fin 2) t * x) =
      centralCharacter t * realize v x)
    (leftRational : ∀ γ : BinaryRationalGL, ∀ v x,
      realize v (GeneralLinearGroup.map rationalAdele γ * x) = realize v x)
    (scalarSmooth : ∀ v g, Smooth (fun x : Fin 1 → BinaryRealGL =>
      realize v (g * atInfinity (x 0))))
    (bounded : ∀ v, ∃ C : ℝ, ∀ x, ‖realize v x‖ ≤ C)
    (cuspidal : ∀ v g,
      MeasureTheory.IntegrableOn (fun u => realize v (binaryUnipotent u * g)) additiveDomain
        adeleMeasure ∧
      (∫ u in additiveDomain, realize v (binaryUnipotent u * g) ∂adeleMeasure) = 0) :
    CuspidalRepresentation where
  H := H
  π := π
  nontrivial := nontrivial
  unitary := unitary
  continuous := continuous
  irreducible := irreducible
  smooth := smoothSubmodule π
  smooth_exact := fun _ => Iff.rfl
  smooth_stable := fun g _ hv => smooth_stable unitary g hv
  realize := realize
  injective := injective
  equivariant := equivariant
  centralCharacter := centralCharacter
  centralUnitary := centralUnitary
  central := central
  leftRational := leftRational
  scalarSmooth := scalarSmooth
  bounded := bounded
  cuspidal := cuspidal

end Smooth

end TernaryPeriodPolynomials.Automorphic.SmoothVectors
