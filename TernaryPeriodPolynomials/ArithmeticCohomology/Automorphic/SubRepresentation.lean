module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.SmoothVectors

@[expose] public section


/-!
# Closed invariant subspaces as cuspidal representations

A closed `π`-invariant subspace `W` of a unitary representation `π` of `GL₂(𝔸)` carries the
restricted representation `restrictRep π W`, whose smooth vectors are exactly the smooth vectors
of `π` lying in `W` (`isSmoothVector_restrict_iff`).  A `Realization` of the smooth vectors of
`π` by scalar cuspidal automorphic functions therefore restricts to `W`, and
`Realization.cuspidalRepresentation` packages the restriction, together with irreducibility and
nontriviality of `W`, as a `CuspidalRepresentation`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.Automorphic.SmoothVectors

namespace TernaryPeriodPolynomials.Automorphic.SubRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : Representation ℂ BinaryAdelicGL H) (W : Submodule ℂ H)

/-- The representation restricted to an invariant subspace. -/
def restrictRep (hinv : ∀ g v, v ∈ W → π g v ∈ W) : Representation ℂ BinaryAdelicGL W where
  toFun g := (π g).restrict (hinv g)
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp

variable {π W}

omit [CompleteSpace H] in
theorem restrictRep_apply_coe (hinv : ∀ g v, v ∈ W → π g v ∈ W) (g : BinaryAdelicGL) (v : W) :
    ((restrictRep π W hinv g v : W) : H) = π g (v : H) := rfl

omit [CompleteSpace H] in
theorem restrictRep_unitary (hu : ∀ g v, ‖π g v‖ = ‖v‖) (hinv : ∀ g v, v ∈ W → π g v ∈ W)
    (g : BinaryAdelicGL) (v : W) : ‖restrictRep π W hinv g v‖ = ‖v‖ := by
  change ‖π g (v : H)‖ = ‖(v : H)‖
  exact hu g v

omit [CompleteSpace H] in
theorem restrictRep_continuous (hc : ∀ v, Continuous (fun g => π g v))
    (hinv : ∀ g v, v ∈ W → π g v ∈ W) (v : W) :
    Continuous (fun g => restrictRep π W hinv g v) := by
  exact Topology.IsInducing.subtypeVal.continuous_iff.mpr (hc (v : H))

/-- The smooth vectors of the restriction are the smooth vectors of `π` lying in `W`. -/
theorem isSmoothVector_restrict_iff (hW : IsClosed (W : Set H))
    (hinv : ∀ g v, v ∈ W → π g v ∈ W) (v : W) :
    IsSmoothVector (restrictRep π W hinv) v ↔ IsSmoothVector π (v : H) := by
  have : CompleteSpace W := hW.completeSpace_coe
  unfold IsSmoothVector
  refine and_congr ?_ ?_
  · unfold Smooth
    constructor
    · intro h
      exact ((W.subtypeL.restrictScalars ℝ).contDiff).comp_contDiffOn h
    · intro h
      have hP := ((W.orthogonalProjectionOnto).restrictScalars ℝ).contDiff.comp_contDiffOn h
      refine hP.congr fun A hA => ?_
      exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
        (K := W) (restrictRep π W hinv _ v)).symm
  · refine exists_congr fun U => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    constructor
    · intro h u
      exact congrArg Subtype.val (h u)
    · intro h u
      exact Subtype.ext (h u)

/-- A realization of the smooth vectors of a unitary representation `π` of `GL₂(𝔸)` by scalar
cuspidal automorphic functions; every field of `CuspidalRepresentation` other than the Hilbert
space data and irreducibility. -/
structure Realization (π : Representation ℂ BinaryAdelicGL H)
    (hu : ∀ g v, ‖π g v‖ = ‖v‖) where
  realize : smoothSubmodule π →ₗ[ℂ] (BinaryAdelicGL → ℂ)
  injective : Function.Injective realize
  equivariant : ∀ g (v : smoothSubmodule π) x,
    realize ⟨π g v.val, smooth_stable hu g v.property⟩ x = realize v (x * g)
  centralCharacter : Adelesˣ →* ℂ
  centralUnitary : ∀ t, ‖centralCharacter t‖ = 1
  central : ∀ t v x, realize v (GeneralLinearGroup.scalar (Fin 2) t * x) =
    centralCharacter t * realize v x
  leftRational : ∀ γ : BinaryRationalGL, ∀ v x,
    realize v (GeneralLinearGroup.map rationalAdele γ * x) = realize v x
  scalarSmooth : ∀ v g, Smooth (fun x : Fin 1 → BinaryRealGL =>
    realize v (g * atInfinity (x 0)))
  bounded : ∀ v, ∃ C : ℝ, ∀ x, ‖realize v x‖ ≤ C
  cuspidal : ∀ v g,
    MeasureTheory.IntegrableOn (fun u => realize v (binaryUnipotent u * g)) additiveDomain
      adeleMeasure ∧
    (∫ u in additiveDomain, realize v (binaryUnipotent u * g) ∂adeleMeasure) = 0

/-- The inclusion of the smooth vectors of the restriction into the smooth vectors of `π`. -/
def smoothInclusion (hW : IsClosed (W : Set H)) (hinv : ∀ g v, v ∈ W → π g v ∈ W) :
    smoothSubmodule (restrictRep π W hinv) →ₗ[ℂ] smoothSubmodule π where
  toFun v := ⟨(v.val : H), (isSmoothVector_restrict_iff hW hinv v.val).mp v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smoothInclusion_injective (hW : IsClosed (W : Set H))
    (hinv : ∀ g v, v ∈ W → π g v ∈ W) :
    Function.Injective (smoothInclusion hW hinv) := by
  intro v w h
  have h' : ((v.val : W) : H) = ((w.val : W) : H) :=
    congrArg (fun x : smoothSubmodule π => (x.val : H)) h
  exact Subtype.ext (Subtype.ext h')

/-- Restricting a realization to a closed invariant subspace. -/
def Realization.restrict {hu : ∀ g v, ‖π g v‖ = ‖v‖} (R : Realization π hu)
    (hW : IsClosed (W : Set H)) (hinv : ∀ g v, v ∈ W → π g v ∈ W) :
    Realization (restrictRep π W hinv) (restrictRep_unitary hu hinv) where
  realize := R.realize ∘ₗ smoothInclusion hW hinv
  injective := R.injective.comp (smoothInclusion_injective hW hinv)
  equivariant g v x := R.equivariant g (smoothInclusion hW hinv v) x
  centralCharacter := R.centralCharacter
  centralUnitary := R.centralUnitary
  central t v x := R.central t (smoothInclusion hW hinv v) x
  leftRational γ v x := R.leftRational γ (smoothInclusion hW hinv v) x
  scalarSmooth v g := R.scalarSmooth (smoothInclusion hW hinv v) g
  bounded v := R.bounded (smoothInclusion hW hinv v)
  cuspidal v g := R.cuspidal (smoothInclusion hW hinv v) g

/-- A realization of a unitary representation with irreducibility and nontriviality assembles to
a `CuspidalRepresentation`. -/
def Realization.cuspidalRepresentation {hu : ∀ g v, ‖π g v‖ = ‖v‖} (R : Realization π hu)
    (nontrivial : Nontrivial H) (continuous : ∀ v, Continuous (fun g => π g v))
    (irreducible : ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
      (∀ g v, v ∈ W → π g v ∈ W) → W = ⊥ ∨ W = ⊤) : CuspidalRepresentation :=
  ofModel π nontrivial hu continuous irreducible R.realize R.injective R.equivariant
    R.centralCharacter R.centralUnitary R.central R.leftRational R.scalarSmooth R.bounded
    R.cuspidal

omit [CompleteSpace H] in
/-- A closed invariant subspace with no proper nonzero closed invariant subspace gives an
irreducible restricted representation. -/
theorem restrictRep_irreducible (hW : IsClosed (W : Set H)) (hinv : ∀ g v, v ∈ W → π g v ∈ W)
    (hirr : ∀ W' : Submodule ℂ H, IsClosed (W' : Set H) → W' ≤ W →
      (∀ g v, v ∈ W' → π g v ∈ W') → W' = ⊥ ∨ W' = W)
    (X : Submodule ℂ W) (hX : IsClosed (X : Set W))
    (hXinv : ∀ g v, v ∈ X → restrictRep π W hinv g v ∈ X) : X = ⊥ ∨ X = ⊤ := by
  have hclosed : IsClosed ((X.map W.subtype : Submodule ℂ H) : Set H) := by
    have : ((X.map W.subtype : Submodule ℂ H) : Set H) = Subtype.val '' (X : Set W) := by
      ext; simp
    rw [this]
    exact hW.isClosedEmbedding_subtypeVal.isClosedMap _ hX
  have hle : X.map W.subtype ≤ W := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hinv' : ∀ g v, v ∈ X.map W.subtype → π g v ∈ X.map W.subtype := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨restrictRep π W hinv g x, hXinv g x hx, rfl⟩
  rcases hirr _ hclosed hle hinv' with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    have hmem : (x : H) ∈ X.map W.subtype := ⟨x, hx, rfl⟩
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).mpr (Subtype.ext ((Submodule.mem_bot ℂ).mp hmem))
  · right
    refine eq_top_iff.mpr fun x _ => ?_
    have hmem : (x : H) ∈ X.map W.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hmem
    exact (Subtype.ext hyx : y = x) ▸ hy

/-- **Builder.** A realization of the smooth vectors of a unitary, strongly continuous
representation `π`, together with a nonzero closed invariant subspace `W` that contains no
proper nonzero closed invariant subspace, gives a `CuspidalRepresentation` on `W`. -/
def Realization.cuspidalOfInvariant {hu : ∀ g v, ‖π g v‖ = ‖v‖} (R : Realization π hu)
    (hc : ∀ v, Continuous (fun g => π g v)) (hW : IsClosed (W : Set H)) (hne : W ≠ ⊥)
    (hinv : ∀ g v, v ∈ W → π g v ∈ W)
    (hirr : ∀ W' : Submodule ℂ H, IsClosed (W' : Set H) → W' ≤ W →
      (∀ g v, v ∈ W' → π g v ∈ W') → W' = ⊥ ∨ W' = W) : CuspidalRepresentation :=
  have : CompleteSpace W := hW.completeSpace_coe
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  (R.restrict hW hinv).cuspidalRepresentation inferInstance (restrictRep_continuous hc hinv)
    (restrictRep_irreducible hW hinv hirr)

end TernaryPeriodPolynomials.Automorphic.SubRepresentation
