module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.SphericalLevel
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.GelfandTrick
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.IntegerCartan
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.StrongApproximation
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


/-!
# Spherical Hecke operators act by scalars

For every `CuspidalRepresentation σ` and every `γ ∈ GL₂(𝔸_f)`, the Hecke operator of the double
coset `K γ K`, `K = GL₂(Ẑ)`, acts on the `K`-fixed vectors of `σ` by a scalar. The proof uses:
* Gelfand's trick with the transpose;
* the Cartan property from integral diagonalization and strong approximation
  `GL₂(𝔸_f) = GL₂(ℚ) GL₂(Ẑ)`;
* Schur's lemma on the compressions.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.RepresentationTheory

/-- Transpose on `GL₂`. -/
def transposeGL {R : Type*} [CommRing R] (x : GeneralLinearGroup (Fin 2) R) :
    GeneralLinearGroup (Fin 2) R :=
  ⟨x.valᵀ, (x⁻¹).valᵀ, by rw [← transpose_mul, x.inv_mul, transpose_one],
    by rw [← transpose_mul, x.mul_inv, transpose_one]⟩

@[simp] theorem transposeGL_val {R : Type*} [CommRing R] (x : GeneralLinearGroup (Fin 2) R) :
    (transposeGL x).val = x.valᵀ := rfl

theorem transposeGL_mul {R : Type*} [CommRing R] (x y : GeneralLinearGroup (Fin 2) R) :
    transposeGL (x * y) = transposeGL y * transposeGL x := by
  apply Units.ext; simp [transpose_mul]

theorem transposeGL_transposeGL {R : Type*} [CommRing R] (x : GeneralLinearGroup (Fin 2) R) :
    transposeGL (transposeGL x) = x := by
  apply Units.ext; simp

theorem transposeGL_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : GeneralLinearGroup (Fin 2) R) :
    transposeGL (GeneralLinearGroup.map f x) = GeneralLinearGroup.map f (transposeGL x) := by
  apply Units.ext; refine Matrix.ext fun i j => ?_; simp [GeneralLinearGroup.map]

/-- `atFinite` as a monoid homomorphism. -/
def atFiniteHom : BinaryFiniteGL →* BinaryAdelicGL where
  toFun := atFinite
  map_one' := by
    apply Units.ext
    refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
      simp [atFinite, combineGL, pairMatrix, Matrix.one_apply] <;> split_ifs <;> rfl
  map_mul' a b := (HeckeTranslate.HeckeInvariance.atFinite_mul a b).symm

theorem atFiniteHom_injective : Function.Injective atFiniteHom := by
  intro a b h
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun x : BinaryAdelicGL => (x.val i j).2) h
  simpa [atFiniteHom, atFinite, combineGL, pairMatrix] using this

theorem transposeGL_atFinite (y : BinaryFiniteGL) :
    transposeGL (atFinite y) = atFinite (transposeGL y) := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;>
    simp [atFinite, combineGL, pairMatrix, Matrix.one_apply, eq_comm]

/-- `GL₂(Ẑ)` inside `GL₂(𝔸)`. -/
def sphericalLevel : Subgroup BinaryAdelicGL := sphericalFinite.map atFiniteHom

theorem transposeGL_sphericalFinite {k : BinaryFiniteGL} (hk : k ∈ sphericalFinite) :
    transposeGL k ∈ sphericalFinite := by
  obtain ⟨k', rfl⟩ := hk
  exact ⟨transposeGL k', (transposeGL_map _ _).symm⟩

/-- Integral unimodular matrices lie in `GL₂(Ẑ)`. -/
theorem int_mem_sphericalFinite (U : IntegerCartan.M2) (hU : IsUnit U.det) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (nonsingInvUnit U hU)) ∈ sphericalFinite := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) (nonsingInvUnit U hU), ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  simp only [GeneralLinearGroup.map, Units.coe_map]
  have h := RingHom.ext_int (integralEmbedding.comp (Int.castRingHom IntegralAdeles))
    ((algebraMap ℚ FiniteAdeles).comp (Int.castRingHom ℚ))
  exact congrArg (fun f : ℤ →+* FiniteAdeles => f ((nonsingInvUnit U hU).val i j)) h

/-- **Cartan property** for the transpose on `GL₂(𝔸_f)`. -/
theorem transpose_cartan (y : BinaryFiniteGL) :
    ∃ a b : sphericalFinite, transposeGL y = a.val * y * b.val := by
  obtain ⟨γ, k, rfl⟩ := BinaryStrongApproximation.exists_rational_integral y
  have hdet : γ.val.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det γ).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  obtain ⟨U, V, hU, hV, hUV⟩ := IntegerCartan.rat_transpose_equiv γ.val hdet
  set Uq := GeneralLinearGroup.map (Int.castRingHom ℚ) (nonsingInvUnit U hU)
  set Vq := GeneralLinearGroup.map (Int.castRingHom ℚ) (nonsingInvUnit V hV)
  have hγ : transposeGL γ = Uq * γ * Vq := by
    apply Units.ext
    rw [transposeGL_val, ← hUV]
    rfl
  set f := GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (n := Fin 2)
  set m := GeneralLinearGroup.map integralEmbedding (n := Fin 2)
  have hUmem := int_mem_sphericalFinite U hU
  have hVmem := int_mem_sphericalFinite V hV
  have hkT : transposeGL (m k) ∈ sphericalFinite := transposeGL_sphericalFinite ⟨k, rfl⟩
  have hk : m k ∈ sphericalFinite := ⟨k, rfl⟩
  refine ⟨⟨transposeGL (m k) * f Uq, sphericalFinite.mul_mem hkT hUmem⟩,
    ⟨(m k)⁻¹ * f Vq, sphericalFinite.mul_mem (sphericalFinite.inv_mem hk) hVmem⟩, ?_⟩
  change transposeGL (f γ * m k) = transposeGL (m k) * f Uq * (f γ * m k) * ((m k)⁻¹ * f Vq)
  rw [transposeGL_mul, transposeGL_map integralEmbedding k,
    show transposeGL (f γ) = f (transposeGL γ) from transposeGL_map _ γ, hγ, map_mul, map_mul]
  group

/-- The transpose is a Gelfand involution for `GL₂(Ẑ) ⊂ GL₂(𝔸)`, Cartan on the finite part. -/
def sphericalGelfand : GelfandInvolution sphericalLevel where
  ι := transposeGL
  map_mul := transposeGL_mul
  invol := transposeGL_transposeGL
  mem := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨transposeGL k, transposeGL_sphericalFinite hk, (transposeGL_atFinite k).symm⟩
  F := atFiniteHom.range
  le := by rintro _ ⟨k, -, rfl⟩; exact ⟨k, rfl⟩
  memF := by
    rintro _ ⟨y, rfl⟩
    exact ⟨transposeGL y, (transposeGL_atFinite y).symm⟩
  cartan := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, b, hab⟩ := transpose_cartan y
    refine ⟨⟨atFinite a.val, ⟨a.val, a.property, rfl⟩⟩, ⟨atFinite b.val, ⟨b.val, b.property, rfl⟩⟩, ?_⟩
    change transposeGL (atFinite y) = atFinite a.val * atFinite y * atFinite b.val
    rw [transposeGL_atFinite, hab, HeckeTranslate.HeckeInvariance.atFinite_mul,
      HeckeTranslate.HeckeInvariance.atFinite_mul]

/-- The spherical double coset of `γ ∈ GL₂(𝔸_f)` inside `GL₂(𝔸)`. -/
def sphericalDoubleCoset (γ : BinaryFiniteGL) : DoubleCoset sphericalLevel :=
  (DoubleCoset.ofFinite sphericalFinite γ).map atFiniteHom atFiniteHom_injective

theorem sphericalDoubleCoset_g (γ : BinaryFiniteGL) :
    (sphericalDoubleCoset γ).g = atFinite γ := rfl

/-- Real and finite components of `GL₂(𝔸)`. -/
theorem binary_real_finite (h : BinaryAdelicGL) :
    h = atInfinity (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) h) *
      atFinite (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) h) := by
  rw [atInfinity, atFinite, HeckeTranslate.HeckeInvariance.combineGL_mul, mul_one, one_mul]
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;> simp [combineGL, pairMatrix, GeneralLinearGroup.map]

/-- **Spherical Hecke operators are scalars.** For every `CuspidalRepresentation` and every
`γ ∈ GL₂(𝔸_f)`, the Hecke operator of `GL₂(Ẑ) γ GL₂(Ẑ)` acts by a scalar on the
`GL₂(Ẑ)`-fixed vectors. -/
theorem sphericalHecke_scalar (σ : CuspidalRepresentation) (γ : BinaryFiniteGL) :
    ∃ z : ℂ, ∀ v ∈ fixedVectors σ sphericalLevel,
      heckeOperator σ (sphericalDoubleCoset γ) v = z • v := by
  apply heckeOperator_scalar_of_gelfand sphericalGelfand (sphericalDoubleCoset γ) ⟨γ, rfl⟩
  intro h
  refine ⟨atInfinity (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) h),
    sphericalDoubleCoset (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) h),
    binary_real_finite h, ⟨_, rfl⟩, ?_, ?_⟩
  · rintro ⟨_, ⟨k, -, rfl⟩⟩
    exact (HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity k _).symm
  · exact (HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity γ _).symm

end TernaryPeriodPolynomials.RepresentationTheory
