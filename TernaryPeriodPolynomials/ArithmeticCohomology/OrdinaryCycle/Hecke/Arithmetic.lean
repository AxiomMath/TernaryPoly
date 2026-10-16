module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.SupportTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.Action
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.Transfer

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryHeckeArithmetic
open Matrix PolynomialGLAction ModThreeGoodAction

/-- The same literal coefficient-extension map used by the existing residue action. -/
abbrev integral : IntegralGL →* GL3 := SinglePoleSupport.integralRational

/-- Rational coefficient extension is injective on actual integral invertible matrices. -/
theorem integral_injective : Function.Injective integral := by
  intro g h he
  apply Units.ext
  ext i j
  have hij := congrArg (fun x : GL3 => x.val i j) he
  exact Int.cast_injective hij

/-- The actual integral group as a subgroup of rational GL3. -/
def Gamma : Subgroup GL3 := integral.range

/-- The integral group and its actual rational image are isomorphic. -/
def integralEquiv : IntegralGL ≃* Gamma := MonoidHom.ofInjective integral_injective

@[simp] theorem integralEquiv_val (g : IntegralGL) : (integralEquiv g).val=integral g := rfl

@[simp] theorem integral_eq_full (g : IntegralGL) : integral g=OrdinaryFullAction.integral g := rfl

@[simp] theorem integral_apply (g : IntegralGL) (i j : Fin 3) : (integral g).val i j=(g.val i j : ℚ) := rfl

/-- Entrywise integrality of a rational matrix. -/
def IntegralEntries (M : Matrix (Fin 3) (Fin 3) ℚ) : Prop :=
  ∀ i j, ∃ z : ℤ, (z : ℚ)=M i j

/-- An invertible rational matrix is integral exactly when both it and its inverse have integral entries. -/
theorem mem_Gamma_iff (g : GL3) : g ∈ Gamma ↔ IntegralEntries g.val ∧ IntegralEntries (g⁻¹).val := by
  constructor
  · rintro ⟨h,rfl⟩
    constructor
    · exact fun i j => ⟨h.val i j,rfl⟩
    · intro i j
      exact ⟨(h⁻¹).val i j,by rw [←map_inv]; rfl⟩
  · rintro ⟨h,k⟩
    choose m hM using h
    choose n hN using k
    let M : Matrix (Fin 3) (Fin 3) ℤ := m
    let N : Matrix (Fin 3) (Fin 3) ℤ := n
    have hm : M.map (Int.castRingHom ℚ)=g.val := by ext i j; exact hM i j
    have hn : N.map (Int.castRingHom ℚ)=(g⁻¹).val := by ext i j; exact hN i j
    have hmn : M*N=1 := by
      ext i j
      apply Int.cast_injective (α := ℚ)
      have he : (M*N).map (Int.castRingHom ℚ)=1 := by
        rw [Matrix.map_mul,hm,hn]
        exact g.val_inv
      simpa [Matrix.one_apply] using congrArg (fun X => X i j) he
    have hnm : N*M=1 := by
      ext i j
      apply Int.cast_injective (α := ℚ)
      have he : (N*M).map (Int.castRingHom ℚ)=1 := by
        rw [Matrix.map_mul,hn,hm]
        exact g.inv_val
      simpa [Matrix.one_apply] using congrArg (fun X => X i j) he
    refine ⟨⟨M,N,hmn,hnm⟩,?_⟩
    apply Units.ext
    exact hm

end TernaryPoly.OrdinaryHeckeArithmetic
