/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract -- abstract Hecke ops
import FLT.AutomorphicForm.QuaternionAlgebra.Defs -- definitions of automorphic forms
import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits -- for (π 0; 0 1)
import FLT.Mathlib.Topology.Algebra.RestrictedProduct

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain

open TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain.HeightOneSpectrum

open scoped TensorProduct

open scoped Pointwise

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator

namespace CosetComputations

-- let F be a totally real number field
variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

-- Let D/F be a quaternion algebra
variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

-- Let r be a rigidification of D, which is a collection of isomorphisms D ⊗ Fᵥ = M₂(Fᵥ)
-- for all finite places v of F, compatible with the adelic structure (i.e. inducing
-- an isomorphism D ⊗_F 𝔸_F^f = M₂(𝔸_F^f))
variable (r : Rigidification F D)

-- Let S be a finite set of finite places of F (the level)
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- let P be a good prime
variable {P : HeightOneSpectrum (𝓞 F)} (hP : P ∉ S)

variable (R : Type*) [CommRing R]

variable (v : HeightOneSpectrum (𝓞 F))

variable (α : v.adicCompletionIntegers F)

variable (hα : α ≠ 0)

variable {F D} in
open scoped TensorProduct.RightActions in
/-- U1(S) -/
noncomputable abbrev U1 : Subgroup (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.map (Units.map r.symm.toMonoidHom) (GL2.TameLevel S)

variable {F α hα} in
noncomputable def U1v : Subgroup (GL (Fin 2) (adicCompletion F v)) := (GL2.localTameLevel v)

variable {F v} in
noncomputable def g : (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1])

set_option synthInstance.maxHeartbeats 0 in
-- double coset space
variable {F v} in
noncomputable def doubleCosets :
  Set ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1v v)) :=
  (QuotientGroup.mk '' ((U1v v) * g α hα • ↑(U1v v) ))

variable {F v} in
noncomputable def gt (t : v.adicCompletionIntegers F) :
  (GL (Fin 2) (adicCompletion F v)) := by
  let gtInv : Invertible !![(α : v.adicCompletion F), t; 0, 1].det :=
  { invOf := (α : v.adicCompletion F)⁻¹,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of,
        mul_one, mul_zero, sub_zero]; rw [inv_mul_cancel₀]; exact_mod_cast hα,
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of,
        mul_one, mul_zero, sub_zero]; rw [mul_inv_cancel₀]; exact_mod_cast hα }
  exact Matrix.unitOfDetInvertible !![(α : v.adicCompletion F), t; 0, 1]

variable {F v α hα} in
noncomputable def ht (t : v.adicCompletion F) : (GL (Fin 2) (adicCompletion F v)) := by
  let htInv : Invertible !![1, t; 0, 1].det :=
  { invOf := 1,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
  exact Matrix.unitOfDetInvertible !![1, t; 0, 1]

variable {F v} in
noncomputable def singleCosetsFunction
  (t : ↑(adicCompletionIntegers F v) ⧸ (AddSubgroup.map (AddMonoidHom.mulLeft α)
    (⊤ : AddSubgroup ↑(adicCompletionIntegers F v)))) :
  ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1v v)) := by
  let tLift : ↑(adicCompletionIntegers F v) := Quotient.out t
  exact QuotientGroup.mk (gt α hα tLift)

set_option maxHeartbeats 500000 in
-- explicit matrix coset computations
variable {F v} in
omit [IsTotallyReal F] in
lemma U_coset : Set.BijOn (singleCosetsFunction α hα) ⊤ (doubleCosets α hα) := by
  have r (A : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) [Invertible A.det] :
    (↑(A.unitOfDetInvertible) : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) = A := rfl
  have valc₁ : Valued.v.IsEquiv (adicCompletionIntegers F v).valuation := by
    apply Valuation.isEquiv_valuation_valuationSubring
  constructor
  · intro t h
    have m : (gt α hα (Quotient.out t)) =  ht ↑(Quotient.out t) * g α hα := by
        have r₁ : (g α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
          = !![↑α, 0; 0, 1] := by
          rw[g]
          ext i j
          rw[Matrix.GeneralLinearGroup.diagonal]
          fin_cases i
          · fin_cases j
            · simp
            simp
          fin_cases j
          · simp
          simp
        ext i j; push_cast
        rw[gt, ht, r₁]
        rw[r, r]
        rw[Matrix.mul_apply]
        simp only [Fin.sum_univ_two, Fin.isValue]
        fin_cases i
        · fin_cases j
          · simp
          simp
        simp
    rw[singleCosetsFunction, m, doubleCosets]
    use (ht ↑(Quotient.out t) * g α hα)
    constructor
    · use ht ↑(Quotient.out t)
      constructor
      · rw[ht]
        constructor
        · let htInt : ((Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v))ˣ) := by
            let htInv : Invertible !![1, (Quotient.out t); 0, 1].det :=
            { invOf := 1,
              invOf_mul_self :=
              by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
              mul_invOf_self :=
              by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
            exact Matrix.unitOfDetInvertible !![1, (Quotient.out t); 0, 1]
          use htInt
          refine Units.eq_iff.mp ?_
          rw[r]
          have ho : (htInt = !![1, (Quotient.out t); 0, 1]) := rfl
          rw[Units.coe_map, ho]
          simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
            ValuationSubring.coe_subtype]
          ext i j
          fin_cases i
          · fin_cases j
            · simp
            simp
          fin_cases j
          · simp
          simp
        rw[r]
        simp
      use g α hα
      simp only [and_true]
      use (1 : GL (Fin 2) (adicCompletion F v))
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true]
      exact Subgroup.one_mem (U1v v)
    rfl

  constructor
  · intro t₁ h₁ t₂ h₂ h
    rw[singleCosetsFunction, singleCosetsFunction] at h
    have h₀ := QuotientGroup.eq.mp h
    have m : (gt α hα (Quotient.out t₁))⁻¹ * gt α hα (Quotient.out t₂)
      = ht ((α : v.adicCompletion F)⁻¹ *
        (( - (Quotient.out t₁) + (Quotient.out t₂)) : adicCompletion F v )) := by
        apply inv_mul_eq_iff_eq_mul.mpr
        rw [gt, gt, ht]
        ext i j; push_cast
        rw[r, r, r]
        rw[Matrix.mul_apply]
        simp only [Fin.sum_univ_two, Fin.isValue]
        fin_cases i
        · fin_cases j
          · simp
          simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, mul_one]
          rw[← mul_assoc, mul_inv_cancel₀, one_mul]; ring
          have hα₁ := Subtype.coe_ne_coe.mpr hα; assumption
        simp
    rw[m] at h₀
    obtain ⟨ ⟨ x, y ⟩ , z ⟩ := h₀
    apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 0 1) at y
    rw[ht] at y
    simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype, Matrix.map_apply] at y
    have w : ((x 0 1) : adicCompletion F v) = (α : v.adicCompletion F)⁻¹ *
        (( - (Quotient.out t₁) + (Quotient.out t₂)) : adicCompletion F v ) := by
        rw[y]; rfl
    conv_lhs =>
      apply Eq.symm (QuotientAddGroup.out_eq' t₁)
    conv_rhs =>
      apply Eq.symm (QuotientAddGroup.out_eq' t₂)
    apply QuotientAddGroup.eq.mpr
    use (x 0 1)
    constructor
    · simp
    simp only [Fin.isValue, AddMonoidHom.coe_mulLeft]
    apply (Subtype.coe_inj).mp; push_cast
    rw[w, ← mul_assoc, mul_inv_cancel₀, one_mul]
    have hα₁ := Subtype.coe_ne_coe.mpr hα; assumption

  intro co h
  obtain ⟨ co₀, ⟨ ⟨ co₁, h₁, ⟨ l, ⟨ ⟨ co₂, ⟨ h₂, z ⟩ ⟩ , hl ⟩ ⟩ ⟩ , h₀ ⟩ ⟩ := h
  have hp : co₀ = co₁ * (g α hα) * co₂ := by
    rw[← hl, ← z]; simp only [smul_eq_mul]; rw[mul_assoc]
  obtain ⟨ ⟨ ⟨ val_x₁, inv_x₁, val_inv_x₁, inv_val_x₁ ⟩ , y ⟩ , z ⟩ := h₁
  let a : (adicCompletionIntegers F v) := (val_x₁ 0 0)
  let b : (adicCompletionIntegers F v) := (val_x₁ 0 1)
  let c : (adicCompletionIntegers F v) := (val_x₁ 1 0)
  let d : (adicCompletionIntegers F v) := (val_x₁ 1 1)
  have h11 : c * (inv_x₁ 0 1) + d * (inv_x₁ 1 1) = 1 := by calc
    _ = (val_x₁ 1 0) * (inv_x₁ 0 1) + (val_x₁ 1 1) * (inv_x₁ 1 1) := rfl
    _ = (val_x₁ * inv_x₁) 1 1 := by rw[Matrix.mul_apply]; simp
    _ = 1 := by rw[val_inv_x₁]; simp
  have valc : Valued.v (c : adicCompletion F v) < 1 := by
    have hc : c = (val_x₁ 1 0) := rfl
    rw[hc]
    apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 1 0) at y
    simp only [RingHom.toMonoidHom_eq_coe, Units.map_mk, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      ValuationSubring.coe_subtype, Fin.isValue, Matrix.map_apply] at y
    rw[y]
    apply z.right
  have maxc : c ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    apply (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) c).mpr
    apply (Valuation.isEquiv_iff_val_lt_one.mp valc₁).mp
    exact valc
  have maxd : d ∉ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    by_contra maxd₁
    have max1 : c * (inv_x₁ 0 1) + d * (inv_x₁ 1 1)
      ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
      apply Ideal.add_mem
      repeat
        apply Ideal.mul_mem_right
        assumption
    rw[h11] at max1
    have nonunit : 1 ∈ nonunits ↥(adicCompletionIntegers F v) :=
      (IsLocalRing.mem_maximalIdeal 1).mp max1
    exact one_notMem_nonunits nonunit
  have dunit : IsUnit d := by
    by_contra dnotunit
    have dnonunit : d ∈ nonunits ↥(adicCompletionIntegers F v) := mem_nonunits_iff.mpr dnotunit
    have dmax : d ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
      (IsLocalRing.mem_maximalIdeal d).mpr dnonunit
    exact maxd dmax
  obtain ⟨ dinv, dvalinv, dinvval ⟩ := isUnit_iff_exists.mp dunit

  let t : ↥(adicCompletionIntegers F v) ⧸ AddSubgroup.map (AddMonoidHom.mulLeft α) ⊤ := b * dinv
  use t
  simp only [Set.top_eq_univ, Set.mem_univ, true_and]
  rw[singleCosetsFunction, ← h₀]
  apply QuotientGroup.eq.mpr
  rw[hp, ← mul_assoc]
  have uele (u₁ : GL (Fin 2) (adicCompletion F v)) (hu₁ : u₁ ∈ U1v v)
    (u₂ : GL (Fin 2) (adicCompletion F v)) (hu₂ : u₂ ∈ U1v v) :
    u₁ * u₂ ∈ U1v v := by
    exact (Subgroup.mul_mem_cancel_right (U1v v) hu₂).mpr hu₁
  have ht : t = b * dinv := rfl
  rw[← QuotientAddGroup.out_eq' t] at ht
  have ht₁ := QuotientAddGroup.eq.mp ht
  obtain ⟨q, hq⟩ := ht₁
  simp only [AddSubgroup.coe_top, Set.mem_univ, AddMonoidHom.coe_mulLeft, true_and] at hq
  have hq₁ : Quotient.out t = b * dinv - α * q := by rw[hq]; ring
  apply uele
  · let muMatrix : Matrix (Fin 2) (Fin 2) (adicCompletion F v) :=
      !![a-(Quotient.out t)*c, (α : adicCompletion F v)⁻¹ * (b-(Quotient.out t)*d); c*α, d]
    let mup : GL (Fin 2) (adicCompletion F v) := (gt α hα (Quotient.out t))⁻¹ * (co₁ * g α hα)
    have hmup : mup = (gt α hα (Quotient.out t))⁻¹ * (co₁ * g α hα) := rfl
    have m : mup = muMatrix := by
      have hp1 : (gt α hα (Quotient.out t))⁻¹
        = !![(α : adicCompletion F v)⁻¹, -(α : adicCompletion F v)⁻¹*(Quotient.out t);0,1] := by
        rw[gt]
        push_cast; rw[r]
        rw[Matrix.inv_def]
        simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_eq_inv',
          Matrix.adjugate_fin_two_of, neg_zero, Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
          mul_neg, Matrix.smul_empty, neg_mul, EmbeddingLike.apply_eq_iff_eq]
        rw [inv_mul_cancel₀]; exact_mod_cast hα
      have hp2 : co₁ = !![(a : adicCompletion F v),b;c,d] := by
        rw[← y]
        ext i j
        simp only [RingHom.toMonoidHom_eq_coe, Units.map_mk, MonoidHom.coe_coe,
          RingHom.mapMatrix_apply, ValuationSubring.coe_subtype, Matrix.map_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_fin_one]
        fin_cases i
        · fin_cases j
          · simp; rfl
          simp; rfl
        fin_cases j
        · simp; rfl
        simp; rfl
      have hp3 : g α hα = !![(α : adicCompletion F v), 0;0,1] := by
        rw[g]
        ext i j
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
        fin_cases i
        · fin_cases j
          · simp; rfl
          simp; rfl
        fin_cases j
        · simp; rfl
        simp; rfl
      rw[hmup]; push_cast; rw[hp2, hp3]
      norm_cast; rw[hp1]
      unfold muMatrix
      simp only [neg_mul, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
        Matrix.head_cons, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
        Matrix.tail_cons, mul_one, Matrix.empty_vecMul, add_zero, Matrix.add_cons, zero_add,
        Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, neg_smul, Matrix.neg_cons,
        Matrix.neg_empty, zero_smul, one_smul, EmbeddingLike.apply_eq_iff_eq]
      ring_nf
      ext i j
      fin_cases i
      · fin_cases j
        · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
          rw [mul_inv_cancel₀]
          · simp
          exact_mod_cast hα
        simp
      fin_cases j
      · simp
      simp

    rw[← hmup]

    let muMatrixInt : Matrix (Fin 2) (Fin 2) (adicCompletionIntegers F v) :=
      !![a-(Quotient.out t)*c, q*d; c*α, d]

    have intdet : muMatrixInt.det = a*d-b*c := by
      unfold muMatrixInt
      rw[Matrix.det_fin_two_of]
      rw[hq₁]
      ring_nf
      rw[mul_assoc b dinv c, mul_comm dinv c, mul_assoc, mul_assoc, dinvval]
      ring

    let val_x₁_unit : (Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v))ˣ :=
      { val := val_x₁, inv := inv_x₁, val_inv := val_inv_x₁, inv_val := inv_val_x₁ }

    have val_x₁_det_unit :
      IsUnit (val_x₁_unit : Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v)).det :=
      Matrix.isUnits_det_units val_x₁_unit

    have val_x₁_det :
      (val_x₁_unit : Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v)).det = a*d-b*c := by
      unfold val_x₁_unit a b c d
      push_cast
      apply Matrix.det_fin_two_of

    rw[val_x₁_det, ← intdet] at val_x₁_det_unit
    have muMatrixIntUnit : IsUnit muMatrixInt :=
      (Matrix.isUnit_iff_isUnit_det muMatrixInt).mpr val_x₁_det_unit

    obtain ⟨ muMatrixIntUnitval , hmuMatrixIntUnitval ⟩ := muMatrixIntUnit

    have inteq : (Units.map (RingHom.mapMatrix ((v.adicCompletionIntegers F).subtype)).toMonoidHom)
      muMatrixIntUnitval = mup := by
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
        ValuationSubring.coe_subtype]
      ext i j
      rw[m]
      unfold muMatrix
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
        ValuationSubring.coe_subtype, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one]
      rw[hmuMatrixIntUnitval]
      unfold muMatrixInt
      fin_cases i
      · fin_cases j
        · simp
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.map_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
          MulMemClass.coe_mul]
        rw[hq₁]
        ring_nf; push_cast
        rw[mul_sub_left_distrib]
        rw[mul_assoc (d : adicCompletion F v) (α : adicCompletion F v)⁻¹
          ((α : adicCompletion F v) * (q : adicCompletion F v))]
        rw[← mul_assoc (α : adicCompletion F v)⁻¹ (α : adicCompletion F v) (q : adicCompletion F v)]
        rw[inv_mul_cancel₀]
        · rw[mul_comm (d : adicCompletion F v) (α : adicCompletion F v)⁻¹]
          rw[mul_comm (b : adicCompletion F v) (dinv : adicCompletion F v)]
          rw[mul_assoc, ← mul_assoc
            (d : adicCompletion F v) (dinv : adicCompletion F v) (b : adicCompletion F v)]
          norm_cast; rw[dvalinv]
          push_cast; ring_nf
        exact_mod_cast hα
      fin_cases j
      · simp
      simp

    constructor
    · use muMatrixIntUnitval
    -- in localTameLevel
    rw[m]; unfold muMatrix
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one]
    norm_cast
    constructor
    · have valad : Valued.v ((a - d) : adicCompletion F v) < 1 := by
        have ha : a = (val_x₁ 0 0) := rfl
        have hd : d = (val_x₁ 1 1) := rfl

        rw[ha, hd]
        have va : (val_x₁ 0 0) = co₁ 0 0 := by
          apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 0 0) at y
          simp only [RingHom.toMonoidHom_eq_coe, Units.map_mk,
            MonoidHom.coe_coe, RingHom.mapMatrix_apply,
            ValuationSubring.coe_subtype, Fin.isValue, Matrix.map_apply] at y
          exact y
        have vd : (val_x₁ 1 1) = co₁ 1 1 := by
          apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 1 1) at y
          simp only [RingHom.toMonoidHom_eq_coe, Units.map_mk,
            MonoidHom.coe_coe, RingHom.mapMatrix_apply,
            ValuationSubring.coe_subtype, Fin.isValue, Matrix.map_apply] at y
          exact y
        rw[va, vd]
        apply z.left
      norm_cast at valad
      have maxad : (a-d) ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
        apply (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) (a-d)).mpr
        apply (Valuation.isEquiv_iff_val_lt_one.mp valc₁).mp
        exact valad
      rw[sub_right_comm]
      have maxadc : (a - d - Quotient.out t * c)
        ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
        apply Ideal.sub_mem
        · assumption
        apply Ideal.mul_mem_left
        assumption
      apply (Valuation.isEquiv_iff_val_lt_one.mp valc₁).mpr
      exact (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) _).mp maxadc
    have maxcα : c*α ∈ IsLocalRing.maximalIdeal ↥(adicCompletionIntegers F v) := by
      exact Ideal.mul_mem_right α (IsLocalRing.maximalIdeal ↥(adicCompletionIntegers F v)) maxc
    apply (Valuation.isEquiv_iff_val_lt_one.mp valc₁).mpr
    exact (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) (c*α)).mp maxcα
  assumption


variable {F v α hα} in
noncomputable def tadele (t : v.adicCompletion F) : (FiniteAdeleRing (𝓞 F) F) :=
    letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
    ⟨fun i ↦ if h : i = v then h ▸ t else 0, by
      apply Set.Finite.subset (Set.finite_singleton v)
      simp only [SetLike.mem_coe, Set.subset_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro w hw
      contrapose! hw
      rw [dif_neg hw]
      exact ValuationSubring.zero_mem (HeightOneSpectrum.adicCompletionIntegers F w)⟩

variable {F v α hα} in
noncomputable def tadele1 (t : v.adicCompletion F) : (FiniteAdeleRing (𝓞 F) F) :=
    letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
    ⟨fun i ↦ if h : i = v then h ▸ t else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      simp only [SetLike.mem_coe, Set.subset_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro w hw
      contrapose! hw
      rw [dif_neg hw]
      exact ValuationSubring.one_mem (HeightOneSpectrum.adicCompletionIntegers F w)⟩

variable {F v α hα} in
noncomputable def GL2toAdele (A : GL (Fin 2) (v.adicCompletion F)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := by
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  let detidele : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    FiniteAdeleRing.localUnit F A.det
  have det : !![tadele1 (A 0 0), tadele (A 0 1); tadele (A 1 0), tadele1 (A 1 1)].det
    = detidele := by
    simp only [Fin.isValue, Matrix.det_fin_two_of]
    rw[tadele, tadele, tadele1, tadele1]
    ext i
    if h : i = v then
      rw[h]; simp only [Fin.isValue, RestrictedProduct.sub_apply, RestrictedProduct.mul_apply,
        RestrictedProduct.mk_apply, ↓reduceDIte]
      unfold detidele
      rw[FiniteAdeleRing.localUnit]; simp only [Fin.isValue,
        Matrix.GeneralLinearGroup.val_det_apply, RestrictedProduct.mk_apply, ↓reduceDIte]
      rw[← Matrix.det_fin_two]
    else
      simp only [Fin.isValue, RestrictedProduct.sub_apply, RestrictedProduct.mul_apply,
        RestrictedProduct.mk_apply, ↓reduceDIte]
      unfold detidele
      rw[FiniteAdeleRing.localUnit]; simp only [Fin.isValue,
        Matrix.GeneralLinearGroup.val_det_apply, RestrictedProduct.mk_apply, ↓reduceDIte]
      rw[dif_neg (h), dif_neg (h), dif_neg (h), dif_neg (h), dif_neg (h)]
      simp
  let aInv : Invertible
    !![tadele1 (A 0 0), tadele (A 0 1); tadele (A 1 0), tadele1 (A 1 1)].det :=
  { invOf := detidele.inv,
    invOf_mul_self :=
      by rw[det]; simp,
    mul_invOf_self :=
      by rw[det]; simp }
  exact Matrix.unitOfDetInvertible
    !![tadele1 (A 0 0), tadele (A 0 1); tadele (A 1 0), tadele1 (A 1 1)]

variable {F v α hα} in
omit [IsTotallyReal F] in
lemma GL2toAdeleInv (A : GL (Fin 2) (v.adicCompletion F)) [DecidableEq (HeightOneSpectrum (𝓞 F))] :
  FiniteAdeleRing.GL2.toAdicCompletion v (GL2toAdele (A)) = A := by
  unfold FiniteAdeleRing.GL2.toAdicCompletion; simp only [RingHom.toMonoidHom_eq_coe]
  rw[GL2toAdele]
  ext i j; simp only [Fin.isValue, Units.inv_eq_val_inv, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply, RingHom.coe_coe, Matrix.map_apply]
  have r (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) [Invertible A.det] :
    (↑(A.unitOfDetInvertible) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = A := rfl
  rw[r, tadele, tadele1, tadele, tadele1]
  rw[FiniteAdeleRing.toAdicCompletion]; simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, AlgHom.coe_mk, RestrictedProduct.evalRingHom_apply]
  fin_cases i
  · fin_cases j
    · simp
    simp
  fin_cases j
  · simp
  simp


variable {F v α hα} in
noncomputable def U1_global : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
  := (GL2.TameLevel S)

variable {F v r} in
noncomputable def g_global : (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  (Matrix.GeneralLinearGroup.diagonal
    (![FiniteAdeleRing.localUnit F ⟨(α : v.adicCompletion F),
      (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1]))



variable {F v r} in
omit [IsTotallyReal F] in
lemma g_global_alt [DecidableEq (HeightOneSpectrum (𝓞 F))] :
  g_global α hα = GL2toAdele (g α hα) := by
  unfold g_global; rw[GL2toAdele, g]
  ext i j v₁
  rw[Matrix.GeneralLinearGroup.diagonal]
  push_cast
  rw[Matrix.diagonal]
  have r (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) [Invertible A.det] :
    (↑(A.unitOfDetInvertible) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = A := rfl
  rw[r, tadele, tadele1, tadele, tadele1,
    FiniteAdeleRing.localUnit, Matrix.GeneralLinearGroup.diagonal]
  simp only [Matrix.of_apply, Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, ne_eq,
    zero_ne_one, not_false_eq_true, Matrix.diagonal_apply_ne, one_ne_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Units.val_one, Matrix.cons_val']
  fin_cases i
  · fin_cases j
    · simp
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceIte,
      RestrictedProduct.zero_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, RestrictedProduct.mk_apply, right_eq_dite_iff]; intro h₁
    cases (tadele._proof_4 v₁ (Eq.mpr_prop (Eq.refl (v₁ = v)) h₁))
    rfl
  fin_cases j
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, ↓reduceIte,
    RestrictedProduct.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    RestrictedProduct.mk_apply, right_eq_dite_iff]
    intro h₁
    cases (tadele._proof_4 v₁ (Eq.mpr_prop (Eq.refl (v₁ = v)) h₁))
    rfl
  simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Units.val_one, RestrictedProduct.one_apply, RestrictedProduct.mk_apply, right_eq_dite_iff]
  intro h₁
  cases (tadele._proof_4 v₁ (Eq.mpr_prop (Eq.refl (v₁ = v)) h₁))
  rfl


set_option synthInstance.maxHeartbeats 0 in
-- double coset space
variable {F v} in
noncomputable def doubleCosets_global :
  Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ ↑(U1_global S)) :=
   (QuotientGroup.mk '' (↑(U1_global S) * (g_global α hα) • ↑(U1_global S)))


variable {F v} in
noncomputable def gt_global (t : v.adicCompletionIntegers F) :
  (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  GL2toAdele (gt α hα t)


variable {F v} in
noncomputable def singleCosetsFunction_global
  (t : ↑(adicCompletionIntegers F v) ⧸ (AddSubgroup.map (AddMonoidHom.mulLeft α)
    (⊤ : AddSubgroup ↑(adicCompletionIntegers F v)))) :
  (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ⧸ ↑(U1_global S)) := by
  let tLift : ↑(adicCompletionIntegers F v) := Quotient.out t
  exact QuotientGroup.mk (gt_global α hα tLift)

variable {F v} in
lemma U_coset_global (vbad : v ∈ S) [DecidableEq (HeightOneSpectrum (𝓞 F))] :
  Set.BijOn (singleCosetsFunction_global S α hα) ⊤ (doubleCosets_global S α hα) := by
  obtain ⟨ loc₁ , loc₂, loc₃ ⟩ := U_coset α hα
  have utoAdele (A : GL (Fin 2) (v.adicCompletion F)) :
    A ∈ ((U1v v) : Set (GL (Fin 2) (adicCompletion F v)))
      → GL2toAdele (A) ∈ ((U1_global S) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
    intro hA
    constructor
    · sorry

    sorry
  constructor
  · intro t h
    rw[singleCosetsFunction_global, doubleCosets_global ]
    let loc := loc₁ h
    rw[singleCosetsFunction] at loc
    obtain ⟨ x, ⟨ y₁, y₂ ⟩ ⟩ := loc
    use GL2toAdele x
    obtain ⟨ u1, hu1, gu2, ⟨ u2, hu2, hgu2 ⟩, u3 ⟩ := y₁
    constructor
    · constructor
      · sorry
      sorry
    rw[gt_global]

    sorry
  constructor
  · intro t₁ h₁ t₂ h₂ h
    apply loc₂
    · assumption
    · assumption
    have hc := QuotientGroup.eq.mp h
    obtain ⟨ hc₁, hc₂ ⟩ := hc
    have hc₃ := hc₂ v vbad
    simp only [map_mul, map_inv] at hc₃
    rw[gt_global, gt_global] at hc₃
    rw[GL2toAdeleInv, GL2toAdeleInv] at hc₃
    rw[← U1v] at hc₃
    have hc₄ := QuotientGroup.eq.mpr hc₃
    rw[singleCosetsFunction]; assumption

  intro co h
  obtain ⟨ co₀, ⟨ ⟨ co₁, h₁, ⟨ l, ⟨ ⟨ co₂, ⟨ h₂, z ⟩ ⟩ , hl ⟩ ⟩ ⟩ , h₀ ⟩ ⟩ := h
  have hp : co₀ = co₁ * (g_global α hα) * co₂ := by
    rw[← hl, ← z]; simp only [smul_eq_mul]; rw[mul_assoc]
  obtain ⟨ h₁x, h₁y ⟩ := h₁
  have h₁yv := h₁y v vbad
  rw[← U1v] at h₁yv
  obtain ⟨ h₂x, h₂y ⟩ := h₂
  have h₂yv := h₂y v vbad
  rw[← U1v] at h₂yv
  let co₀local : GL (Fin 2) (adicCompletion F v) :=
    (FiniteAdeleRing.GL2.toAdicCompletion v) co₁ *
      (g α hα) * (FiniteAdeleRing.GL2.toAdicCompletion v) co₂
  have hlocal : (co₀local : (GL (Fin 2) (adicCompletion F v) ⧸ U1v v)) ∈ doubleCosets α hα := by
    use (FiniteAdeleRing.GL2.toAdicCompletion v) co₁ *
      (g α hα) * (FiniteAdeleRing.GL2.toAdicCompletion v) co₂
    constructor
    · constructor
      · use (h₁y v vbad)
        use (g α hα) * (FiniteAdeleRing.GL2.toAdicCompletion v) co₂
        constructor
        · use (FiniteAdeleRing.GL2.toAdicCompletion v) co₂
          use (h₂y v vbad)
          rfl
        rw[mul_assoc]

    unfold co₀local; rfl

  obtain ⟨ t, ht ⟩ := loc₃ (hlocal)
  use t
  constructor
  · exact ht.left
  rw[← h₀]
  rw[singleCosetsFunction_global]
  apply QuotientGroup.eq.mpr

  constructor
  · intro v1
    rw[hp]
    -- use h₁x v1, h₂x v1
    sorry
  intro v1 hv1
  sorry

open scoped TensorProduct.RightActions

set_option synthInstance.maxHeartbeats 0 in
-- double coset space
variable {F D v} in
noncomputable def g_global_r : (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ :=
  (Units.map (AlgEquiv.symm r).toMulEquiv) (g_global α hα)

set_option synthInstance.maxHeartbeats 0 in
-- double coset space
set_option maxHeartbeats 0 in
-- double coset space
variable {F D v} in
noncomputable def doubleCosets_global_r :
  Set ((D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ ⧸ U1 r S) :=
    ((QuotientGroup.mk ''
      (((U1 r S) : Set (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ)
      * (g_global_r r α hα)
      • ((U1 r S) : Set (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ))))

set_option synthInstance.maxHeartbeats 0 in
-- double coset space
variable {F D v} in
noncomputable def singleCosetsFunction_global_r
  (t : ↑(adicCompletionIntegers F v) ⧸ (AddSubgroup.map (AddMonoidHom.mulLeft α)
    (⊤ : AddSubgroup ↑(adicCompletionIntegers F v)))) :
  (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ ⧸ U1 r S := by
  let tLift : ↑(adicCompletionIntegers F v) := Quotient.out t
  exact QuotientGroup.mk ((Units.map (AlgEquiv.symm r).toMulEquiv) (gt_global α hα tLift))

variable {F D v} in
lemma U_coset_global_r (vbad : v ∈ S) [DecidableEq (HeightOneSpectrum (𝓞 F))] :
  Set.BijOn (singleCosetsFunction_global_r r S α hα) ⊤ (doubleCosets_global_r r S α hα) := by
  constructor
  · sorry
  constructor
  · sorry
  sorry


end CosetComputations

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
