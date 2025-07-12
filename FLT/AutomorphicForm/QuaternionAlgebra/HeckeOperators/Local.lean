/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper, Bryan Wang
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

-- let F be a totally real number field
variable (F : Type*) [Field F] [NumberField F]

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

namespace Local

variable (v : HeightOneSpectrum (𝓞 F))

variable (α : v.adicCompletionIntegers F)

variable (hα : α ≠ 0)

variable {F α hα} in
/-- The subgroup `U1 v = GL2.localTameLevel v`. -/
noncomputable abbrev U1 : Subgroup (GL (Fin 2) (adicCompletion F v)) := (GL2.localTameLevel v)

variable {F v} in
/-- The matrix element `g = diag[α, 1]`. -/
noncomputable abbrev g : (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1])

variable {F v} in
lemma g_def : (g α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
  = !![↑α, 0; 0, 1] := by
    rw[g]; ext i j
    rw[Matrix.GeneralLinearGroup.diagonal]
    fin_cases i; all_goals fin_cases j
    all_goals simp

variable {F v} in
/-- The double coset space `U1 g U1` as a set of left cosets. -/
noncomputable abbrev U1gU1 :
  Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (U1 v)) :=
  (QuotientGroup.mk '' ((U1 v) * {g α hα}))

variable {F v} in
/-- The unipotent matrix element `!![1, t; 0, 1]`. -/
noncomputable def GL2.unipotent (t : v.adicCompletion F) : (GL (Fin 2) (adicCompletion F v)) :=
  let htInv : Invertible !![1, t; 0, 1].det :=
  { invOf := 1,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
  Matrix.unitOfDetInvertible !![1, t; 0, 1]

variable {F v} in
/-- The matrix element `gt = !![α, t; 0, 1]`. -/
noncomputable abbrev gt (t : v.adicCompletionIntegers F) :
  (GL (Fin 2) (adicCompletion F v)) :=
  let gtInv : Invertible !![(α : v.adicCompletion F), t; 0, 1].det :=
  { invOf := (α : v.adicCompletion F)⁻¹,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of,
        mul_one, mul_zero, sub_zero]; rw [inv_mul_cancel₀]; exact_mod_cast hα,
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of,
        mul_one, mul_zero, sub_zero]; rw [mul_inv_cancel₀]; exact_mod_cast hα }
  Matrix.unitOfDetInvertible !![(α : v.adicCompletion F), t; 0, 1]

variable {F v} in
/-- For each `t ∈ O_v / αO_v`, the left coset `gt U1`
for a lift of t to `O_v`. -/
noncomputable abbrev gtU1
  (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
  ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1 v)) :=
  let tLift : ↑(adicCompletionIntegers F v) := Quotient.out t
  QuotientGroup.mk (gt α hα tLift)

set_option maxHeartbeats 600000 in
-- long explicit matrix coset computations
variable {F v} in
/-- The double coset space `U1gU1` is the disjoint union of `gtU1`
as t ranges over `O_v / αO_v`. -/
lemma U1gU1_cosetDecomposition : Set.BijOn (gtU1 α hα) ⊤ (U1gU1 α hα) := by
  have r (A : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) [Invertible A.det] :
    (↑(A.unitOfDetInvertible) : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) = A := rfl

  constructor
  · -- Show that `gtU1` is contained in `U1gU1` for all t.
    intro t h
    -- We have `gt = (GL2.unipotent t) * g`.
    have m : (gt α hα (Quotient.out t)) = GL2.unipotent ↑(Quotient.out t) * g α hα := by
        ext i j; push_cast
        rw[gt]; unfold GL2.unipotent; rw[g_def, r, r, Matrix.mul_apply]
        simp only [Fin.sum_univ_two, Fin.isValue]
        fin_cases i; all_goals fin_cases j
        all_goals simp
    rw[gtU1, m, U1gU1]
    use (GL2.unipotent ↑(Quotient.out t) * g α hα)
    constructor
    · use GL2.unipotent ↑(Quotient.out t)
      constructor
      · -- Show that `GL2.unipotent t` is in `U1`.
        unfold GL2.unipotent
        constructor
        · let htInt : ((Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v))ˣ) :=
            let htInv : Invertible !![1, (Quotient.out t); 0, 1].det :=
            { invOf := 1,
              invOf_mul_self :=
              by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
              mul_invOf_self :=
              by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
            Matrix.unitOfDetInvertible !![1, (Quotient.out t); 0, 1]
          use htInt; refine Units.eq_iff.mp ?_
          rw[Units.coe_map]; unfold htInt
          simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
            ValuationSubring.coe_subtype]
          ext i j
          fin_cases i; all_goals fin_cases j
          all_goals simp; rfl
        rw[r]; simp
      use g α hα
      simp only [Set.mem_singleton_iff, and_self]
    rfl

  constructor
  · -- Show that distinct t give distinct `gtU1`, i.e. we have a disjoint union.
    intro t₁ h₁ t₂ h₂ h
    rw[gtU1, gtU1] at h
    -- If `gtU1 t₁ = gtU1 t₂`, then `(gt t₁)⁻¹ * (gt t₂)` is in `U1 v`.
    have m : (gt α hα (Quotient.out t₁))⁻¹ * gt α hα (Quotient.out t₂)
      = GL2.unipotent ((α : v.adicCompletion F)⁻¹ *
        (( - (Quotient.out t₁) + (Quotient.out t₂)) : adicCompletion F v )) := by
        apply inv_mul_eq_iff_eq_mul.mpr
        rw [gt, gt]; unfold GL2.unipotent
        ext i j; push_cast
        rw[r, r, r, Matrix.mul_apply]
        simp only [Fin.sum_univ_two, Fin.isValue]
        fin_cases i; all_goals fin_cases j
        all_goals simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
          mul_one, mul_zero, add_zero]
        rw[← mul_assoc, mul_inv_cancel₀, one_mul]
        any_goals ring_nf
        exact (Subtype.coe_ne_coe.mpr hα)
    obtain ⟨ ⟨ x, y ⟩ , z ⟩ := m ▸ (QuotientGroup.eq.mp h)
    -- But inspecting the top-right entry of `(gt t₁)⁻¹ * (gt t₂)`
    -- gives us `t₁ = t₂`.
    apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 0 1) at y
    unfold GL2.unipotent at y; rw[r] at y
    simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype, Matrix.map_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero] at y
    conv_lhs =>
      apply Eq.symm (QuotientAddGroup.out_eq' t₁)
    conv_rhs =>
      apply Eq.symm (QuotientAddGroup.out_eq' t₂)
    apply QuotientAddGroup.eq.mpr
    apply Ideal.mem_span_singleton'.mpr
    use (x 0 1)
    apply (Subtype.coe_inj).mp; push_cast
    rw[y]; ring_nf; rw[mul_inv_cancel₀, one_mul, one_mul]
    exact (Subtype.coe_ne_coe.mpr hα)

  -- Show that each coset in `U1gU1` is of the form `gtU1` for some t.
  -- This is the more involved part.
  rintro _ ⟨ _, ⟨ ⟨ w, ⟨ ⟨ x , y ⟩ , z ⟩, ⟨ _, rfl, rfl ⟩ ⟩ , rfl ⟩ ⟩
  -- Each element of `U1gU1` can be written as
  -- `x * g`, where `x = !![a,b;c,d]`
  -- is viewed as a matrix over `O_v`.
  let a : (adicCompletionIntegers F v) := (x 0 0)
  let b : (adicCompletionIntegers F v) := (x 0 1)
  let c : (adicCompletionIntegers F v) := (x 1 0)
  let d : (adicCompletionIntegers F v) := (x 1 1)
  have h11 : c * (x.inv 0 1) + d * (x.inv 1 1) = 1 := by calc
    _ = (x 1 0) * (x.inv 0 1) + (x 1 1) * (x.inv 1 1) := rfl
    _ = (x * x.inv) 1 1 := by rw[Matrix.mul_apply]; simp
    _ = 1 := by rw[x.val_inv]; simp
  have valc : Valued.v (c : adicCompletion F v) < 1 := by
    unfold c
    apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 1 0) at y
    simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype, Matrix.map_apply] at y
    rw[y]
    apply z.right
  have maxc : c ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    apply (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) c).mpr
    apply (Valuation.isEquiv_iff_val_lt_one.mp
      (Valuation.isEquiv_valuation_valuationSubring Valued.v)).mp
    exact valc
  have maxd : d ∉ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    by_contra maxd₁
    have max1 : c * (x.inv 0 1) + d * (x.inv 1 1)
      ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
      apply Ideal.add_mem
      repeat
        apply Ideal.mul_mem_right
        assumption
    rw[h11] at max1
    exact one_notMem_nonunits ((IsLocalRing.mem_maximalIdeal 1).mp max1)
  have dunit : IsUnit d := by
    by_contra dnotunit
    exact maxd ((IsLocalRing.mem_maximalIdeal d).mpr (mem_nonunits_iff.mpr dnotunit))
  obtain ⟨ dinv, dval_inv, dinv_val ⟩ := isUnit_iff_exists.mp dunit
  /- In the above, we show that d is a unit,
  because c is a non-unit (by assumption on U).
  This is necessary because the desired t
  is `b * d⁻¹`.
  The rest of the proof is devoted to showing
  that this t works.
  This means showing that `gt⁻¹ * x * g` is in U,
  which boils down to explicit matrix computations.
  -/
  let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) := (b * dinv)
  use t
  simp only [Set.top_eq_univ, Set.mem_univ, true_and]; rw[gtU1]
  apply QuotientGroup.eq.mpr
  -- We first compute `m := gt⁻¹ * x * g` explicitly,
  -- and denote the resulting matrix by `mMatrix`.
  let m : GL (Fin 2) (adicCompletion F v) := (gt α hα (Quotient.out t))⁻¹ * w * g α hα
  let mMatrix : Matrix (Fin 2) (Fin 2) (adicCompletion F v) :=
    !![a - (Quotient.out t) * c, (α : adicCompletion F v)⁻¹ * (b - (Quotient.out t) * d);
        c * α, d]
  have hm : m = mMatrix := by
      have hp1 : (gt α hα (Quotient.out t))⁻¹
        = !![(α : adicCompletion F v)⁻¹, -(α : adicCompletion F v)⁻¹ * (Quotient.out t); 0, 1] := by
        rw[gt]; push_cast; rw[r, Matrix.inv_def]
        simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_eq_inv',
          Matrix.adjugate_fin_two_of, neg_zero, Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
          mul_neg, Matrix.smul_empty, neg_mul, EmbeddingLike.apply_eq_iff_eq]
        rw [inv_mul_cancel₀]; exact_mod_cast hα
      have hp2 : w = !![(a : adicCompletion F v), b; c, d] := by
        rw[← y]; ext i j
        simp only [RingHom.toMonoidHom_eq_coe, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_fin_one]
        fin_cases i; all_goals fin_cases j
        all_goals simp; rfl
      unfold m; push_cast; rw[hp2, g_def]; norm_cast; rw[hp1]
      unfold mMatrix
      simp only [neg_mul, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
        Matrix.head_cons, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
        Matrix.tail_cons, mul_one, Matrix.empty_vecMul, add_zero, Matrix.add_cons, zero_add,
        Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, neg_smul, Matrix.neg_cons,
        Matrix.neg_empty, zero_smul, one_smul, EmbeddingLike.apply_eq_iff_eq]
      ring_nf
      ext i j
      fin_cases i; all_goals fin_cases j
      all_goals simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Fin.mk_one, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero]
      rw [mul_inv_cancel₀, one_mul, one_mul]
      exact_mod_cast hα
  rw[← mul_assoc]; convert_to m ∈ U1 v
    -- We have `tLift = b * dinv - α * q` for some `q ∈ O_v`.
  have ht : t = b * dinv := rfl
  rw[← Ideal.Quotient.mk_out t] at ht
  obtain ⟨ q, hq ⟩ :=
    Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp ht)
  simp only at hq
  have hq₁ : Quotient.out t = b * dinv + q * α := by rw[hq]; ring
  -- First we show that `m = mMatrix` is in `GL_2(O_v)`.
  -- Note this is not a priori obvious,
  -- as even `g` itself need not be in `GL_2(O_v)`
  -- (`α` need not be a unit).
  let mMatrixInt : Matrix (Fin 2) (Fin 2) (adicCompletionIntegers F v) :=
    !![a - (Quotient.out t) * c, - q * d; c * α, d]
  have intdet : mMatrixInt.det = x.val.det := by
    unfold mMatrixInt
    rw[Matrix.det_fin_two_of, hq₁]; ring_nf
    rw[mul_assoc b dinv c, mul_comm dinv c, mul_assoc, mul_assoc, dinv_val]; ring_nf
    rw[Matrix.det_fin_two]
  obtain ⟨ mMatrixIntUnitval , hmMatrixIntUnitval ⟩ :=
    ((Matrix.isUnit_iff_isUnit_det mMatrixInt).mpr (intdet ▸ (Matrix.isUnits_det_units x)))
  have inteq : (Units.map (RingHom.mapMatrix ((v.adicCompletionIntegers F).subtype)).toMonoidHom)
    mMatrixIntUnitval = m := by
    simp only [RingHom.toMonoidHom_eq_coe]
    ext i j; rw[hm]; unfold mMatrix
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      ValuationSubring.coe_subtype, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one]
    rw[hmMatrixIntUnitval]; unfold mMatrixInt
    fin_cases i; all_goals fin_cases j
    all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw[hq₁]
    ring_nf; push_cast
    rw[left_distrib]; ring_nf
    rw[mul_inv_cancel_right₀]
    nth_rw 3 [mul_comm]
    rw[← mul_assoc, ← mul_assoc]
    norm_cast; rw[dinv_val]
    push_cast; ring_nf
    exact_mod_cast hα
  constructor
  · use mMatrixIntUnitval
  -- Next we show that `m = mMatrix` is in `GL2.localTameLevel`.
  rw[hm]; unfold mMatrix
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  norm_cast
  constructor
  · have valad : Valued.v ((a - d) : adicCompletion F v) < 1 := by
      unfold a d
      have va : (x 0 0) = w 0 0 := by
        apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 0 0) at y
        simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue] at y
        exact y
      have vd : (x 1 1) = w 1 1 := by
        apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 1 1) at y
        simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue] at y
        exact y
      rw[va, vd]
      apply z.left
    norm_cast at valad
    have maxad : (a - d) ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
      apply (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) (a-d)).mpr
      apply (Valuation.isEquiv_iff_val_lt_one.mp
        (Valuation.isEquiv_valuation_valuationSubring Valued.v)).mp
      exact valad
    rw[sub_right_comm]
    have maxadc : (a - d - Quotient.out t * c)
      ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
      apply Ideal.sub_mem
      · assumption
      apply Ideal.mul_mem_left
      assumption
    apply (Valuation.isEquiv_iff_val_lt_one.mp
      (Valuation.isEquiv_valuation_valuationSubring Valued.v)).mpr
    exact (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) _).mp maxadc
  have maxcα : c * α ∈ IsLocalRing.maximalIdeal ↥(adicCompletionIntegers F v) := by
    exact Ideal.mul_mem_right α (IsLocalRing.maximalIdeal ↥(adicCompletionIntegers F v)) maxc
  apply (Valuation.isEquiv_iff_val_lt_one.mp
    (Valuation.isEquiv_valuation_valuationSubring Valued.v)).mpr
  exact (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) (c*α)).mp maxcα

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
