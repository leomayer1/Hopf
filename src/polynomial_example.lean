import Hopf
import ring_theory.tensor_product
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product
open polynomial

-- TODO variables {K : Type*} [comm_ring K]
-- notation `K` := ℚ
variables (K : Type*) [comm_ring K]

set_option profiler true -- time everything

-- noncomputable def comm_ring.comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := aeval ((X ⊗ₜ 1) + (1 ⊗ₜ X))
noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := aeval ((X ⊗ₜ 1) + (1 ⊗ₜ X))

@[simp] lemma comul_1 : comul K (1 : K[X]) = (1 ⊗ₜ 1 : K[X] ⊗[K] K[X]) :=
begin 
  rw alg_hom.map_one, -- ⊢ 1 = 1 ⊗ₜ[K] 1
  refl,
end

@[simp] lemma comul_X : comul K X = X ⊗ₜ 1 + 1 ⊗ₜ X :=
begin 
  unfold comul,
  rw aeval_X,
end

local notation `V` := K[X]

-- TODO make this a linear equality to make it faster?
-- TODO convert to dot notation
lemma coassoc :  (algebra.tensor_product.assoc K K[X] K[X] K[X]).to_alg_hom.comp ((map (comul K) (alg_hom.id K K[X])).comp (comul K)) = (map (alg_hom.id K K[X]) (comul K)).comp (comul K) :=
begin
  ext,
  simp only [alg_hom.coe_comp, alg_hom.coe_comp, alg_hom.coe_comp, 
      function.comp_app, function.comp_app, function.comp_app, 
      comul_X K, 
      alg_hom.map_add, alg_hom.map_add, alg_hom.map_add, 
      map_tmul, map_tmul, map_tmul, map_tmul, 
      comul_X K, comul_1 K, 
      alg_hom.coe_id, id.def, id.def, 
      tensor_product.tmul_add, tensor_product.add_tmul, 
      alg_hom.map_add, 
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, 
      algebra.tensor_product.assoc_tmul, algebra.tensor_product.assoc_tmul, algebra.tensor_product.assoc_tmul],
  refl,
end

noncomputable def counit : K[X] →ₐ[K] K := aeval 0

@[simp] lemma counit_X : counit K X = 0 :=
begin
  unfold counit,
  rw [coe_aeval_eq_eval, eval_X],
end

@[simp] lemma counit_1 : counit K 1 = 1 :=
begin
  rw alg_hom.map_one, 
end

.
-- TODO why do we get .coeff n after ext?
lemma counit_left : (algebra.tensor_product.lid K K[X]).to_alg_hom.comp ((map (counit K) (alg_hom.id K K[X])).comp (comul K)) = (alg_hom.id K K[X]) :=
begin
  ext,
  rw [alg_hom.coe_comp, alg_hom.coe_comp, 
      function.comp_app, function.comp_app,
      comul_X K, 
      alg_hom.map_add,
      map_tmul, map_tmul,
      counit_X K, counit_1 K, 
      alg_hom.coe_id, id.def, id.def, 
      alg_hom.map_add, 
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, 
      lid_tmul, lid_tmul,
      one_smul, zero_smul, zero_add],
end

lemma counit_right : (algebra.tensor_product.rid K K[X]).to_alg_hom.comp ((map (alg_hom.id K K[X]) (counit K)).comp (comul K)) = (alg_hom.id K K[X]) :=
begin
  ext,
  rw [alg_hom.coe_comp, alg_hom.coe_comp, 
      function.comp_app, function.comp_app,
      comul_X K, 
      alg_hom.map_add,
      map_tmul, map_tmul,
      counit_X K, counit_1 K, 
      alg_hom.coe_id, id.def, id.def, 
      alg_hom.map_add, 
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, 
      rid_tmul, rid_tmul,
      one_smul, zero_smul, add_zero],
end

noncomputable def coinv : K[X] →ₐ[K] K[X] := aeval (-X)

@[simp] lemma coinv_X : coinv K X = -X :=
begin
  unfold coinv,
  rw aeval_X,
end

@[simp] lemma coinv_1 : coinv K 1 = 1 :=
begin
  rw alg_hom.map_one,
end

lemma coinv_right : (lmul' K).comp ((map (alg_hom.id K K[X]) (coinv K)).comp (comul K)) = (algebra.of_id K K[X]).comp (counit K) :=
begin
  ext,
  rw [alg_hom.coe_comp, alg_hom.coe_comp, alg_hom.coe_comp, 
      function.comp_app, function.comp_app, function.comp_app, 
      comul_X K, 
      alg_hom.map_add,
      map_tmul, map_tmul,
      counit_X K, coinv_X K, coinv_1 K, 
      alg_hom.coe_id, id.def, id.def, 
      alg_hom.map_add, 
      lmul'_apply_tmul, lmul'_apply_tmul,
      _root_.mul_one, _root_.one_mul, add_right_neg, _root_.map_zero],
end

lemma coinv_left : (lmul' K).comp ((map (coinv K) (alg_hom.id K K[X])).comp (comul K) )= (algebra.of_id K K[X]).comp (counit K) :=
begin
  ext,
  rw [alg_hom.coe_comp, alg_hom.coe_comp, alg_hom.coe_comp, 
      function.comp_app, function.comp_app, function.comp_app, 
      comul_X K, 
      alg_hom.map_add,
      map_tmul, map_tmul,
      counit_X K, coinv_X K, coinv_1 K, 
      alg_hom.coe_id, id.def, id.def, 
      alg_hom.map_add, 
      lmul'_apply_tmul, lmul'_apply_tmul,
      _root_.mul_one, _root_.one_mul, add_left_neg, _root_.map_zero],
end
.

set_option profiler true -- time everything

#check hopf_algebra.mk

-- TODO figure out how to make an instance of a structure as opposed to a class
noncomputable def polynomial_hopf : hopf_algebra K K[X] := { -- no timeout!
  comul := comul K,
  counit := counit K,
  coinv := coinv K,
  coassoc := begin 
    have := coassoc K,
    exact this,
  end,
  counit_left := counit_left K,
  counit_right := counit_right K,
  coinv_right := coinv_right K,
  coinv_left := coinv_left K,
}

-- noncomputable instance polynomial_hopf' : hopf_algebra K K[X] := { -- TIMEOUT!
--   comul := comul K,
--   counit := counit K,
--   coinv := coinv K,
--   coassoc := by exact coassoc K,
--   counit_left := counit_left K,
--   counit_right := counit_right K,
--   coinv_right := coinv_right K,
--   coinv_left := coinv_left K,
-- }

-- noncomputable instance polynomial_hopf : hopf_algebra K K[X] := { -- No timeout!
--   comul := comul K,
--   counit := counit K,
--   coinv := coinv K,
--   coassoc := sorry,
--   counit_left := counit_left K,
--   counit_right := counit_right K,
--   coinv_right := coinv_right K,
--   coinv_left := coinv_left K,
-- }