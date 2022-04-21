import ring_theory.tensor_product
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product
open polynomial

universe u
variables (K : Type u) [comm_ring K]

-- set_option profiler true -- time everything

@[simp] lemma assoc_symm_tmul {R : Type u} [comm_semiring R] {A : Type u} [semiring A] [algebra R A] {B : Type u} [semiring B] [algebra R B] {C : Type u} [semiring C] [algebra R C] (a : A) (b : B) (c : C) :
(algebra.tensor_product.assoc R A B C).symm (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = a ⊗ₜ[R] b ⊗ₜ[R] c :=
begin
  apply_fun (algebra.tensor_product.assoc R A B C),
  rw [assoc_tmul, alg_equiv.apply_symm_apply],
  exact (algebra.tensor_product.assoc R A B C).injective,
end

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := aeval ((X ⊗ₜ 1) + (1 ⊗ₜ X))

@[simp] lemma comul_1 : comul K (1 : K[X]) = (1 ⊗ₜ 1 : K[X] ⊗[K] K[X]) := -- elaboration of comul_1 took 4.18s
begin 
  rw alg_hom.map_one, -- ⊢ 1 = 1 ⊗ₜ[K] 1
  refl,
end

@[simp] lemma comul_X : comul K X = X ⊗ₜ 1 + 1 ⊗ₜ X := -- elaboration of comul_X took 257ms
begin 
  unfold comul,
  rw aeval_X,
end


noncomputable def map1 : K[X] →ₐ[K] K[X] ⊗ K[X] ⊗ K[X] := (algebra.tensor_product.assoc K K[X] K[X] K[X]).symm.to_alg_hom.comp ((map (alg_hom.id K K[X]) (comul K)).comp (comul K))

noncomputable def map2 : (K[X] →ₐ[K] K[X] ⊗[K] K[X] ⊗[K] K[X] ) :=  (map (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) (alg_hom.id K K[X])).comp (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X])
. -- this tells Lean not to recompile definitions


lemma coassoc : map1 K = map2 K := -- TODO this still takes 10 seconds to elaborate
begin
  ext,
  simp only [map1, map2, alg_equiv.to_alg_hom_eq_coe, alg_hom.coe_comp, alg_equiv.coe_alg_hom,
    function.comp_app, comul_X, map_tmul, alg_hom.coe_id, id.def, comul_1,
    tensor_product.tmul_add, add_assoc, assoc_symm_tmul, tensor_product.add_tmul, _root_.map_add],
  -- have P1 : map1 K X = X ⊗ₜ 1 ⊗ₜ 1 + 1 ⊗ₜ X ⊗ₜ 1 + 1 ⊗ₜ 1 ⊗ₜ X,
  --   unfold map1,
  --   simp [tensor_product.tmul_add, add_assoc],

  -- have P2 : map2 K X = X ⊗ₜ 1 ⊗ₜ 1 + 1 ⊗ₜ X ⊗ₜ 1 + 1 ⊗ₜ 1 ⊗ₜ X,
  --   unfold map2,
  --   simp only [tensor_product.add_tmul, alg_hom.coe_comp, function.comp_app, comul_X, _root_.map_add, map_tmul, alg_hom.coe_id, id.def, comul_1],
  
  -- ext,
  -- rw P1,
  -- rw P2,
end

noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0
.

lemma counit_left : (algebra.tensor_product.lid K K[X]).to_alg_hom.comp ((map (counit K) (alg_hom.id K K[X])).comp (comul K)) = (alg_hom.id K K[X]) :=
begin
  ext,
  simp only [counit, alg_equiv.to_alg_hom_eq_coe, alg_hom.coe_comp, alg_equiv.coe_alg_hom, function.comp_app, comul_X, _root_.map_add, map_tmul, coe_aeval_eq_eval, eval_X, tensor_product.zero_tmul, eval_one, zero_add, lid_tmul, one_smul],
end

lemma counit_right : (algebra.tensor_product.rid K K[X]).to_alg_hom.comp ((map (alg_hom.id K K[X]) (counit K)).comp (comul K)) = (alg_hom.id K K[X]) :=
begin
  ext,
  simp only [counit, alg_equiv.to_alg_hom_eq_coe, alg_hom.coe_comp, alg_equiv.coe_alg_hom, function.comp_app, comul_X, _root_.map_add, map_tmul, coe_aeval_eq_eval, eval_one, eval_X, tensor_product.tmul_zero, add_zero, rid_tmul, one_smul],
end

noncomputable def coinv : K[X] →ₐ[K] K[X] := aeval (-X)

-- TODO
-- lemma coinv_right : (lmul' K).comp ((map (alg_hom.id K K[X]) (coinv K)).comp (comul K)) = (algebra.of_id K K[X]).comp (counit K) :=
-- begin
--   sorry
-- end