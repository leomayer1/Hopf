import ring_theory.tensor_product
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product
open polynomial

universe u
variables (K : Type u) [comm_semiring K]

@[simp] lemma assoc_symm_tmul {R : Type u} [comm_semiring R] {A : Type u} [semiring A] [algebra R A] {B : Type u} [semiring B] [algebra R B] {C : Type u} [semiring C] [algebra R C] (a : A) (b : B) (c : C) :
(algebra.tensor_product.assoc R A B C).symm (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = a ⊗ₜ[R] b ⊗ₜ[R] c :=
begin
  apply_fun (algebra.tensor_product.assoc R A B C),
  rw assoc_tmul,
  rw alg_equiv.apply_symm_apply (algebra.tensor_product.assoc R A B C) (a ⊗ₜ[R] (b ⊗ₜ[R] c)),
  simp,
  unfold function.injective,
  intros a b h,
  exact h,
end

-- noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := aeval ((X ⊗ₜ 1) + (1 ⊗ₜ X))

@[simp] lemma comul_1 : comul K (1 : K[X]) = (1 ⊗ₜ 1 : K[X] ⊗[K] K[X]) := 
begin 
  rw alg_hom.map_one (comul K), -- ⊢ 1 = 1 ⊗ₜ[K] 1
  refl,
end

@[simp] lemma comul_X : comul K X = X ⊗ₜ 1 + 1 ⊗ₜ X := 
begin 
  unfold comul,
  rw aeval_X,
end


noncomputable def map1 : K[X] →ₐ[K] K[X] ⊗ K[X] ⊗ K[X] := (algebra.tensor_product.assoc K K[X] K[X] K[X]).symm.to_alg_hom.comp ((map (alg_hom.id K K[X]) (comul K)).comp (comul K))

noncomputable def map2 : (K[X] →ₐ[K] K[X] ⊗[K] K[X] ⊗[K] K[X] ) :=  (map (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) (alg_hom.id K K[X])).comp (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X])
. -- this tells Lean not to recompile definitions


lemma coassoc : map1 K = map2 K :=
begin
  have P1 : map1 K X = X ⊗ₜ 1 ⊗ₜ 1 + 1 ⊗ₜ X ⊗ₜ 1 + 1 ⊗ₜ 1 ⊗ₜ X,
    unfold map1,
    simp [tensor_product.tmul_add, add_assoc],

  have P2 : map2 K X = X ⊗ₜ 1 ⊗ₜ 1 + 1 ⊗ₜ X ⊗ₜ 1 + 1 ⊗ₜ 1 ⊗ₜ X,
    unfold map2,
    simp only [tensor_product.add_tmul, alg_hom.coe_comp, function.comp_app, comul_X, _root_.map_add, map_tmul, alg_hom.coe_id, id.def, comul_1],
  
  ext,
  rw P1,
  rw P2,
end