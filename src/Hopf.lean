import ring_theory.tensor_product
import algebra.monoid_algebra.basic
import data.polynomial.algebra_map

open_locale tensor_product

open algebra.tensor_product

variables (K : Type) [field K]
variables (V : Type) [semiring V] [algebra K V]

structure hopf_algebra :=
(comul : V →ₐ[K] V ⊗[K] V)
(counit : V →ₐ[K] K)
(coassoc : (tensor_product.assoc K V V V) ∘ (map comul (alg_hom.id K V)) ∘ comul = map (alg_hom.id K V) comul ∘ comul)
(counit_left : (tensor_product.lid K V) ∘ (map counit (alg_hom.id K V)) ∘ comul = (alg_hom.id K V))
(counit_right : (tensor_product.rid K V) ∘ (map (alg_hom.id K V) counit) ∘ comul = (alg_hom.id K V))
(coinv : V →ₗ[K] V)
--(coinv_right : mul ∘ (map id coinv) ∘ comul = unit ∘ counit)
--(coinv_left : mul ∘ (map coinv id) ∘ comul = unit ∘ counit)

notation K`[X]`:9000 := polynomial K

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := polynomial.aeval ((polynomial.X ⊗ₜ 1) + (1 ⊗ₜ polynomial.X))

notation `Δ` :9000 := comul

noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0

-- noncomputable lemma coassoc : (tensor_product.assoc K K[X] K[X] K[X]) ∘ (map (Δ K) (alg_hom.id K K[X])) ∘ (Δ K) = (map (alg_hom.id K K[X]) (Δ K)) ∘ (Δ K)) := sorry
-- begin
--   sorry
-- end

