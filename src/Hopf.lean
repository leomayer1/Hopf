import ring_theory.tensor_product

open_locale tensor_product
open algebra.tensor_product

variables (K : Type*) [comm_ring K]
variables (V : Type*) [comm_ring V] [algebra K V]

/- A big structure. There's a lot of uglinesshere...
  So much of the text here is making natural isomorphisms explicit...
  `tensor_product.assoc K V V V` is associativiy of tensor product,
  `map` is taking the tensor product of two algebra maps
  `alg_hom.id` is the identity, as an algebra map
  `tensor_product.lid` is saying that K is a left identity for K algebras under tensoring
  `algebra.of_id` is the structure morphism K →ₐ[K] V
  Should I add notation for these? Is there a way to have lean automatically do these?
-/
class hopf_algebra :=
(comul : V →ₐ[K] V ⊗[K] V)
(counit : V →ₐ[K] K)
(coinv : V →ₐ[K] V)
(coassoc : (algebra.tensor_product.assoc K V V V).to_alg_hom.comp ((map comul (alg_hom.id K V)).comp comul) = (map (alg_hom.id K V) comul).comp comul)
(counit_left : (algebra.tensor_product.lid K V).to_alg_hom.comp ((map counit (alg_hom.id K V)).comp comul) = (alg_hom.id K V))
(counit_right : (algebra.tensor_product.rid K V).to_alg_hom.comp ((map (alg_hom.id K V) counit).comp comul) = (alg_hom.id K V))
(coinv_right : (lmul' K).comp ((map (alg_hom.id K V) coinv).comp comul) = (algebra.of_id K V).comp counit)
(coinv_left : (lmul' K).comp ((map coinv (alg_hom.id K V)).comp comul) = (algebra.of_id K V).comp counit)
.
#check hopf_algebra