import ring_theory.tensor_product

open_locale tensor_product
open algebra.tensor_product

variables (K : Type*) [comm_ring K]
variables (A : Type*) [comm_ring A] [algebra K A]

/- A big structure. There's a lot of uglinesshere...
  So much of the text here is making natural isomorphisms explicit...
  `tensor_product.assoc K A A A` is associativiy of tensor product,
  `map` is taking the tensor product of two algebra maps
  `alg_hom.id` is the identity, as an algebra map
  `tensor_product.lid` is saying that K is a left identity for K algebras under tensoring
  `algebra.of_id` is the structure morphism K →ₐ[K] A
  Should I add notation for these? Is there a way to have lean automatically do these?
-/
class hopf_algebra :=
(comul : A →ₐ[K] A ⊗[K] A)
(counit : A →ₐ[K] K)
(coinv : A →ₐ[K] A)
(coassoc : (algebra.tensor_product.assoc K A A A).to_alg_hom.comp ((map comul (alg_hom.id K A)).comp comul) = (map (alg_hom.id K A) comul).comp comul)
(counit_left : (algebra.tensor_product.lid K A).to_alg_hom.comp ((map counit (alg_hom.id K A)).comp comul) = (alg_hom.id K A))
(counit_right : (algebra.tensor_product.rid K A).to_alg_hom.comp ((map (alg_hom.id K A) counit).comp comul) = (alg_hom.id K A))
(coinv_right : (lmul' K).comp ((map (alg_hom.id K A) coinv).comp comul) = (algebra.of_id K A).comp counit)
(coinv_left : (lmul' K).comp ((map coinv (alg_hom.id K A)).comp comul) = (algebra.of_id K A).comp counit)
.
