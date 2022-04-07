import linear_algebra.tensor_product
import algebra.monoid_algebra.basic

open_locale tensor_product

section hopf_alg

open tensor_product
open linear_map

variables (K : Type) [field K]
variables (V : Type) [add_comm_group V] [module K V]


namespace Hopf
/- A coalgebra class, i.e a vector space with maps which look like the algebra maps,
  but with arrows flipped.
  Maybe it would be nicer to make classes for has_comul, has_counit, has_coassoc, etc.
-/
class coalgebra :=
(comul : V →ₗ[K] V ⊗[K] V)
(counit : V →ₗ[K] K)
(coassoc : (tensor_product.assoc K V V V) ∘ (map comul id) ∘ comul = map id comul ∘ comul)
(counit_left : (tensor_product.lid K V) ∘ (map counit id) ∘ comul = id)
(counit_right : (tensor_product.rid K V) ∘ (map id counit) ∘ comul = id)

class algebra :=
(mul : V ⊗[K] V →ₗ[K] V)
(unit : K →ₗ[K] V)
(assoc : mul ∘ (map mul id) = mul ∘ (map id mul) ∘ tensor_product.assoc K V V V)
(unit_left : mul ∘ (map unit id) = (tensor_product.lid K V))
(unit_right : mul ∘ (map id unit) = (tensor_product.rid K V))

class bialgebra extends algebra K V, coalgebra K V

class hopf_algebra extends bialgebra K V :=
(coinv : V →ₗ[K] V)
(coinv_right : mul ∘ (map id coinv) ∘ comul = unit ∘ counit)
(coinv_left : mul ∘ (map coinv id) ∘ comul = unit ∘ counit)

/- Group ring of an abelian group is actually a hopf algebra? -/
end Hopf
end hopf_alg
