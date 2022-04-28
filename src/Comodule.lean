import Hopf

variables (K : Type) [field K]
variables (A : Type) [comm_ring A] [algebra K A] [hopf_algebra K A]
variables (M : Type) [add_comm_group M] [module K M]

open_locale tensor_product
open tensor_product
open hopf_algebra
open alg_hom

set_option profiler true

structure comodule :=
(coact : M →ₗ[K] M ⊗[K] A)
(coassoc : (tensor_product.assoc K M A A) ∘ (map coact linear_map.id) ∘ coact =
          (map linear_map.id (to_linear_map comul)) ∘ coact)
(counit' : (tensor_product.rid K M) ∘ (map (linear_map.id) (to_linear_map counit)) ∘ coact = id)
.

def comod_of_id : comodule K A A :=
{ coact := to_linear_map comul,
  coassoc := coassoc,
  counit' := counit_right}