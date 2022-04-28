-- https://leanprover-community.github.io/mathlib_docs/category_theory/functor/hom.html
-- THE PLAN IS TO DEFINE AN AFFINE GROUP SCHEME AS A REPRESENTABLE FUNCTOR FROM K-ALGEBRAS TO GROUPS, AND PROVE THAT G_a := Hom(K[X], _) IS AN AFFINE GROUP SCHEME

import Hopf
import category_theory.functor.hom

variables (K : Type*) [comm_ring K]
variables (V : Type*) [comm_ring V] [algebra K V]

