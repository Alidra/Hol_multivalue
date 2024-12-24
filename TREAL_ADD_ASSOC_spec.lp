require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1328039 : Prf (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (∀ (λ z : El (prod hreal hreal), (treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z))))))));
