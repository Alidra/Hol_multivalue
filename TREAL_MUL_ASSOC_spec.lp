require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1329092 : Prf (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (∀ (λ z : El (prod hreal hreal), (treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z))))))));
