require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1329890 : Prf (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (∀ (λ z : El (prod hreal hreal), (treal_eq (treal_mul x (treal_add y z)) (treal_add (treal_mul x y) (treal_mul x z)))))))));
