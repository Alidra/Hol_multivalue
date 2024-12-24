require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1334047 : Prf (∀ (λ x1 : El (prod hreal hreal), (∀ (λ x2 : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (⇒ (treal_eq x1 x2) (treal_eq (treal_mul x1 y) (treal_mul x2 y)))))))));
