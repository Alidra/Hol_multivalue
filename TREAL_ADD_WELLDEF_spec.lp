require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1333561 : Prf (∀ (λ x1 : El (prod hreal hreal), (∀ (λ x2 : El (prod hreal hreal), (∀ (λ y1 : El (prod hreal hreal), (∀ (λ y2 : El (prod hreal hreal), (⇒ (∧ (treal_eq x1 x2) (treal_eq y1 y2)) (treal_eq (treal_add x1 y1) (treal_add x2 y2)))))))))));
