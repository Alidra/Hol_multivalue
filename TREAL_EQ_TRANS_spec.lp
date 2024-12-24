require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1326778 : Prf (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (∀ (λ z : El (prod hreal hreal), (⇒ (∧ (treal_eq x y) (treal_eq y z)) (treal_eq x z))))))));
