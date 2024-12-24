require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1330142 : Prf (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (= (∧ (treal_le x y) (treal_le y x)) (treal_eq x y))))));
