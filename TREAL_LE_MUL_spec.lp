require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1331691 : Prf (∀ (λ x : El (prod hreal hreal), (∀ (λ y : El (prod hreal hreal), (⇒ (∧ (treal_le (treal_of_num (NUMERAL _0)) x) (treal_le (treal_of_num (NUMERAL _0)) y)) (treal_le (treal_of_num (NUMERAL _0)) (treal_mul x y)))))));
