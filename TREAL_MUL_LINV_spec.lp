require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1332639 : Prf (∀ (λ x : El (prod hreal hreal), (⇒ (¬ (treal_eq x (treal_of_num (NUMERAL _0)))) (treal_eq (treal_mul (treal_inv x) x) (treal_of_num (NUMERAL (BIT1 _0)))))));
