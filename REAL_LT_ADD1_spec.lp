require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1504643 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (real_le x y) (real_lt x (real_add y (real_of_num (NUMERAL (BIT1 _0))))))))));
