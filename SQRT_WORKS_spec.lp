require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1943636 : Prf (∀ (λ x : El real, (⇒ (real_le (real_of_num (NUMERAL _0)) x) (∧ (real_le (real_of_num (NUMERAL _0)) (sqrt x)) (= (real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 _0)))) x)))));
