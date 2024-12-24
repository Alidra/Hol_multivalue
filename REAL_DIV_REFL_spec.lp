require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1593003 : Prf (∀ (λ x : El real, (⇒ (¬ (= x (real_of_num (NUMERAL _0)))) (= (real_div x x) (real_of_num (NUMERAL (BIT1 _0)))))));
