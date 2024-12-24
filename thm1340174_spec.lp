require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1340174 : Prf (∀ (λ x : El real, (⇒ (¬ (= x (real_of_num (NUMERAL _0)))) (= (real_mul (real_inv x) x) (real_of_num (NUMERAL (BIT1 _0)))))));
