require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1321192 : Prf (∀ (λ x : El hreal, (⇒ (¬ (= x (hreal_of_num (NUMERAL _0)))) (= (hreal_mul (hreal_inv x) x) (hreal_of_num (NUMERAL (BIT1 _0)))))));
