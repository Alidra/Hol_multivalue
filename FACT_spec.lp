require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem146110 : Prf (∧ (= (FACT (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ (λ n : El num, (= (FACT (SUC n)) (* (SUC n) (FACT n))))));
