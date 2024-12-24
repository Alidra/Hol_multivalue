require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem182041 : Prf (∧ (∀ (λ n : El num, (= (DIV n (NUMERAL (BIT1 _0))) n))) (∀ (λ n : El num, (= (MOD n (NUMERAL (BIT1 _0))) (NUMERAL _0)))));
