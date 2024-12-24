require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem76380 : Prf (∧ (= (BIT0 (NUMERAL _0)) (NUMERAL _0)) (∀ (λ n : El num, (= (BIT0 (SUC n)) (SUC (SUC (BIT0 n)))))));
