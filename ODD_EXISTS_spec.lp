require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem128894 : Prf (∀ (λ n : El num, (= (ODD n) (∃ (λ m : El num, (= n (SUC (* (NUMERAL (BIT0 (BIT1 _0))) m))))))));
