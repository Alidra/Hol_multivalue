require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem80210 : Prf (∀ (λ n : El num, (= (NUMERAL (BIT1 n)) (SUC (+ (NUMERAL n) (NUMERAL n))))));
