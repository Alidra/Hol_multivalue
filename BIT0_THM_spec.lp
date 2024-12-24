require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem80165 : Prf (∀ (λ n : El num, (= (NUMERAL (BIT0 n)) (+ (NUMERAL n) (NUMERAL n)))));
