require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem100773 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (< n (+ m n)) (< (NUMERAL _0) m))))));
