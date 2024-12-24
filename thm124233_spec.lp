require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem124233 : Prf (∧ (= (EVEN (NUMERAL _0)) T) (∀ (λ n : El num, (= (EVEN (SUC n)) (¬ (EVEN n))))));
