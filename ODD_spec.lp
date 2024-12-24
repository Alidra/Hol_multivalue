require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem124619 : Prf (∧ (= (ODD (NUMERAL _0)) F) (∀ (λ n : El num, (= (ODD (SUC n)) (¬ (ODD n))))));
