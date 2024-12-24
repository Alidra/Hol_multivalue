require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem76132 : Prf (∀ (λ m : El num, (∨ (= m (NUMERAL _0)) (∃ (λ n : El num, (= m (SUC n)))))));
