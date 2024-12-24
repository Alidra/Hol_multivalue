require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem102215 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (< (NUMERAL _0) (* m n)) (∧ (< (NUMERAL _0) m) (< (NUMERAL _0) n)))))));
