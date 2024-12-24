require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem126297 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (EVEN (EXP m n)) (∧ (EVEN m) (¬ (= n (NUMERAL _0)))))))));
