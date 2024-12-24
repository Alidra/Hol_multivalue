require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3112385 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (num_divides m n) (= (MOD n m) (NUMERAL _0)))))));
