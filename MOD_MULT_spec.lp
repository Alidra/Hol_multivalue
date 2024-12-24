require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem170526 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (MOD (* m n) m) (NUMERAL _0))))));
