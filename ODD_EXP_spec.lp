require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem128321 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (ODD (EXP m n)) (∨ (ODD m) (= n (NUMERAL _0))))))));
