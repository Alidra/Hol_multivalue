require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1260600 : Prf (∀ (λ A : El num, (∀ (λ B : El num, (= (∀ (λ n : El num, (<= (* A n) B))) (= A (NUMERAL _0)))))));
