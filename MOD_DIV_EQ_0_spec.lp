require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem196469 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (DIV (MOD m n) n) (NUMERAL _0)))))));
