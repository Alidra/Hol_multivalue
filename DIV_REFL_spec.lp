require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem210692 : Prf (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (DIV n n) (NUMERAL (BIT1 _0))))));
