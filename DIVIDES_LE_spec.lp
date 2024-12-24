require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3082292 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (num_divides m n) (∨ (<= m n) (= n (NUMERAL _0))))))));
