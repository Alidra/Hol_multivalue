require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3112686 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (¬ (= n (NUMERAL _0))) (num_divides m n)) (= (DIV n (DIV n m)) m))))));
