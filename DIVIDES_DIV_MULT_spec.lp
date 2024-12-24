require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3112549 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (num_divides m n) (= (* (DIV n m) m) n))))));
