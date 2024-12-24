require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2267738 : Prf (∧ (∀ (λ a : El int, (= (int_of_real (real_of_int a)) a))) (∀ (λ r : El real, (= (integer r) (= (real_of_int (int_of_real r)) r)))));
