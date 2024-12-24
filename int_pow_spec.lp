require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2294056 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (= (int_pow x n) (int_of_real (real_pow (real_of_int x) n)))))));
