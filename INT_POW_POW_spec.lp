require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308910 : Prf (∀ (λ x : El int, (∀ (λ m : El num, (∀ (λ n : El num, (= (int_pow (int_pow x m) n) (int_pow x (* m n)))))))));
