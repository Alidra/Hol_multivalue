require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1640492 : Prf (∀ (λ x : El real, (∀ (λ m : El num, (∀ (λ n : El num, (= (real_pow (real_pow x m) n) (real_pow x (* m n)))))))));
