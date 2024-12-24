require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1526444 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (real_mul x (real_sub y z)) (real_sub (real_mul x y) (real_mul x z)))))))));
