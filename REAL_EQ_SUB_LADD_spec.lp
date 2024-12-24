require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1521519 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (= x (real_sub y z)) (= (real_add x z) y))))))));
