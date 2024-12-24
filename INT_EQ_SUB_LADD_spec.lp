require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301939 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (= x (int_sub y z)) (= (int_add x z) y))))))));
