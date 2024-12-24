require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301974 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (= (int_sub x y) z) (= x (int_add z y)))))))));
