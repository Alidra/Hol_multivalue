require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304723 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (int_lt (int_add x z) (int_add y z)) (int_lt x y))))))));
