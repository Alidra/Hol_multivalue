require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301299 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_sub x (int_add x y)) (int_neg y))))));
