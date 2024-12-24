require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2270452 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_ge x y) (real_ge (real_of_int x) (real_of_int y)))))));
