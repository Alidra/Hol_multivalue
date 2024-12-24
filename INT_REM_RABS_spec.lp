require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2520091 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (rem x (int_abs y)) (rem x y))))));
