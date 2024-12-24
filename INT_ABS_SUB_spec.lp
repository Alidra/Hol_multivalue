require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300765 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_abs (int_sub x y)) (int_abs (int_sub y x)))))));
