require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2309505 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_sgn x) (int_sgn y)) (∨ (= x y) (int_lt (int_abs (int_sub x y)) (int_max (int_abs x) (int_abs y)))))))));
