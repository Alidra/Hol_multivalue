require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1821194 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (= (real_sgn x) (real_sgn y)) (∨ (= x y) (real_lt (real_abs (real_sub x y)) (real_max (real_abs x) (real_abs y)))))))));
