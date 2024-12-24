require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2286307 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_mul x y) (int_of_real (real_mul (real_of_int x) (real_of_int y))))))));
