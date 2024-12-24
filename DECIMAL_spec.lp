require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1977711 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (= (DECIMAL x y) (real_div (real_of_num x) (real_of_num y)))))));
