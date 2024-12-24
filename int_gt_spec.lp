require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2271143 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_gt x y) (real_gt (real_of_int x) (real_of_int y)))))));
