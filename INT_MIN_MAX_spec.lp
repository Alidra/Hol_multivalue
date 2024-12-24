require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305733 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_min x y) (int_neg (int_max (int_neg x) (int_neg y))))))));
