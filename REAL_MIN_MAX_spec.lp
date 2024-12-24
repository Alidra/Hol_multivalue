require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1555966 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_min x y) (real_neg (real_max (real_neg x) (real_neg y))))))));
