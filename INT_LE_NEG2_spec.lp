require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302944 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_le (int_neg x) (int_neg y)) (int_le y x))))));
