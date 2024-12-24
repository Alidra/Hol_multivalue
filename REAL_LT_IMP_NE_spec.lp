require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1509403 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (real_lt x y) (¬ (= x y)))))));
