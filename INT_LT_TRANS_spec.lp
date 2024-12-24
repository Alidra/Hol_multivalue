require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305090 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_lt x y) (int_lt y z)) (int_lt x z))))))));
