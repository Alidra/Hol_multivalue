require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300126 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_lt x z) (int_lt (int_abs (int_sub y x)) (int_sub z x))) (int_lt y z))))))));
