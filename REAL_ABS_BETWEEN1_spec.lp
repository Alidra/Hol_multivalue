require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1541398 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_lt x z) (real_lt (real_abs (real_sub y x)) (real_sub z x))) (real_lt y z))))))));
