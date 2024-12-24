require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1531896 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (real_lt (real_add (real_abs x) (real_abs (real_sub y x))) z) (real_lt (real_abs y) z))))))));
