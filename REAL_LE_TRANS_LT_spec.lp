require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1995414 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_le x y) (∀ (λ z : El real, (⇒ (real_lt y z) (real_lt x z)))))))));
