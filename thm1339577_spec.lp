require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1339577 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_le x y) (real_le y z)) (real_le x z))))))));
