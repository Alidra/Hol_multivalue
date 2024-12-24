require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem403 [A] : Prf (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ z : El A, (⇒ (∧ (= x y) (= y z)) (= x z))))))));
