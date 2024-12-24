require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9442 [A] : Prf (∀ (λ x : El A, (= ((@ε A) (λ y : El A, (= y x))) x)));
