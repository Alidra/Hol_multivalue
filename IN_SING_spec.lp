require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3205876 [A] : Prf (∀ (λ x : El A, (∀ (λ y : El A, (= ((@IN A) x ((@INSERT A) y (@EMPTY A))) (= x y))))));
