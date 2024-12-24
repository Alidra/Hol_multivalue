require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1320494 : Prf (∀ (λ x : El hreal, (∀ (λ y : El hreal, (∀ (λ z : El hreal, (⇒ (= (hreal_add x y) (hreal_add x z)) (= y z))))))));
