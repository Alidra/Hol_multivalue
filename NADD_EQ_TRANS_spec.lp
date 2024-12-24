require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1268295 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∀ (λ z : El nadd, (⇒ (∧ (nadd_eq x y) (nadd_eq y z)) (nadd_eq x z))))))));
