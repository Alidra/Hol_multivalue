require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1270569 : Prf (∀ (λ x : El nadd, (∀ (λ x' : El nadd, (∀ (λ y : El nadd, (∀ (λ y' : El nadd, (⇒ (∧ (nadd_eq x x') (nadd_eq y y')) (= (nadd_le x y) (nadd_le x' y')))))))))));
