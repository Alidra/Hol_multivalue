require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1270880 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∀ (λ z : El nadd, (⇒ (∧ (nadd_le x y) (nadd_le y z)) (nadd_le x z))))))));
