require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1276037 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (⇒ (nadd_le x y) (∃ (λ d : El nadd, (nadd_eq y (nadd_add x d)))))))));
