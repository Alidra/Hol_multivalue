require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1317729 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (⇒ (nadd_eq x y) (nadd_eq (nadd_inv x) (nadd_inv y)))))));
