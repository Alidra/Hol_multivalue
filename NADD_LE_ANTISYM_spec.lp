require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1271366 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (= (∧ (nadd_le x y) (nadd_le y x)) (nadd_eq x y))))));
