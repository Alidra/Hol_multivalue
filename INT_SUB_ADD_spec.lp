require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2310126 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_add (int_sub x y) y) x)))));
