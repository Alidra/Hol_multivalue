require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2323496 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_max x y) ((@COND int) (int_le x y) y x))))));
