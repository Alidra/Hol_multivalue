require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2318180 : Prf (∀ (λ x : El int, (= (int_abs x) ((@COND int) (int_le (int_of_num (NUMERAL _0)) x) x (int_neg x)))));
