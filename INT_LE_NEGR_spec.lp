require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302998 : Prf (∀ (λ x : El int, (= (int_le x (int_neg x)) (int_le x (int_of_num (NUMERAL _0))))));
