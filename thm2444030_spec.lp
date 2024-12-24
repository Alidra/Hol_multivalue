require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2444030 (x : El int) (y : El int) : Prf ((λ y' : El int, (= (= x y') (= (int_sub x y') (int_of_num (NUMERAL _0))))) y);
