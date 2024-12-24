require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070937 (x : El int) (h1 : Prf (int_le (int_of_num (NUMERAL _0)) x)) : Prf (= (int_of_num (num_of_int x)) x);
