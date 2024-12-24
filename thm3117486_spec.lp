require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3117486 (a : El num) (b : El num) : Prf ((λ b' : El num, (= (int_of_num (num_gcd ((@̦‚ num num) a b'))) (int_gcd ((@̦‚ int int) (int_of_num a) (int_of_num b'))))) b);
