require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3117493 (a : El num) (b : El num) : Prf (= ((λ b' : El num, (= (num_coprime ((@̦‚ num num) a b')) (int_coprime ((@̦‚ int int) (int_of_num a) (int_of_num b'))))) b) (= (num_coprime ((@̦‚ num num) a b)) (int_coprime ((@̦‚ int int) (int_of_num a) (int_of_num b)))));
