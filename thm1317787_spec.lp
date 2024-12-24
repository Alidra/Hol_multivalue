require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1317787 (m : El num) : Prf (= (= (hreal_of_num m) (mk_hreal (nadd_eq (nadd_of_num m)))) (= (mk_hreal (nadd_eq (nadd_of_num m))) (hreal_of_num m)));
