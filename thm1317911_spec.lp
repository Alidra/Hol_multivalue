require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1317911 (x : El nadd) (y : El nadd) : Prf (= (= (hreal_add (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y))) (mk_hreal (nadd_eq (nadd_add x y)))) (= (mk_hreal (nadd_eq (nadd_add x y))) (hreal_add (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y)))));
