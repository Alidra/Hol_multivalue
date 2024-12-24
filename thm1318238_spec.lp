require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318238 (x : El nadd) : Prf (= (= (hreal_inv (mk_hreal (nadd_eq x))) (mk_hreal (nadd_eq (nadd_inv x)))) (= (mk_hreal (nadd_eq (nadd_inv x))) (hreal_inv (mk_hreal (nadd_eq x)))));
