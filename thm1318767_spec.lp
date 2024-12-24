require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318767 (x : El nadd) (y : El nadd) : Prf (= ((λ y' : El nadd, (= (nadd_eq x y') (= (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y'))))) y) (= (nadd_eq x y) (= (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y)))));
