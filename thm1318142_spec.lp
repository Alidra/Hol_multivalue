require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1318142 (x : El nadd) (y : El nadd) : Prf (= (hreal_le (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y))) (nadd_le x y));
