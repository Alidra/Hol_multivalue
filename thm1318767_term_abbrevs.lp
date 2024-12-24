require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El nadd) (x1: El nadd) ≔ ((λ y0 : El nadd, (= (nadd_eq x0 y0) (= (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq y0))))) x1);
symbol term1 (x0: El nadd) ≔ (mk_hreal (nadd_eq x0));
