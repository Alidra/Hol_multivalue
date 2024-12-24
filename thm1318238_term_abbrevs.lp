require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El nadd) ≔ (hreal_inv (mk_hreal (nadd_eq x0)));
symbol term1 (x0: El nadd) ≔ (mk_hreal (nadd_eq (nadd_inv x0)));
