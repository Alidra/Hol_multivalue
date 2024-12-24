require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El (prod hreal hreal)) ≔ (real_neg (mk_real (treal_eq x0)));
symbol term1 (x0: El (prod hreal hreal)) ≔ (mk_real (treal_eq (treal_neg x0)));
