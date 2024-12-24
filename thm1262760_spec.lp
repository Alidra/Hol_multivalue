require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1262760 (r : El (fun num num)) : Prf (= (is_nadd r) (= (dest_nadd (mk_nadd r)) r));
