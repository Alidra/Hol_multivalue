require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1262760_term_abbrevs;
opaque symbol lem1262760 (r : El (fun num num)) : Prf (= (is_nadd r) (= (term0 r) r)) ≔ @axiom_20 r;
