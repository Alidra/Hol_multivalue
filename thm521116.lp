require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm521116_term_abbrevs;
require open hol-light.thm82_spec;
opaque symbol lem521116 (n : El num) (m : El num) : Prf (term0 n m) ≔ (@lem82 (term1 n m));
