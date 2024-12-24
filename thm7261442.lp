require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7261442_term_abbrevs;
require open hol-light.thm7261413_spec;
opaque symbol lem7261442 : Prf term0 ≔ λ f : El (fun num real), (@lem7261413 f);
