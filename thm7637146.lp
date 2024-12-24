require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7637146_term_abbrevs;
require open hol-light.DIMINDEX_UNIV_spec;
opaque symbol lem7637146 [A] (s : El (fun A bool)) : Prf (term0 A s) ≔ (@lem7594688 A) s;
