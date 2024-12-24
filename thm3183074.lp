require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3183074_term_abbrevs;
require open hol-light.GSPEC_spec;
opaque symbol lem3183074 [A] (p : El (fun A bool)) : Prf (term0 A p) ≔ (@lem3182122 A) p;
