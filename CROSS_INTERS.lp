require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.CROSS_INTERS_term_abbrevs;
require open hol-light.thm4380536_spec;
require open hol-light.thm4380546_spec;
opaque symbol lem4380559 [_104960 _104961 _105011 _105012] : Prf (term0 _104960 _104961 _105011 _105012) ≔ ∧ᵢ (@lem4380546 _104960 _104961) (@lem4380536 _105011 _105012);
