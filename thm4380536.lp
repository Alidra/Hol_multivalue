require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4380536_term_abbrevs;
require open hol-light.thm4380490_spec;
opaque symbol lem4380531 [_105011 _105012] (f : El (type686 _105011)) : Prf (term0 _105011 _105012 f) ≔ λ t : El (fun _105012 bool), (@lem4380490 _105011 _105012 f t);
opaque symbol lem4380536 [_105011 _105012] : Prf (term1 _105011 _105012) ≔ λ f : El (type686 _105011), (@lem4380531 _105011 _105012 f);
