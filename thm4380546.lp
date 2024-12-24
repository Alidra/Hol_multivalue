require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4380546_term_abbrevs;
require open hol-light.thm4380502_spec;
opaque symbol lem4380541 [_104960 _104961] (s : El (fun _104960 bool)) : Prf (term0 _104960 _104961 s) ≔ λ f : El (type686 _104961), (@lem4380502 _104960 _104961 f s);
opaque symbol lem4380546 [_104960 _104961] : Prf (term1 _104960 _104961) ≔ λ s : El (fun _104960 bool), (@lem4380541 _104960 _104961 s);
