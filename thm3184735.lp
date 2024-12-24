require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184735_term_abbrevs;
require open hol-light.thm3184697_spec;
opaque symbol lem3184735 [_83095] (p : El (fun _83095 bool)) : Prf (term0 _83095 p) ≔ λ x : El _83095, (@lem3184697 _83095 p x);
