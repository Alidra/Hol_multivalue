require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184703_term_abbrevs;
require open hol-light.thm3183254_spec;
opaque symbol lem3184703 [_83169] (p : El (fun _83169 bool)) : Prf (term0 _83169 p) ≔ λ x : El _83169, (@lem3183254 _83169 p x);
