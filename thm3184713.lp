require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184713_term_abbrevs;
require open hol-light.thm3184695_spec;
opaque symbol lem3184713 [_83152] (p : El (fun _83152 bool)) : Prf (term0 _83152 p) ≔ λ x : El _83152, (@lem3184695 _83152 p x);
