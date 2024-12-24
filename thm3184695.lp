require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184695_term_abbrevs;
require open hol-light.thm3183232_spec;
require open hol-light.thm3184689_spec;
opaque symbol lem3184695 [_83152] (p : El (fun _83152 bool)) (x : El _83152) : Prf (= (term0 _83152 p x) (p x)) ≔ EQ_MP (@lem3183232 _83152 p x) (@lem3184689 _83152 p x);
