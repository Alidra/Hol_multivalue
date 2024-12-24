require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184690_term_abbrevs;
require open hol-light.thm3183509_spec;
require open hol-light.thm3184137_spec;
opaque symbol lem3184690 [_83095] (p : El (fun _83095 bool)) (x : El _83095) : Prf (= (term0 _83095 x p) (p x)) ≔ EQ_MP (@lem3183509 _83095 p x) (@lem3184137 _83095 p x);
