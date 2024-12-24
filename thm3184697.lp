require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184697_term_abbrevs;
require open hol-light.thm3183162_spec;
require open hol-light.thm3184690_spec;
opaque symbol lem3184697 [_83095] (p : El (fun _83095 bool)) (x : El _83095) : Prf (= (term0 _83095 x p) (p x)) ≔ EQ_MP (@lem3183162 _83095 p x) (@lem3184690 _83095 p x);
