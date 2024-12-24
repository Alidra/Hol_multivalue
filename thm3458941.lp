require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3458941_term_abbrevs;
require open hol-light.thm3454059_spec;
require open hol-light.thm3455583_spec;
opaque symbol lem3458941 [_89520 _89534] (P : El (fun _89534 bool)) (f : El (type1470 _89520 _89534)) : Prf (term0 _89520 _89534 P f) ≔ EQ_MP (@lem3454059 _89520 _89534 P f) (@lem3455583 _89520 _89534 P f);
