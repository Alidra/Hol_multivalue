require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.UNIONS_1_term_abbrevs;
require open hol-light.thm3322190_spec;
require open hol-light.thm3322871_spec;
opaque symbol lem3322872 [_86807] (s : El (fun _86807 bool)) : Prf (= (term0 _86807 s) s) ≔ EQ_MP (@lem3322190 _86807 s) (@lem3322871 _86807 s);
