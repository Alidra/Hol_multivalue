require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.UNIONS_INSERT_term_abbrevs;
require open hol-light.thm3324017_spec;
require open hol-light.thm3325374_spec;
opaque symbol lem3325375 [_86841] (s : El (fun _86841 bool)) (u : El (type686 _86841)) : Prf (= (term0 _86841 s u) (term1 _86841 s u)) ≔ EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u);
