require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3458943_term_abbrevs;
require open hol-light.thm3453917_spec;
require open hol-light.thm3458940_spec;
opaque symbol lem3458943 [_89578 _89597 _89598] (P : El (type1470 _89597 _89598)) (f : El (type1517 _89578 _89597 _89598)) : Prf (= (term0 _89578 _89597 _89598 P f) (term1 _89578 _89597 _89598 P f)) ≔ EQ_MP (@lem3453917 _89578 _89597 _89598 P f) (@lem3458940 _89578 _89597 _89598 P f);
