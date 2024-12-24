require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3458970_term_abbrevs;
require open hol-light.thm3458944_spec;
opaque symbol lem3458970 [_89520 _89534] (P : El (fun _89534 bool)) : Prf (term0 _89520 _89534 P) ≔ λ f : El (type1470 _89520 _89534), (@lem3458944 _89520 _89534 P f);
