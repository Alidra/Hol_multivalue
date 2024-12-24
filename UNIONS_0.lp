require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3322101_spec;
require open hol-light.thm3322164_spec;
opaque symbol lem3322165 [_86801] : Prf (= ((@UNIONS _86801) (@EMPTY (fun _86801 bool))) (@EMPTY _86801)) ≔ EQ_MP (@lem3322101 _86801) (@lem3322164 _86801);
