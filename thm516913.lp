require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7_spec;
opaque symbol lem516913 (n : El num) : Prf (= (<= _0 n) (= (<= _0 n) T)) ≔ (@lem7 (<= _0 n));
