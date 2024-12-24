require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1106562_spec;
require open hol-light.thm1106563_spec;
opaque symbol lem1106564 [_25594] (P : El (fun _25594 bool)) : Prf (= ((@FILTER _25594) P (@NIL _25594)) (@NIL _25594)) ≔ EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P);
