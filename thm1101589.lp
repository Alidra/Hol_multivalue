require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1101587_spec;
require open hol-light.thm1101588_spec;
opaque symbol lem1101589 [_25328] (P : El (fun _25328 bool)) : Prf (= ((@EX _25328) P (@NIL _25328)) F) ≔ EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P);
