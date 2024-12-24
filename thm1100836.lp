require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1100834_spec;
require open hol-light.thm1100835_spec;
opaque symbol lem1100836 [_25307] (P : El (fun _25307 bool)) : Prf (= ((@ALL _25307) P (@NIL _25307)) T) ≔ EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P);
