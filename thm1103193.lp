require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1103191_spec;
require open hol-light.thm1103192_spec;
opaque symbol lem1103193 [_25376] (x : El _25376) : Prf (= ((@MEM _25376) x (@NIL _25376)) F) ≔ EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x);
