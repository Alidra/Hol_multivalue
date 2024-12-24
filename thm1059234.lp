require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
opaque symbol lem1059234 [A] : Prf (= ((@_mk_rec A) (@ZBOT A)) ((@_mk_rec A) (@ZBOT A))) ≔ REFL ((@_mk_rec A) (@ZBOT A));
