require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1246844_term_abbrevs;
require open hol-light.DIST_ELIM_THM_spec;
opaque symbol lem1246844 (_22840 : El num) (_22841 : El num) (_22842 : El (fun num bool)) : Prf (= (term0 _22842 _22841 _22840) (term1 _22840 _22841 _22842)) ≔ (@lem1246841 _22840 _22841 _22842);
