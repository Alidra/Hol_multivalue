require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4380552_term_abbrevs;
require open hol-light.thm4380526_spec;
opaque symbol lem4380552 [_104907 _104908] (f : El (type686 _104907)) : Prf (term0 _104907 _104908 f) ≔ λ g : El (type686 _104908), (@lem4380526 _104907 _104908 f g);
