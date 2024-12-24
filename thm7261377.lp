require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7261377_term_abbrevs;
require open hol-light.thm7260968_spec;
require open hol-light.thm7261111_spec;
opaque symbol lem7261377 [_137613] (s : El (fun _137613 bool)) (f : El (fun _137613 real)) (g : El (fun _137613 real)) (h1 : Prf (term0 _137613 s f g)) : Prf (= (term1 _137613 s f) ((@sum _137613) s g)) ≔ (@lem7260968 _137613 f s g) (@lem7261111 _137613 s f g h1);
