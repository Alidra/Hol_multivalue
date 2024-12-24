require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm302578_term_abbrevs;
opaque symbol lem302578 (p : El num) (m : El num) (n : El num) : Prf (= (term0 m n p) (= (= (+ m p) (+ n p)) (= m n))) ≔ REFL (term0 m n p);
