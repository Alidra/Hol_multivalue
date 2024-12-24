require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm515641_term_abbrevs;
opaque symbol lem515641 (n : El num) (m : El num) (p : El num) : Prf (= (term0 n m p) (= (term1 m n p) (term2 n m p))) ≔ REFL (term0 n m p);
