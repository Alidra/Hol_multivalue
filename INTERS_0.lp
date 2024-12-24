require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3354637_spec;
require open hol-light.thm3354697_spec;
opaque symbol lem3354698 [A] : Prf (= ((@INTERS A) (@EMPTY (fun A bool))) (@UNIV A)) ≔ EQ_MP (@lem3354637 A) (@lem3354697 A);
