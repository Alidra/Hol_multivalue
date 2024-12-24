require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm7936917_spec;
opaque symbol lem7948705 [A] (s : El (fun A bool)) (n : El num) : Prf (= (= ((@dimindex A) (@UNIV A)) n) (= ((@dimindex A) s) (NUMERAL n))) ≔ EQ_MP (@lem7936917 A s n) (@lem0);
