require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7598119 [A] (n : El num) : Prf (⇒ (¬ (⇒ ((@HAS_SIZE A) (@UNIV A) n) (= ((@dimindex A) (@UNIV A)) n))) F);
