require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7990967 [A N] : Prf (∀ (λ m : El num, (⇒ ((@HAS_SIZE A) (@UNIV A) m) ((@HAS_SIZE (cart A N)) (@UNIV (cart A N)) (EXP m ((@dimindex N) (@UNIV N)))))));
