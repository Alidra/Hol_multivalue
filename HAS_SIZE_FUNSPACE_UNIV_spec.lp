require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4582295 [A B] : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE A) (@UNIV A) m) ((@HAS_SIZE B) (@UNIV B) n)) ((@HAS_SIZE (fun A B)) (@UNIV (fun A B)) (EXP n m)))))));
