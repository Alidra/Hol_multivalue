require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1052803 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∧ (= (NUMFST (NUMPAIR x y)) x) (= (NUMSND (NUMPAIR x y)) y))))));
