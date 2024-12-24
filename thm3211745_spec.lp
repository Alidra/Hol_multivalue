require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211745 [A] (s : El (fun A bool)) (t : El (fun A bool)) : Prf (= ((λ t' : El (fun A bool), (= ((@PSUBSET A) s t') (∧ ((@SUBSET A) s t') (¬ (= s t'))))) t) (= ((@PSUBSET A) s t) (∧ ((@SUBSET A) s t) (¬ (= s t)))));
