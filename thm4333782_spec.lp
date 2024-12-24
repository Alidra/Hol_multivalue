require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4333782 [A B] : Prf (= (= (∨ ((@INFINITE B) (@UNIV B)) ((@INFINITE A) (@UNIV A))) (∨ ((@INFINITE A) (@UNIV A)) ((@INFINITE B) (@UNIV B)))) (= ((@INFINITE (prod A B)) (@UNIV (prod A B))) (∨ ((@INFINITE A) (@UNIV A)) ((@INFINITE B) (@UNIV B)))));
