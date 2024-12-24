require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7928467 [A] (_103802' : El (fun (finite_sum (finite_sum A A) 1) (recspace (finite_sum (finite_sum A A) 1)))) (h1 : Prf (= _103802' (λ a : El (finite_sum (finite_sum A A) 1), ((@CONSTR (finite_sum (finite_sum A A) 1)) (NUMERAL _0) a (λ n : El num, (@BOTTOM (finite_sum (finite_sum A A) 1))))))) : Prf (= (λ a : El (finite_sum (finite_sum A A) 1), ((@_mk_tybit1 A) (_103802' a))) (λ a : El (finite_sum (finite_sum A A) 1), ((@_mk_tybit1 A) ((λ a' : El (finite_sum (finite_sum A A) 1), ((@CONSTR (finite_sum (finite_sum A A) 1)) (NUMERAL _0) a' (λ n : El num, (@BOTTOM (finite_sum (finite_sum A A) 1))))) a))));
