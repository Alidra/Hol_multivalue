require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7926442 [A] (a : El (finite_sum A A)) (_103783' : El (fun (finite_sum A A) (recspace (finite_sum A A)))) (h1 : Prf (= _103783' (λ a' : El (finite_sum A A), ((@CONSTR (finite_sum A A)) (NUMERAL _0) a' (λ n : El num, (@BOTTOM (finite_sum A A))))))) : Prf (= ((@_103783 A) a) ((@_mk_tybit0 A) (_103783' a)));
