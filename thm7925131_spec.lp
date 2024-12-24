require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7925131 [A] (r : El (recspace (finite_sum A A))) : Prf (= ((λ a : El (recspace (finite_sum A A)), (∀ (λ tybit0' : El (fun (recspace (finite_sum A A)) bool), (⇒ (∀ (λ a' : El (recspace (finite_sum A A)), (⇒ (∃ (λ a'' : El (finite_sum A A), (= a' ((λ a''' : El (finite_sum A A), ((@CONSTR (finite_sum A A)) (NUMERAL _0) a''' (λ n : El num, (@BOTTOM (finite_sum A A))))) a'')))) (tybit0' a')))) (tybit0' a))))) r) (= ((@_dest_tybit0 A) ((@_mk_tybit0 A) r)) r));
