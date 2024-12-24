require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7925129 [A] (a : El (finite_sum A A)) : Prf ((λ a' : El (recspace (finite_sum A A)), (∀ (λ tybit0' : El (fun (recspace (finite_sum A A)) bool), (⇒ (∀ (λ a'' : El (recspace (finite_sum A A)), (⇒ (∃ (λ a''' : El (finite_sum A A), (= a'' ((λ a'''' : El (finite_sum A A), ((@CONSTR (finite_sum A A)) (NUMERAL _0) a'''' (λ n : El num, (@BOTTOM (finite_sum A A))))) a''')))) (tybit0' a'')))) (tybit0' a'))))) ((λ a' : El (finite_sum A A), ((@CONSTR (finite_sum A A)) (NUMERAL _0) a' (λ n : El num, (@BOTTOM (finite_sum A A))))) a));
