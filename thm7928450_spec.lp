require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7928450 [A] (r : El (recspace (finite_sum (finite_sum A A) 1))) : Prf (= ((λ a : El (recspace (finite_sum (finite_sum A A) 1)), (∀ (λ tybit1' : El (fun (recspace (finite_sum (finite_sum A A) 1)) bool), (⇒ (∀ (λ a' : El (recspace (finite_sum (finite_sum A A) 1)), (⇒ (∃ (λ a'' : El (finite_sum (finite_sum A A) 1), (= a' ((λ a''' : El (finite_sum (finite_sum A A) 1), ((@CONSTR (finite_sum (finite_sum A A) 1)) (NUMERAL _0) a''' (λ n : El num, (@BOTTOM (finite_sum (finite_sum A A) 1))))) a'')))) (tybit1' a')))) (tybit1' a))))) r) (= ((@_dest_tybit1 A) ((@_mk_tybit1 A) r)) r));
