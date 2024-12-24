require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7931456 [A] : Prf (∀ (λ a : El (finite_sum (finite_sum A A) 1), (∀ (λ a' : El (finite_sum (finite_sum A A) 1), (= (= ((@mktybit1 A) a) ((@mktybit1 A) a')) (= a a'))))));
