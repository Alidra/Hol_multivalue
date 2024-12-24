require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7932353 [A] : Prf (∀ (λ x : El (tybit1 A), (∃ (λ a : El (finite_sum (finite_sum A A) 1), (= x ((@mktybit1 A) a))))));
