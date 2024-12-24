require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7931326 [A Z] : Prf (∀ (λ f : El (fun (finite_sum (finite_sum A A) 1) Z), (∃ (λ fn : El (fun (tybit1 A) Z), (∀ (λ a : El (finite_sum (finite_sum A A) 1), (= (fn ((@mktybit1 A) a)) (f a))))))));
