require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7927999 [A Z] : Prf (∀ (λ f : El (fun (finite_sum A A) Z), (∃ (λ fn : El (fun (tybit0 A) Z), (∀ (λ a : El (finite_sum A A), (= (fn ((@mktybit0 A) a)) (f a))))))));
